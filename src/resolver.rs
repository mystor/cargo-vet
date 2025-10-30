//! The Resolver is the heart of cargo-vet, and does all the work to validate the audits
//! for your current packages and to suggest fixes. This is done in 3 phases:
//!
//! 1. Resolving required criteria based on your policies
//! 2. Searching for audits which satisfy the required criteria
//! 3. Suggesting audits that would make your project pass validation
//!
//! # High-level Usage
//!
//! * [`resolve`] is the main entry point, Validating and Searching and producing a [`ResolveReport`]
//! * [`ResolveReport::compute_suggest`] does Suggesting and produces a [`Suggest`]
//! * various methods on [`ResolveReport`] and [`Suggest`] handle printing
//! * [`update_store`] handles automatically minimizing and generating exemptions and imports
//!
//! # Low-level Design
//!
//!
//! ## Resolve
//!
//! * construct the [`CriteriaMapper`] which maps criteria and their
//!   dependencies to bitsets for faster operation during the rest of resolve.
//!
//! * resolve_requirements_for_build: simulate a cargo build config, applying required
//!   audit criteria to each package
//!     * simulate cargo's feature resolution with [`guppy::graph::cargo::CargoSet`]
//!     * propagate audit requirements over enabled dependency edges based on
//!       the computed feature resolution
//!     * policies can override requirements on each crate and its dependencies
//!     * results for target and host builds are merged into the overall
//!       requirements table, which may be shared between multiple calls to
//!       `resolve_requirements_for_build`
//!
//! * resolve_requirements: simulates multiple builds, merging them all together
//!   to determine overall criteria requirements
//!     * builds are simulated with `resolve_requirements_for_build` (see above)
//!     * the full workspace is first "built" once with dev-dependencies
//!       enabled, propagating dev-only criteria, then
//!     * each root package is "built" without dev-dependencies,
//!       propagating normal audit criteria.
//!
//! * resolve_audits: for each package, resolve what criteria it's audited for
//!     * compute the [`AuditGraph`] and check for violations
//!     * for each criteria, search the for a connected path in the audit graph
//!     * check if the criteria are satisfied
//!         * if they are, record caveats which were required for the criteria
//!         * if they aren't record the criteria which failed, and how to fix them
//!
//!
//! ## Suggest
//!
//! * enumerate the failures and perform a number of diffstats based on the
//!   existing set of criteria, to suggest the best audit and criteria which could
//!   be used to allow the crate to vet successfully.

use futures_util::future::join_all;
use guppy::graph::cargo::{BuildPlatform, CargoOptions, CargoResolverVersion};
use guppy::graph::feature::{FeatureLabel, FeatureSet, StandardFeatures};
use guppy::graph::{DependencyDirection, PackageGraph, PackageLink, PackageMetadata};
use guppy::platform::{EnabledTernary, PlatformSpec};
use guppy::{DependencyKind, PackageId};
use miette::IntoDiagnostic;
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{hash_map, BinaryHeap};
use std::sync::Arc;
use tracing::{debug, debug_span, trace, trace_span, warn};

use crate::cli::OutputFormat;
use crate::criteria::{CriteriaMapper, CriteriaSet};
use crate::errors::SuggestError;
use crate::format::{
    self, AuditEntry, AuditKind, AuditsFile, CratesPublisher, CratesPublisherSource,
    CratesSourceId, CriteriaName, Delta, DiffStat, ExemptedDependency, FastMap, FastSet,
    ImportName, ImportsFile, JsonPackage, JsonReport, JsonReportConclusion, JsonReportFailForVet,
    JsonReportFailForViolationConflict, JsonReportSuccess, JsonSuggest, JsonSuggestItem,
    JsonVetFailure, PackageName, PackageStr, Policy, UnpublishedEntry, VetVersion, WildcardEntry,
};
use crate::format::{SortedMap, SortedSet};
use crate::network::Network;
use crate::out::{progress_bar, IncProgressOnDrop, Out};
use crate::storage::Cache;
use crate::string_format::FormatShortList;
use crate::{Config, PackageExt, Store};

pub struct ResolveReport<'g> {
    /// Mappings between criteria names and CriteriaSets/Indices.
    pub criteria_mapper: CriteriaMapper,

    /// Low-level results for each package's individual criteria resolving
    /// analysis, indexed by [`PackageIdx`][]. Will be absent for first-party
    /// crates or crates with violation conflicts.
    pub results: FastMap<&'g PackageId, ResolveResult>,

    /// The final conclusion of our analysis.
    pub conclusion: Conclusion<'g>,
}

#[derive(Debug)]
pub enum Conclusion<'g> {
    Success(Success<'g>),
    FailForViolationConflict(FailForViolationConflict<'g>),
    FailForVet(FailForVet<'g>),
}

#[derive(Debug, Clone)]
pub struct Success<'g> {
    /// Third-party packages that were successfully vetted using only 'exemptions'
    pub vetted_with_exemptions: Vec<PackageMetadata<'g>>,
    /// Third-party packages that were successfully vetted using both 'audits' and 'exemptions'
    pub vetted_partially: Vec<PackageMetadata<'g>>,
    /// Third-party packages that were successfully vetted using only 'audits'
    pub vetted_fully: Vec<PackageMetadata<'g>>,
}

#[derive(Debug, Clone)]
pub struct FailForViolationConflict<'g> {
    pub violations: Vec<(PackageMetadata<'g>, Vec<ViolationConflict>)>,
}

#[derive(Debug)]
pub struct FailForVet<'g> {
    /// These packages are to blame and need to be fixed
    pub failures: Vec<(PackageMetadata<'g>, AuditFailure)>,
    pub suggest: Option<Suggest<'g>>,
}

// FIXME: This format is pretty janky and unstable, so we probably should come
// up with an actually-useful format for this.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViolationConflict {
    UnauditedConflict {
        violation_source: Option<ImportName>,
        violation: AuditEntry,
        exemptions: ExemptedDependency,
    },
    AuditConflict {
        violation_source: Option<ImportName>,
        violation: AuditEntry,
        audit_source: Option<ImportName>,
        audit: AuditEntry,
    },
}

#[derive(Debug, Default)]
pub struct Suggest<'g> {
    pub suggestions: Vec<SuggestItem<'g>>,
    pub suggestions_by_criteria: SortedMap<CriteriaName, Vec<SuggestItem<'g>>>,
    pub total_lines: u64,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct TrustHint {
    trusted_by: Vec<String>,
    publisher: CratesPublisherSource,
    exact_version: bool,
}

#[derive(Debug, Clone)]
pub struct SuggestItem<'g> {
    pub package: PackageMetadata<'g>,
    pub suggested_criteria: CriteriaSet,
    pub suggested_diff: DiffRecommendation,
    pub notable_parents: Vec<String>,
    pub publisher_login: Option<String>,
    pub trust_hint: Option<TrustHint>,
    pub is_sole_publisher: bool,
    pub registry_suggestion: Vec<RegistrySuggestion>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq)]
pub struct DiffRecommendation {
    pub from: Option<VetVersion>,
    pub to: VetVersion,
    pub diffstat: DiffStat,
}

#[derive(Debug, Clone)]
pub struct RegistrySuggestion {
    pub name: ImportName,
    pub url: Vec<String>,
    pub diff: DiffRecommendation,
}

/// Results and notes from running vet on a particular package.
#[derive(Debug, Clone)]
pub struct ResolveResult {
    /// Cache of search results for each criteria.
    pub search_results: Vec<Result<Vec<DeltaEdgeOrigin>, SearchFailure>>,
}

#[derive(Debug, Clone)]
pub struct AuditFailure {
    pub criteria_failures: CriteriaSet,
}

/// Value indicating a failure to find a path in the audit graph between two nodes.
#[derive(Debug, Clone)]
pub struct SearchFailure {
    /// Nodes we could reach from "root"
    pub reachable_from_root: SortedSet<Option<VetVersion>>,
    /// Nodes we could reach from the "target"
    pub reachable_from_target: SortedSet<Option<VetVersion>>,
}

type DirectedAuditGraph<'a> = SortedMap<Option<&'a VetVersion>, Vec<DeltaEdge<'a>>>;

/// A graph of the audits for a package.
///
/// The nodes of the graph are Versions and the edges are audits.
/// An AuditGraph is directed, potentially cyclic, and potentially disconnected.
///
/// There are two important versions in each AuditGraph:
///
/// * The "root" version (None) which exists as a dummy node for full-audits
/// * The "target" version which is the current version of the package
///
/// The edges are constructed as follows:
///
/// * Delta Audits desugar directly to edges
/// * Full Audits and Unaudited desugar to None -> Some(Version)
///
/// If there are multiple versions of a package in-tree, we analyze each individually
/// so there is always one root and one target. All we want to know is if there exists
/// a path between the two where every edge on that path has a given criteria. We do this
/// check for every possible criteria in a loop to keep the analysis simple and composable.
///
/// When resolving the audits for a package, we create a "forward" graph and a "backward" graph.
/// These are the same graphs but with the edges reversed. The backward graph is only used if
/// we can't find the desired path in the forward graph, and is used to compute the
/// reachability set of the target version for that criteria. That reachability is
/// used for `suggest`.
#[derive(Debug, Clone)]
pub struct AuditGraph<'a> {
    forward_audits: DirectedAuditGraph<'a>,
    backward_audits: DirectedAuditGraph<'a>,
}

/// The precise origin of an edge in the audit graph.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum DeltaEdgeOrigin {
    /// This edge represents an audit from the local audits.toml.
    StoredLocalAudit {
        audit_index: usize,
        importable: bool,
    },
    /// This edge represents an audit imported from a peer, potentially stored
    /// in the local imports.lock.
    ImportedAudit {
        import_index: usize,
        audit_index: usize,
    },
    /// This edge represents a reified wildcard audit.
    WildcardAudit {
        import_index: Option<usize>,
        audit_index: usize,
        publisher_index: usize,
    },
    /// This edge represents a trusted publisher.
    Trusted { publisher_index: usize },
    /// This edge represents an exemption from the local config.toml.
    Exemption { exemption_index: usize },
    /// This edge represents an unpublished entry in imports.lock.
    Unpublished { unpublished_index: usize },
    /// This edge represents brand new exemption which didn't previously exist
    /// in the audit graph. Will only ever be produced from
    /// SearchMode::RegenerateExemptions.
    FreshExemption { version: VetVersion },
}

/// An indication of a required local audit, imported entry, or exemption. Used to compute the
/// minimal set of possible imports for imports.lock and for pruning unused audits and exemptions.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum RequiredEntry {
    LocalAudit {
        audit_index: usize,
    },
    Audit {
        import_index: usize,
        audit_index: usize,
    },
    WildcardAudit {
        import_index: usize,
        audit_index: usize,
    },
    Publisher {
        publisher_index: usize,
    },
    Exemption {
        exemption_index: usize,
    },
    Unpublished {
        unpublished_index: usize,
    },
    // NOTE: This variant must come last, as code in `update_store` depends on
    // `FreshExemption` entries sorting after all other entries.
    FreshExemption {
        version: VetVersion,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum DeltaEdgeFreshness {
    // All information requried for this delta edge is already stored within the store's
    // supply-chain. Using this edge will require no changes to imports.lock.
    Stale,
    // This edge originates from an already-imported or local wildcard audit, however will require
    // importing fresh publisher information into imports.lock.
    FreshPublisher,
    // This edge is fully fresh, and will require adding the audit entry to imports.lock to use.
    Fresh,
}

impl DeltaEdgeFreshness {
    fn new(is_fresh_audit: bool, is_fresh_publisher: bool) -> Self {
        if is_fresh_audit {
            DeltaEdgeFreshness::Fresh
        } else if is_fresh_publisher {
            DeltaEdgeFreshness::FreshPublisher
        } else {
            DeltaEdgeFreshness::Stale
        }
    }

    fn is_fresh(&self) -> bool {
        self != &DeltaEdgeFreshness::Stale
    }
}

/// A directed edge in the graph of audits. This may be forward or backwards,
/// depending on if we're searching from "roots" (forward) or the target (backward).
/// The source isn't included because that's implicit in the Node.
#[derive(Debug, Clone)]
struct DeltaEdge<'a> {
    /// The version this edge goes to.
    version: Option<&'a VetVersion>,
    /// The criteria that this edge is valid for.
    criteria: CriteriaSet,
    /// The origin of this edge. See `DeltaEdgeOrigin`'s documentation for more
    /// details.
    origin: DeltaEdgeOrigin,
    /// Whether or not the edge is a "fresh import", and should be
    /// de-prioritized to avoid unnecessary imports.lock updates.
    freshness: DeltaEdgeFreshness,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum SearchMode {
    /// Prefer exemptions over fresh imports when searching.
    PreferExemptions,
    /// Prefer fresh imports over exemptions when searching for paths.
    PreferFreshImports,
    /// Prefer fresh imports over exemptions, and allow introducing new
    /// exemptions or expanding their criteria beyond the written criteria
    /// (unless they are suggest=false).
    RegenerateExemptions,
}

pub fn resolve<'a>(
    package_graph: &'a PackageGraph,
    resolver_version: CargoResolverVersion,
    store: &Store,
) -> ResolveReport<'a> {
    // A large part of our algorithm is unioning and intersecting criteria, so we map all
    // the criteria into indexed boolean sets (*whispers* an integer with lots of bits).
    let criteria_mapper = CriteriaMapper::new(&store.audits.criteria);
    trace!("built CriteriaMapper!");

    // FIXME: The CargoResolverVersion should be based on the edition & version
    // in Cargo.toml!
    let requirements = resolve_requirements(
        package_graph,
        &store.config,
        &criteria_mapper,
        resolver_version,
    );

    let (results, conclusion) =
        resolve_audits(package_graph, store, &criteria_mapper, &requirements);

    ResolveReport {
        criteria_mapper,
        results,
        conclusion,
    }
}

/// Check if a given PackageLink is enabled for a given build & dependency kind.
fn is_link_enabled(
    feature_set: &FeatureSet<'_>,
    link: &PackageLink<'_>,
    kind: DependencyKind,
    platform_spec: &PlatformSpec,
) -> bool {
    let req_status = link.req_for_kind(kind).status();

    // Check if we have a feature for this dependency enabled. If we do, we'll
    // also include optional dependencies.
    let enabled = if feature_set
        .contains((
            link.from().id(),
            FeatureLabel::OptionalDependency(link.dep_name()),
        ))
        .unwrap_or(false)
    {
        req_status.enabled_on(platform_spec)
    } else {
        req_status.required_on(platform_spec)
    };

    // NOTE: We bias towards assuming an edge is enabled if we don't have
    // information about the target features for a platform.
    enabled != EnabledTernary::Disabled
}

fn resolve_requirements_for_build<'g>(
    config_file: &ConfigFile,
    criteria_mapper: &CriteriaMapper,
    initials: FeatureSet<'g>,
    platform: &PlatformSpec,
    resolver_version: CargoResolverVersion,
    dev_pass: bool,
    out_requirements: &mut FastMap<&'g PackageId, CriteriaSet>,
) {
    let _resolve_requirements_for_build = debug_span!(
        "resolve_requirements_for_build",
        initials = ?initials,
        platform = ?platform,
        dev_pass
    )
    .entered();

    // Use guppy's "cargo set" algorithm to resolve the final feature sets for
    // the target & host platforms for this build. This will be used when
    // evaluating edges.
    let cargo_set = initials
        .into_cargo_set(
            CargoOptions::new()
                .set_platform(platform.clone())
                .set_include_dev(dev_pass)
                .set_resolver(resolver_version),
        )
        .expect("FeatureSet::into_cargo_set cannot fail unless an invalid PackageId is excluded");

    let initial_criteria = if dev_pass {
        match &config_file.root_policy.dev_criteria {
            Some(dev_criteria) => criteria_mapper.criteria_from_list(dev_criteria),
            None => criteria_mapper.criteria_from_list([format::DEFAULT_POLICY_DEV_CRITERIA]),
        }
    } else {
        match &config_file.root_policy.criteria {
            Some(criteria) => criteria_mapper.criteria_from_list(criteria),
            None => criteria_mapper.criteria_from_list([format::DEFAULT_POLICY_CRITERIA]),
        }
    };

    // Use our initials set to populate the first set of todo items.
    struct Todo<'g> {
        build_platform: BuildPlatform,
        package: PackageMetadata<'g>,
        criteria: CriteriaSet,
    }

    // Pending TODO item stack. This approach means we effectively do a DFS.
    // Order of evaluating todos should not matter.
    let mut todos: Vec<_> = cargo_set
        .initials()
        .to_package_set()
        .packages(DependencyDirection::Forward)
        .map(|package| Todo {
            build_platform: BuildPlatform::Target,
            package,
            criteria: initial_criteria.clone(),
        })
        .collect();

    let mut target_seen = FastMap::<&PackageId, CriteriaSet>::new();
    let mut host_seen = FastMap::<&PackageId, CriteriaSet>::new();

    while let Some(todo) = todos.pop() {
        let _resolve_requirements_todo = trace_span!(
            "resolve_requirements_todo",
            platform = ?todo.build_platform,
            package = %todo.package.id(),
            criteria = ?todo.criteria
        );

        let self_policy = todo.package.policy_entry(&config_file.policy);

        let build_platform = if todo.package.is_proc_macro() {
            BuildPlatform::Host
        } else {
            todo.build_platform
        };

        let explicit_criteria = self_policy
            .and_then(|p| p.criteria.as_ref())
            .map(|c| criteria_mapper.criteria_from_list(c))
            .unwrap_or_else(|| todo.criteria.clone());
        let explicit_dev_criteria = self_policy
            .and_then(|p| p.dev_criteria.as_ref())
            .map(|c| criteria_mapper.criteria_from_list(c))
            .unwrap_or_else(|| {
                // If `policy.criteria` was specified, but `policy.dev-criteria`
                // was not, cap the required criteria during the dev pass to at
                // most `policy.criteria` (as the dev pass must not expand
                // required criteria beyond `policy.criteria`).
                let mut criteria = todo.criteria.clone();
                criteria.intersected_with(&explicit_criteria);
                criteria
            });

        let self_criteria = if dev_pass {
            explicit_dev_criteria
        } else {
            explicit_criteria
        };

        // If we've already seen this package, on this platform, and there are
        // no new criteria, we've entered a loop. Break it.
        let seen = match build_platform {
            BuildPlatform::Target => &mut target_seen,
            BuildPlatform::Host => &mut host_seen,
        };
        match seen.entry(todo.package.id()) {
            hash_map::Entry::Occupied(occupied_entry)
                if occupied_entry.get().contains(&self_criteria) =>
            {
                continue;
            }
            entry => entry
                .or_insert_with(|| criteria_mapper.no_criteria())
                .unioned_with(&self_criteria),
        }

        trace!(
            "applying criteria {:?} for {} ({build_platform:?})",
            criteria_mapper
                .criteria_names(&self_criteria)
                .collect::<Vec<_>>()
                .join(", "),
            todo.package.id()
        );

        // We're making progress, record the new required criteria for the
        // package in `out_requirements` if the crate is third-party.
        // First party crates do not contribute to audit requirements.
        if todo.package.is_third_party(&config_file.policy) {
            out_requirements
                .entry(todo.package.id())
                .or_insert_with(|| criteria_mapper.no_criteria())
                .unioned_with(&self_criteria);
        }

        let feature_set = cargo_set.platform_features(build_platform);

        // Check direct dependencies declared by this node, and add todo items
        // to process them with.
        for link in todo.package.direct_links() {
            let package = link.to();
            let criteria = self_policy
                .and_then(|policy| policy.dependency_criteria.get(package.name()))
                .map(|criteria| criteria_mapper.criteria_from_list(criteria))
                .unwrap_or_else(|| self_criteria.clone());

            // We may need to add multiple todos for this dependency edge, if
            // it's both a normal and build dependency of the crate (as each may
            // unify features differently).
            let has_normal = is_link_enabled(feature_set, &link, DependencyKind::Normal, platform);
            // Dev edges are only checked in the dev pass.
            let has_dev = dev_pass
                && is_link_enabled(feature_set, &link, DependencyKind::Development, platform);
            // Cargo only follows build dependencies if a build script is
            // present, mimic that behaviour here.
            let has_build = todo.package.has_build_script()
                && is_link_enabled(feature_set, &link, DependencyKind::Build, platform);

            trace!(
                "link to {} (criteria={criteria:?}) normal={has_normal} dev={has_dev} build={has_build}",
                package.id()
            );

            if has_normal || has_dev {
                todos.push(Todo {
                    build_platform,
                    package,
                    criteria: criteria.clone(),
                })
            }
            if has_build {
                todos.push(Todo {
                    build_platform: BuildPlatform::Host,
                    package,
                    criteria,
                })
            }
        }
    }
}

fn resolve_requirements<'g>(
    package_graph: &'g PackageGraph,
    config_file: &ConfigFile,
    criteria_mapper: &CriteriaMapper,
    resolver_version: CargoResolverVersion,
) -> FastMap<&'g PackageId, CriteriaSet> {
    let _resolve_requirements = trace_span!("resolve_requirements").entered();

    // FIXME: Allow the user to customize a subset of platforms to be interested
    // in, and check each independently.
    let platform_spec = PlatformSpec::Any;

    let mut requirements = FastMap::<&'g PackageId, CriteriaSet>::new();

    let workspace_set = package_graph.resolve_workspace();

    // First-pass: Simulate a build for the entire workspace at once, with
    // dev-dependencies enabled. Dependencies built this way will use dev
    // criteria, respecting config options.
    debug!("simulating --workspace dev build (dev_pass)");
    resolve_requirements_for_build(
            config_file,
        criteria_mapper,
        workspace_set.to_feature_set(StandardFeatures::All),
        &platform_spec,
        resolver_version,
        /* dev_pass */ true,
        &mut requirements,
    );

    // Second-pass: Simulate a build of each root package independently, with
    // dev-dependencies disabled. Dependencies built this way will use standard
    // criteria, respecting config options.
    for root in workspace_set.root_packages(DependencyDirection::Forward) {
        debug!("simulating target build of root package: {}", root.id());
        resolve_requirements_for_build(
                config_file,
            criteria_mapper,
            root.to_feature_set(StandardFeatures::All),
            &platform_spec,
            resolver_version,
            /* dev_pass */ false,
            &mut requirements,
        );
    }

    requirements
}

fn resolve_audits<'g>(
    package_graph: &'g PackageGraph,
    store: &Store,
    criteria_mapper: &CriteriaMapper,
    requirements: &FastMap<&'g PackageId, CriteriaSet>,
) -> (FastMap<&'g PackageId, ResolveResult>, Conclusion<'g>) {
    let _resolve_audits = trace_span!("resolve_audits").entered();
    let mut violations = Vec::new();
    let mut failures = Vec::new();
    let mut vetted_with_exemptions = Vec::new();
    let mut vetted_partially = Vec::new();
    let mut vetted_fully = Vec::new();

    let mut results = FastMap::<&'g PackageId, ResolveResult>::new();
    for package in package_graph.packages() {
        // First-party crates don't need audits.
        if !package.is_third_party(&store.config.policy) {
            continue;
        }

        let audit_graph = match AuditGraph::build(store, criteria_mapper, package.name(), None) {
            Ok(audit_graph) => audit_graph,
            Err(violation) => {
                violations.push((package, violation));
                continue;
            }
        };

        let no_criteria = criteria_mapper.no_criteria();
        let required_criteria = requirements.get(package.id()).unwrap_or(&no_criteria);

        // NOTE: We currently always compute all search results even if we
        // only need those in `req_criteria` because some later passes using
        // the resolver results might need that information. We might want
        // to look into simplifying this in the future.
        let search_results: Vec<_> = (0..criteria_mapper.len())
            .map(|criteria_idx| {
                audit_graph.search(
                    criteria_idx,
                    &package.vet_version(),
                    SearchMode::PreferExemptions,
                )
            })
            .collect();

        let mut needed_exemptions = false;
        let mut directly_exempted = false;
        let mut criteria_failures = criteria_mapper.no_criteria();
        for criteria_idx in required_criteria.indices() {
            match &search_results[criteria_idx] {
                Ok(path) => {
                    needed_exemptions |= path
                        .iter()
                        .any(|o| matches!(o, DeltaEdgeOrigin::Exemption { .. }));
                    // Ignore `Unpublished` entries when deciding if a crate
                    // is directly exempted.
                    directly_exempted |= path.iter().all(|o| {
                        matches!(
                            o,
                            DeltaEdgeOrigin::Exemption { .. } | DeltaEdgeOrigin::Unpublished { .. }
                        )
                    });
                }
                Err(_) => criteria_failures.set_criteria(criteria_idx),
            }
        }

        if !criteria_failures.is_empty() {
            failures.push((package, AuditFailure { criteria_failures }));
        }

        // XXX: Callers using these fields in success should perhaps be
        // changed to instead walk the results?
        if !needed_exemptions {
            vetted_fully.push(package);
        } else if directly_exempted {
            vetted_with_exemptions.push(package);
        } else {
            vetted_partially.push(package);
        }

        results.insert(package.id(), ResolveResult { search_results });
    }

    fn package_sort_key<'g>(package: &PackageMetadata<'g>) -> (&'g str, VetVersion, &'g PackageId) {
        (package.name(), package.vet_version(), package.id())
    }
    vetted_fully.sort_by_key(package_sort_key);
    vetted_with_exemptions.sort_by_key(package_sort_key);
    vetted_partially.sort_by_key(package_sort_key);
    failures.sort_by_key(|(package, _)| package_sort_key(package));

    let conclusion = if !violations.is_empty() {
        Conclusion::FailForViolationConflict(FailForViolationConflict { violations })
    } else if !failures.is_empty() {
        Conclusion::FailForVet(FailForVet {
            failures,
            suggest: None,
        })
    } else {
        Conclusion::Success(Success {
            vetted_with_exemptions,
            vetted_partially,
            vetted_fully,
        })
    };

    (results, conclusion)
}

impl<'a> AuditGraph<'a> {
    /// Given the store, and a package name, builds up an audit graph. This can
    /// then be searched in order to find a specific path which satisfies a
    /// given criteria.
    pub fn build(
        store: &'a Store,
        criteria_mapper: &CriteriaMapper,
        package: PackageStr<'_>,
        extra_audits_file: Option<&'a AuditsFile>,
    ) -> Result<Self, Vec<ViolationConflict>> {
        // Pre-build the namespaces for each audit so that we can take a reference
        // to each one as-needed rather than cloning the name each time.
        let foreign_namespaces: Vec<Option<ImportName>> = store
            .imported_audits()
            .keys()
            .map(|import_name| Some(import_name.clone()))
            .collect();

        // Iterator over every audits file, including imported audits.
        let all_audits_files = store
            .imported_audits()
            .values()
            .enumerate()
            .map(|(import_index, audits_file)| {
                (
                    Some(import_index),
                    &foreign_namespaces[import_index],
                    audits_file,
                )
            })
            .chain([(None, &None, &store.audits)])
            .chain(
                // Consider extra audits as local for now - we don't care about
                // how the audits from it are prioritized.
                extra_audits_file
                    .iter()
                    .map(|&audits_file| (None, &None, audits_file)),
            );

        // Iterator over every normal audit.
        let all_audits =
            all_audits_files
                .clone()
                .flat_map(|(import_index, namespace, audits_file)| {
                    audits_file
                        .audits
                        .get(package)
                        .map(|v| &v[..])
                        .unwrap_or(&[])
                        .iter()
                        .enumerate()
                        .map(move |(audit_index, audit)| {
                            (
                                namespace,
                                match import_index {
                                    Some(import_index) => DeltaEdgeOrigin::ImportedAudit {
                                        import_index,
                                        audit_index,
                                    },
                                    None => DeltaEdgeOrigin::StoredLocalAudit {
                                        audit_index,
                                        importable: audit.importable,
                                    },
                                },
                                audit,
                            )
                        })
                });

        // Iterator over every wildcard audit.
        let all_wildcard_audits =
            all_audits_files
                .clone()
                .flat_map(|(import_index, namespace, audits_file)| {
                    audits_file
                        .wildcard_audits
                        .get(package)
                        .map(|v| &v[..])
                        .unwrap_or(&[])
                        .iter()
                        .enumerate()
                        .map(move |(audit_index, audit)| {
                            (namespace, import_index, audit_index, audit)
                        })
                });

        // Iterator over every trusted entry.
        let trusteds = store
            .audits
            .trusted
            .get(package)
            .map(|v| &v[..])
            .unwrap_or(&[]);

        let publishers = store
            .publishers()
            .get(package)
            .map(|v| &v[..])
            .unwrap_or(&[]);

        let unpublished = store
            .unpublished()
            .get(package)
            .map(|v| &v[..])
            .unwrap_or(&[]);

        let exemptions = store.config.exemptions.get(package);

        let mut forward_audits = DirectedAuditGraph::new();
        let mut backward_audits = DirectedAuditGraph::new();
        let mut violation_nodes = Vec::new();

        // Collect up all the deltas, and their criteria
        for (namespace, origin, entry) in all_audits.clone() {
            // For uniformity, model a Full Audit as `None -> x.y.z`
            let (from_ver, to_ver) = match &entry.kind {
                AuditKind::Full { version } => (None, version),
                AuditKind::Delta { from, to } => (Some(from), to),
                AuditKind::Violation { .. } => {
                    violation_nodes.push((namespace.clone(), entry));
                    continue;
                }
            };

            let criteria = criteria_mapper.criteria_from_list(&entry.criteria);
            let freshness = DeltaEdgeFreshness::new(entry.is_fresh_import, false);

            forward_audits.entry(from_ver).or_default().push(DeltaEdge {
                version: Some(to_ver),
                criteria: criteria.clone(),
                origin: origin.clone(),
                freshness,
            });
            backward_audits
                .entry(Some(to_ver))
                .or_default()
                .push(DeltaEdge {
                    version: from_ver,
                    criteria,
                    origin,
                    freshness,
                });
        }

        // For each published version of the crate we're aware of, check if any
        // wildcard audits apply and add full-audits to those versions if they
        // do.
        for (publisher_index, publisher) in publishers.iter().enumerate() {
            for (_, import_index, audit_index, entry) in all_wildcard_audits.clone() {
                if entry.source == publisher.source
                    && *entry.start <= publisher.when
                    && publisher.when < *entry.end
                {
                    let from_ver = None;
                    let to_ver = Some(&publisher.version);
                    let criteria = criteria_mapper.criteria_from_list(&entry.criteria);
                    let origin = DeltaEdgeOrigin::WildcardAudit {
                        import_index,
                        audit_index,
                        publisher_index,
                    };
                    let freshness =
                        DeltaEdgeFreshness::new(entry.is_fresh_import, publisher.is_fresh_import);

                    forward_audits.entry(from_ver).or_default().push(DeltaEdge {
                        version: to_ver,
                        criteria: criteria.clone(),
                        origin: origin.clone(),
                        freshness,
                    });
                    backward_audits.entry(to_ver).or_default().push(DeltaEdge {
                        version: from_ver,
                        criteria,
                        origin,
                        freshness,
                    });
                }
            }

            for entry in trusteds {
                if entry.source == publisher.source
                    && *entry.start <= publisher.when
                    && publisher.when < *entry.end
                {
                    let from_ver = None;
                    let to_ver = Some(&publisher.version);
                    let criteria = criteria_mapper.criteria_from_list(&entry.criteria);
                    let origin = DeltaEdgeOrigin::Trusted { publisher_index };
                    // While the import freshness is technically based on the publisher being a
                    // fresh import, we use this as the _audit_ freshness here because a trusted
                    // entry should be put at the same caveat level ordering as other audits (which
                    // is determined from freshness later on).
                    let freshness = DeltaEdgeFreshness::new(publisher.is_fresh_import, false);

                    forward_audits.entry(from_ver).or_default().push(DeltaEdge {
                        version: to_ver,
                        criteria: criteria.clone(),
                        origin: origin.clone(),
                        freshness,
                    });
                    backward_audits.entry(to_ver).or_default().push(DeltaEdge {
                        version: from_ver,
                        criteria,
                        origin,
                        freshness,
                    });
                }
            }
        }

        // For each unpublished entry for the crate we're aware of, generate a delta audit for that edge.
        for (unpublished_index, unpublished) in unpublished.iter().enumerate() {
            let from_ver = Some(&unpublished.audited_as);
            let to_ver = Some(&unpublished.version);
            let criteria = criteria_mapper.all_criteria();
            let origin = DeltaEdgeOrigin::Unpublished { unpublished_index };
            let freshness = DeltaEdgeFreshness::new(unpublished.is_fresh_import, false);

            forward_audits.entry(from_ver).or_default().push(DeltaEdge {
                version: to_ver,
                criteria: criteria.clone(),
                origin: origin.clone(),
                freshness,
            });
            backward_audits.entry(to_ver).or_default().push(DeltaEdge {
                version: from_ver,
                criteria,
                origin,
                freshness,
            });
        }

        // Exempted entries are equivalent to full-audits
        if let Some(alloweds) = exemptions {
            for (exemption_index, allowed) in alloweds.iter().enumerate() {
                let from_ver = None;
                let to_ver = Some(&allowed.version);
                let criteria = criteria_mapper.criteria_from_list(&allowed.criteria);
                let origin = DeltaEdgeOrigin::Exemption { exemption_index };

                // For simplicity, turn 'exemptions' entries into deltas from None.
                forward_audits.entry(from_ver).or_default().push(DeltaEdge {
                    version: to_ver,
                    criteria: criteria.clone(),
                    origin: origin.clone(),
                    freshness: DeltaEdgeFreshness::Stale,
                });
                backward_audits.entry(to_ver).or_default().push(DeltaEdge {
                    version: from_ver,
                    criteria,
                    origin,
                    freshness: DeltaEdgeFreshness::Stale,
                });
            }
        }

        // Reject forbidden packages (violations)
        let mut violations = Vec::new();
        for (violation_source, violation_entry) in &violation_nodes {
            // Ok this is kind of weird. We want to reject any audits which contain any of these criteria.
            // Normally we would slap all the criteria in this entry into a set and do some kind of set
            // comparison, but that's not quite right. Here are the cases we want to work:
            //
            // * violation: safe-to-deploy, audit: safe-to-deploy -- ERROR!
            // * violation: safe-to-deploy, audit: safe-to-run    -- OK!
            // * violation: safe-to-run,    audit: safe-to-deploy -- ERROR!
            // * violation: [a, b],         audit: [a, c]         -- ERROR!
            //
            // The first 3 cases are correctly handled by audit.contains(violation)
            // but the last one isn't. I think the correct solution to this is to
            // *for each individual entry in the violation* do audit.contains(violation).
            // If any of those queries trips, then it's an ERROR.
            //
            // Note that this would also more correctly handle [safe-to-deploy, safe-to-run]
            // as a violation entry because it would effectively become safe-to-run instead
            // of safe-to-deploy, which is the correct and desirable behaviour!
            //
            // So here we make a criteria set for each entry in the violation.
            let violation_criterias = violation_entry
                .criteria
                .iter()
                .map(|c| criteria_mapper.criteria_from_list([&c]))
                .collect::<Vec<_>>();
            let violation_range = if let AuditKind::Violation { violation } = &violation_entry.kind
            {
                violation
            } else {
                unreachable!("violation_entry wasn't a Violation?");
            };

            // Note if this entry conflicts with any exemptions
            if let Some(alloweds) = exemptions {
                for allowed in alloweds {
                    let audit_criteria = criteria_mapper.criteria_from_list(&allowed.criteria);
                    let has_violation = violation_criterias
                        .iter()
                        .any(|v| audit_criteria.contains(v));
                    if !has_violation {
                        continue;
                    }
                    if violation_range.matches(&allowed.version) {
                        violations.push(ViolationConflict::UnauditedConflict {
                            violation_source: violation_source.clone(),
                            violation: (*violation_entry).clone(),
                            exemptions: allowed.clone(),
                        });
                    }
                }
            }

            // Note if this entry conflicts with any audits
            for (namespace, _origin, audit) in all_audits.clone() {
                let audit_criteria = criteria_mapper.criteria_from_list(&audit.criteria);
                let has_violation = violation_criterias
                    .iter()
                    .any(|v| audit_criteria.contains(v));
                if !has_violation {
                    continue;
                }
                match &audit.kind {
                    AuditKind::Full { version, .. } => {
                        if violation_range.matches(version) {
                            violations.push(ViolationConflict::AuditConflict {
                                violation_source: violation_source.clone(),
                                violation: (*violation_entry).clone(),
                                audit_source: namespace.clone(),
                                audit: audit.clone(),
                            });
                        }
                    }
                    AuditKind::Delta { from, to, .. } => {
                        if violation_range.matches(from) || violation_range.matches(to) {
                            violations.push(ViolationConflict::AuditConflict {
                                violation_source: violation_source.clone(),
                                violation: (*violation_entry).clone(),
                                audit_source: namespace.clone(),
                                audit: audit.clone(),
                            });
                        }
                    }
                    AuditKind::Violation { .. } => {
                        // don't care
                    }
                }
            }
        }

        // If we enountered any violations, report them.
        if !violations.is_empty() {
            return Err(violations);
        }

        Ok(AuditGraph {
            forward_audits,
            backward_audits,
        })
    }

    /// Search for a path in this AuditGraph which indicates that the given
    /// version of the crate satisfies the given criteria. Returns the path used
    /// for that proof if successful, and information about the versions which
    /// could be reached from both the target and root if unsuccessful.
    pub fn search(
        &self,
        criteria_idx: usize,
        version: &VetVersion,
        mode: SearchMode,
    ) -> Result<Vec<DeltaEdgeOrigin>, SearchFailure> {
        // First, search backwards, starting from the target, as that's more
        // likely to have a limited graph to traverse.
        // This also interacts well with the search ordering from
        // search_for_path, which prefers edges closer to `None` when
        // traversing.
        search_for_path(
            &self.backward_audits,
            criteria_idx,
            Some(version),
            None,
            mode,
        )
        .map_err(|reachable_from_target| {
            assert!(
                mode != SearchMode::RegenerateExemptions,
                "RegenerateExemptions search mode cannot fail"
            );

            // The search failed, perform the search in the other direction
            // in order to also get the set of nodes reachable from the
            // root. We can `unwrap_err()` here, as we'll definitely fail.
            let reachable_from_root = search_for_path(
                &self.forward_audits,
                criteria_idx,
                None,
                Some(version),
                mode,
            )
            .unwrap_err();
            SearchFailure {
                reachable_from_root,
                reachable_from_target,
            }
        })
    }
}

/// Core algorithm used to search for a path between two versions within a
/// DirectedAuditGraph. A path with the fewest "caveats" will be used in order
/// to minimize dependence on exemptions and freshly imported audits.
fn search_for_path(
    audit_graph: &DirectedAuditGraph<'_>,
    criteria_idx: usize,
    from_version: Option<&VetVersion>,
    to_version: Option<&VetVersion>,
    mode: SearchMode,
) -> Result<Vec<DeltaEdgeOrigin>, SortedSet<Option<VetVersion>>> {
    assert!(
        mode != SearchMode::RegenerateExemptions || to_version.is_none(),
        "RegenerateExemptions requires searching towards root"
    );

    // Search for any path through the graph with edges that satisfy criteria.
    // Finding any path validates that we satisfy that criteria.
    //
    // All full-audits and exemptions have been "desugarred" to a delta from
    // None, meaning our graph now has exactly one source and one sink,
    // significantly simplifying the start and end conditions.
    //
    // Some edges have caveats which we want to avoid requiring, so we defer
    // edges with caveats to be checked later, after all edges without caveats
    // have been visited. This is done by storing work to do in a BinaryHeap,
    // sorted by the caveats which apply to each node. This means that if we
    // find a patch without using a node with caveats, it's unambiguous proof we
    // don't need edges with caveats.
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    enum CaveatLevel {
        None,
        NonImportableAudit,
        PreferredExemption,
        PreferredUnpublished,
        FreshPublisher,
        FreshImport,
        Exemption,
        Unpublished,
        FreshExemption,
    }

    #[derive(Debug)]
    struct Node<'a> {
        version: Option<&'a VetVersion>,
        origin_version: Option<&'a VetVersion>,
        path: Vec<DeltaEdgeOrigin>,
        caveat_level: CaveatLevel,
    }

    impl Node<'_> {
        fn key(&self) -> impl Ord + '_ {
            // Nodes are compared by caveat level. A lower caveat level makes
            // the node sort higher, as it will be stored in a max heap.
            //
            // Once we've sorted by all caveats, we sort by the version
            // (preferring lower versions), exemption origin version (preferring
            // smaller exemptions), the length of the path (preferring short
            // paths), and then the most recently added DeltaEdgeOrigin
            // (preferring more-local audits).
            //
            // NOTE: This ordering logic priorities assume `to_version == None`,
            // as we will only be searched in the other direction if the search
            // is guaranteed to fail, in which case ordering doesn't matter (as
            // we're going to visit every node).
            Reverse((
                self.caveat_level,
                self.version,
                self.exemption_origin_version(),
                self.path.len(),
                self.path.last(),
            ))
        }

        // To make better decisions when selecting exemptions, exemption edges
        // with lower origin versions are preferred over those with higher
        // origin versions. This is checked before path length, as a longer path
        // which uses a smaller exemption is generally preferred to a short one
        // which uses a full-exemption. This is ignored for other edge types.
        fn exemption_origin_version(&self) -> Option<&VetVersion> {
            if matches!(
                self.caveat_level,
                CaveatLevel::PreferredExemption
                    | CaveatLevel::Exemption
                    | CaveatLevel::FreshExemption
            ) {
                self.origin_version
            } else {
                None
            }
        }
    }
    impl PartialEq for Node<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.key() == other.key()
        }
    }
    impl Eq for Node<'_> {}
    impl PartialOrd for Node<'_> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Node<'_> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.key().cmp(&other.key())
        }
    }

    let mut queue = BinaryHeap::new();
    queue.push(Node {
        version: from_version,
        origin_version: from_version,
        path: Vec::new(),
        caveat_level: CaveatLevel::None,
    });

    let mut visited = SortedSet::new();
    while let Some(Node {
        version,
        origin_version: _,
        path,
        caveat_level,
    }) = queue.pop()
    {
        // If We've been to a version before, We're not going to get a better
        // result revisiting it, as we visit the "best" edges first.
        if !visited.insert(version) {
            continue;
        }

        // We found a path! Return a search result reflecting what we
        // discovered.
        if version == to_version {
            return Ok(path);
        }

        // Apply deltas to move along to the next layer of the search, adding it
        // to our queue.
        let edges = audit_graph.get(&version).map(|v| &v[..]).unwrap_or(&[]);
        for edge in edges {
            // We'll allow any criteria if we're regenerating exemption edges.
            let allow_any_criteria = mode == SearchMode::RegenerateExemptions
                && matches!(edge.origin, DeltaEdgeOrigin::Exemption { .. });
            if !allow_any_criteria && !edge.criteria.has_criteria(criteria_idx) {
                // This edge never would have been useful to us.
                continue;
            }
            if visited.contains(&edge.version) {
                // We've been to the target of this edge already.
                continue;
            }

            // Compute the level of caveats which are being added by the current edge
            let edge_caveat_level = match &edge.origin {
                DeltaEdgeOrigin::StoredLocalAudit { importable, .. } if !importable => {
                    CaveatLevel::NonImportableAudit
                }
                DeltaEdgeOrigin::Exemption { .. } if mode == SearchMode::PreferExemptions => {
                    CaveatLevel::PreferredExemption
                }
                DeltaEdgeOrigin::Exemption { .. } => CaveatLevel::Exemption,
                DeltaEdgeOrigin::FreshExemption { .. } => unreachable!(),
                DeltaEdgeOrigin::Unpublished { .. } => match mode {
                    // When preferring exemptions, prefer existing unpublished
                    // entries to avoid imports.lock churn.
                    SearchMode::PreferExemptions if !edge.freshness.is_fresh() => {
                        CaveatLevel::PreferredUnpublished
                    }
                    SearchMode::PreferExemptions => CaveatLevel::Unpublished,
                    // Otherwise, prefer fresh to avoid outdated versions.
                    _ if edge.freshness.is_fresh() => CaveatLevel::PreferredUnpublished,
                    _ => CaveatLevel::Unpublished,
                },
                _ => match edge.freshness {
                    DeltaEdgeFreshness::Stale => CaveatLevel::None,
                    DeltaEdgeFreshness::FreshPublisher => CaveatLevel::FreshPublisher,
                    DeltaEdgeFreshness::Fresh => CaveatLevel::FreshImport,
                },
            };

            queue.push(Node {
                version: edge.version,
                origin_version: version,
                path: path.iter().cloned().chain([edge.origin.clone()]).collect(),
                caveat_level: caveat_level.max(edge_caveat_level),
            });
        }

        // If we're regenerating exemptions, add a fresh exemption edge which
        // directly leads to the root version.
        if mode == SearchMode::RegenerateExemptions {
            queue.push(Node {
                version: None,
                origin_version: version,
                path: path
                    .iter()
                    .cloned()
                    .chain([DeltaEdgeOrigin::FreshExemption {
                        version: version
                            .expect("RegenerateExemptions requires searching towards None")
                            .clone(),
                    }])
                    .collect(),
                caveat_level: caveat_level.max(CaveatLevel::FreshExemption),
            })
        }
    }

    // Complete failure, we need more audits for this package, so all that
    // matters is what nodes were reachable.
    Err(visited.into_iter().map(|v| v.cloned()).collect())
}

impl ResolveReport<'_> {
    pub fn has_errors(&self) -> bool {
        // Just check the conclusion
        !matches!(self.conclusion, Conclusion::Success(_))
    }

    pub fn _has_warnings(&self) -> bool {
        false
    }

    pub fn compute_suggest(
        &self,
        cfg: &Config,
        store: &Store,
        network: Option<&Network>,
    ) -> Result<Option<Suggest<'_>>, SuggestError> {
        let _suggest_span = trace_span!("suggest").entered();
        let fail = if let Conclusion::FailForVet(fail) = &self.conclusion {
            fail
        } else {
            // Nothing to suggest unless we failed for vet
            return Ok(None);
        };

        let cache = Cache::acquire(cfg)?;

        let warnings = RefCell::new(Vec::new());

        let mut store = store.clone_for_suggest(false);
        let registry = if let (false, OutputFormat::Human, Some(network)) = (
            cfg.cli.no_registry_suggestions,
            cfg.cli.output_format,
            network,
        ) {
            tokio::runtime::Handle::current()
                .block_on(store.fetch_registry_audits(cfg, network, &cache))
                .map_err(|error| warnings.borrow_mut().push(error.to_string()))
                .ok()
        } else {
            None
        };

        const THIS_PROJECT: &str = "this project";

        let mut trusted_publishers: FastMap<CratesSourceId, SortedSet<ImportName>> = FastMap::new();
        for trusted_entry in store.audits.trusted.values().flatten() {
            trusted_publishers
                .entry(trusted_entry.source.clone())
                .or_default()
                .insert(THIS_PROJECT.to_owned());
        }
        for (import_name, audits_file) in store.imported_audits() {
            for trusted_entry in audits_file.trusted.values().flatten() {
                trusted_publishers
                    .entry(trusted_entry.source.clone())
                    .or_default()
                    .insert(import_name.clone());
            }
        }

        let suggest_progress =
            progress_bar("Suggesting", "relevant audits", fail.failures.len() as u64);

        let mut suggestions = tokio::runtime::Handle::current()
            .block_on(join_all(fail.failures.iter().map(
                |(package, audit_failure)| async {
                    let _guard = IncProgressOnDrop(&suggest_progress, 1);

                    let package_version = package.vet_version();

                    let result = self
                        .results
                        .get(package.id())
                        .expect("failed package without ResolveResults?");

                    // Precompute some "notable" parents
                    let notable_parents: Vec<_> = package
                        .reverse_direct_links()
                        .map(|link| link.from().name().to_owned())
                        .collect();

                    let Some((suggested_diff, extra_suggested_diff)) = suggest_delta(
                        &cfg.package_graph,
                        network,
                        &cache,
                        package.name(),
                        &package_version,
                        audit_failure
                            .criteria_failures
                            .indices()
                            .map(|criteria_idx| {
                                result.search_results[criteria_idx].as_ref().unwrap_err()
                            }),
                        &warnings,
                    )
                    .await
                    else {
                        return vec![];
                    };

                    // Attempt to look up the publisher of the target version
                    // for the suggested diff, and also record whether the given
                    // package has a sole publisher.
                    let crates_io_info = cache.crates_io_info(network, package.name()).await.ok();
                    let publisher_source = match (suggested_diff.to.as_semver(), &crates_io_info) {
                        (Some(semver), Some(metadata)) => metadata
                            .versions
                            .get(semver)
                            .and_then(|details| details.source.as_ref()),
                        _ => None,
                    };
                    let publisher_count = crates_io_info
                        .iter()
                        .flat_map(|m| m.versions.values())
                        .flat_map(|details| &details.source)
                        .collect::<FastSet<_>>()
                        .len();

                    // Compute the trust hint, which is the information used to generate "consider
                    // cargo trust FOO" messages. There can be multiple potential hints, but we
                    // only provide the most relevant one. If the publisher of the in-use version
                    // of the crate is potentially trustworthy, we suggest that. If not (and we
                    // don't already have at least one trusted entry for this crate), we iterate
                    // over the crate releases in reverse order to see if another version was
                    // published by a potentially-trustworth author. We pick the first one of
                    // those we find, if any.
                    let trust_hint = {
                        let mut exact_version = false;
                        let source_for_hint = if publisher_source
                            .is_some_and(|i| trusted_publishers.contains_key(i))
                        {
                            exact_version = true;
                            publisher_source
                        } else if !store.audits.trusted.contains_key(package.name()) {
                            crates_io_info.as_ref().and_then(|metadata| {
                                metadata
                                    .versions
                                    .iter()
                                    .rev()
                                    .filter_map(|(_, details)| details.source.as_ref())
                                    .find(|i| trusted_publishers.contains_key(i))
                            })
                        } else {
                            None
                        };

                        source_for_hint.map(|source| {
                            let mut trusted_by: Vec<String> = trusted_publishers
                                .get(source)
                                .unwrap()
                                .iter()
                                .cloned()
                                .collect();
                            // If we're already trusted by this project, don't
                            // bother listing anyone else.
                            if trusted_by.iter().any(|s| s == THIS_PROJECT) {
                                trusted_by.retain(|s| s == THIS_PROJECT);
                            }
                            let publisher = cache.publisher_id_to_source(source).unwrap();
                            TrustHint {
                                trusted_by,
                                publisher,
                                exact_version,
                            }
                        })
                    };

                    let publisher_login = publisher_source
                        .as_ref()
                        .and_then(|source| cache.publisher_id_to_source(source))
                        .map(|pi| pi.as_identifier().to_owned());

                    let mut registry_suggestion: Vec<_> = join_all(registry.iter().flatten().map(
                        |(name, entry, audits)| async {
                            // Don't search for git deltas in the registry.
                            if suggested_diff.to.git_rev.is_some() {
                                return None;
                            }

                            let audit_graph = AuditGraph::build(
                                &store,
                                &self.criteria_mapper,
                                package.name(),
                                Some(audits),
                            )
                            .ok()?;

                            // If we have an extra diff, only try to search for
                            // a path to the "from" version in that diff, to
                            // make the results more comparable.
                            let target_version = extra_suggested_diff
                                .as_ref()
                                .and_then(|d| d.from.as_ref())
                                .unwrap_or(&package_version);

                            let failures: Vec<_> = audit_failure
                                .criteria_failures
                                .indices()
                                .filter_map(|criteria_idx| {
                                    audit_graph
                                        .search(
                                            criteria_idx,
                                            target_version,
                                            SearchMode::PreferExemptions,
                                        )
                                        .err()
                                })
                                .collect();

                            let (registry_suggested_diff, _) = suggest_delta(
                                &cfg.package_graph,
                                network,
                                &cache,
                                package.name(),
                                target_version,
                                failures.iter(),
                                &warnings,
                            )
                            .await?;

                            if registry_suggested_diff.diffstat.count()
                                < suggested_diff.diffstat.count()
                            {
                                Some(RegistrySuggestion {
                                    name: name.clone(),
                                    url: entry.url.clone(),
                                    diff: registry_suggested_diff,
                                })
                            } else {
                                None
                            }
                        },
                    ))
                    .await
                    .into_iter()
                    .flatten()
                    .collect();
                    registry_suggestion.sort_by_key(|suggestion| suggestion.diff.diffstat.count());

                    extra_suggested_diff
                        .into_iter()
                        .map(|suggested_diff| SuggestItem {
                            package: *package,
                            suggested_diff,
                            suggested_criteria: audit_failure.criteria_failures.clone(),
                            notable_parents: notable_parents.clone(),
                            publisher_login: None,
                            trust_hint: None,
                            is_sole_publisher: false,
                            registry_suggestion: vec![],
                        })
                        .chain([SuggestItem {
                            package: *package,
                            suggested_diff,
                            suggested_criteria: audit_failure.criteria_failures.clone(),
                            notable_parents: notable_parents.clone(),
                            publisher_login,
                            trust_hint,
                            is_sole_publisher: publisher_count == 1,
                            registry_suggestion,
                        }])
                        .collect()
                },
            )))
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        // First sort by diff size (ascending), then package name, then version
        // being certified, to have stable output ordering.
        suggestions.sort_by_key(|item| {
            (
                item.suggested_diff.diffstat.count(),
                item.package.name(),
                item.suggested_diff.to.clone(),
            )
        });

        // If we have duplicate suggestions in the output, e.g. due to multiple
        // versions of the same crate requiring the same new audit, deduplicate
        // them in the output to avoid clutter.
        suggestions.dedup_by(|a, b| {
            if a.package.name() == b.package.name() && a.suggested_diff == b.suggested_diff {
                // Per the `dedup_by` documentation, if true is returned, `a`
                // will be removed. Preserve its notable parents.
                b.notable_parents.extend_from_slice(&a.notable_parents);
                true
            } else {
                false
            }
        });

        // Sort and remove any duplicate entries from `notable_parents`.
        for s in &mut suggestions {
            s.notable_parents.sort();
            s.notable_parents.dedup();
        }

        let total_lines = suggestions
            .iter()
            .map(|s| s.suggested_diff.diffstat.count())
            .sum();

        let mut suggestions_by_criteria = SortedMap::<CriteriaName, Vec<SuggestItem>>::new();
        for s in suggestions.clone().into_iter() {
            // Generate a suggestion for which criteria to use for the given
            // suggestion. For each criteria, also list out others which would
            // imply the required criteria to surface the full set of options.
            let criteria_names = self
                .criteria_mapper
                .minimal_indices(&s.suggested_criteria)
                .map(|criteria_idx| {
                    let name = self.criteria_mapper.criteria_name(criteria_idx);
                    let implied_by = self
                        .criteria_mapper
                        .implied_by_indices(criteria_idx)
                        .map(|idx| format!("or {}", self.criteria_mapper.criteria_name(idx)))
                        .collect::<Vec<_>>();

                    if implied_by.is_empty() {
                        name.to_owned()
                    } else {
                        format!("{} ({})", name, implied_by.join(", "))
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");

            suggestions_by_criteria
                .entry(criteria_names)
                .or_default()
                .push(s);
        }

        Ok(Some(Suggest {
            suggestions,
            suggestions_by_criteria,
            total_lines,
            warnings: warnings.into_inner(),
        }))
    }

    /// Given a package name and a delta to be certified, determine the set of
    /// additional criteria for that delta/version pair which would have a
    /// healing impact on the audit graph.
    ///
    /// This is more reliable than running a suggest and looking for a matching
    /// output, as it will also select criteria for non-suggested audits.
    pub fn compute_suggested_criteria(
        &self,
        package_name: PackageStr<'_>,
        from: Option<&VetVersion>,
        to: &VetVersion,
    ) -> Vec<CriteriaName> {
        let fail = if let Conclusion::FailForVet(fail) = &self.conclusion {
            fail
        } else {
            return Vec::new();
        };

        let mut criteria = self.criteria_mapper.no_criteria();

        // Make owned versions of the `Version` types, such that we can look
        // them up in search results more easily.
        let from = from.cloned();
        let to = Some(to.clone());

        // Enumerate over the recorded failures, adding any criteria for this
        // delta which would connect that package version into the audit graph.
        for (package, audit_failure) in &fail.failures {
            if package.name() != package_name {
                continue;
            }

            let result = self
                .results
                .get(package.id())
                .expect("failure without ResolveResults?");
            for criteria_idx in audit_failure.criteria_failures.indices() {
                let search_result = &result.search_results[criteria_idx];
                if let Err(SearchFailure {
                    reachable_from_root,
                    reachable_from_target,
                }) = search_result
                {
                    if reachable_from_target.contains(&to) && reachable_from_root.contains(&from) {
                        criteria.set_criteria(criteria_idx);
                    }
                }
            }
        }

        self.criteria_mapper
            .criteria_names(&criteria)
            .map(str::to_owned)
            .collect()
    }

    /// Print a full human-readable report
    pub fn print_human(
        &self,
        out: &Arc<dyn Out>,
        cfg: &Config,
        suggest: Option<&Suggest>,
    ) -> Result<(), std::io::Error> {
        match &self.conclusion {
            Conclusion::Success(res) => res.print_human(out, self, cfg),
            Conclusion::FailForViolationConflict(res) => res.print_human(out, self, cfg),
            Conclusion::FailForVet(res) => res.print_human(out, self, cfg, suggest),
        }
    }

    /// Print only the suggest portion of a human-readable report
    pub fn print_suggest_human(
        &self,
        out: &Arc<dyn Out>,
        _cfg: &Config,
        suggest: Option<&Suggest>,
    ) -> Result<(), std::io::Error> {
        if let Some(suggest) = suggest {
            suggest.print_human(out, self)?;
        } else {
            // This API is only used for vet-suggest
            writeln!(out, "Nothing to suggest, you're fully audited!");
        }
        Ok(())
    }

    /// Print a full json report
    pub fn print_json(
        &self,
        out: &Arc<dyn Out>,
        suggest: Option<&Suggest>,
    ) -> Result<(), miette::Report> {
        let result = JsonReport {
            conclusion: match &self.conclusion {
                Conclusion::Success(success) => {
                    let json_package = |package: &PackageMetadata<'_>| JsonPackage {
                        name: package.name().to_owned(),
                        version: package.vet_version(),
                    };
                    JsonReportConclusion::Success(JsonReportSuccess {
                        vetted_fully: success.vetted_fully.iter().map(json_package).collect(),
                        vetted_partially: success
                            .vetted_partially
                            .iter()
                            .map(json_package)
                            .collect(),
                        vetted_with_exemptions: success
                            .vetted_with_exemptions
                            .iter()
                            .map(json_package)
                            .collect(),
                    })
                }
                Conclusion::FailForViolationConflict(fail) => {
                    JsonReportConclusion::FailForViolationConflict(
                        JsonReportFailForViolationConflict {
                            violations: fail
                                .violations
                                .iter()
                                .map(|(package, violations)| {
                                    let key =
                                        format!("{}:{}", package.name(), package.vet_version());
                                    (key, violations.clone())
                                })
                                .collect(),
                        },
                    )
                }
                Conclusion::FailForVet(fail) => {
                    // FIXME: How to report confidence for suggested criteria?
                    let json_suggest_item = |item: &SuggestItem| JsonSuggestItem {
                        name: item.package.name().to_owned(),
                        notable_parents: FormatShortList::string(item.notable_parents.clone()),
                        suggested_criteria: self
                            .criteria_mapper
                            .criteria_names(&item.suggested_criteria)
                            .map(|s| s.to_owned())
                            .collect(),
                        suggested_diff: item.suggested_diff.clone(),
                    };
                    JsonReportConclusion::FailForVet(JsonReportFailForVet {
                        failures: fail
                            .failures
                            .iter()
                            .map(|(package, audit_fail)| JsonVetFailure {
                                name: package.name().to_owned(),
                                version: package.vet_version(),
                                missing_criteria: self
                                    .criteria_mapper
                                    .criteria_names(&audit_fail.criteria_failures)
                                    .map(|s| s.to_owned())
                                    .collect(),
                            })
                            .collect(),
                        suggest: suggest.as_ref().map(|suggest| JsonSuggest {
                            suggestions: suggest
                                .suggestions
                                .iter()
                                .map(json_suggest_item)
                                .collect(),
                            suggest_by_criteria: suggest
                                .suggestions_by_criteria
                                .iter()
                                .map(|(criteria, items)| {
                                    (
                                        criteria.to_owned(),
                                        items.iter().map(json_suggest_item).collect::<Vec<_>>(),
                                    )
                                })
                                .collect(),
                            total_lines: suggest.total_lines,
                        }),
                    })
                }
            },
        };

        serde_json::to_writer_pretty(&**out, &result).into_diagnostic()?;

        Ok(())
    }
}

impl Success<'_> {
    pub fn print_human(
        &self,
        out: &Arc<dyn Out>,
        _report: &ResolveReport<'_>,
        _cfg: &Config,
    ) -> Result<(), std::io::Error> {
        let fully_audited_count = self.vetted_fully.len();
        let partially_audited_count: usize = self.vetted_partially.len();
        let exemptions_count = self.vetted_with_exemptions.len();

        // Figure out how many entries we're going to print
        let mut count_count = (fully_audited_count != 0) as usize
            + (partially_audited_count != 0) as usize
            + (exemptions_count != 0) as usize;

        // Print out a summary of how we succeeded
        if count_count == 0 {
            writeln!(
                out,
                "Vetting Succeeded (because you have no third-party dependencies)"
            );
        } else {
            write!(out, "Vetting Succeeded (");

            if fully_audited_count != 0 {
                write!(out, "{fully_audited_count} fully audited");
                count_count -= 1;
                if count_count > 0 {
                    write!(out, ", ");
                }
            }
            if partially_audited_count != 0 {
                write!(out, "{partially_audited_count} partially audited");
                count_count -= 1;
                if count_count > 0 {
                    write!(out, ", ");
                }
            }
            if exemptions_count != 0 {
                write!(out, "{exemptions_count} exempted");
                count_count -= 1;
                if count_count > 0 {
                    write!(out, ", ");
                }
            }

            writeln!(out, ")");
        }
        Ok(())
    }
}

impl Suggest<'_> {
    pub fn print_human(
        &self,
        out: &Arc<dyn Out>,
        _report: &ResolveReport<'_>,
    ) -> Result<(), std::io::Error> {
        for (criteria, suggestions) in &self.suggestions_by_criteria {
            writeln!(out, "recommended audits for {criteria}:");

            let mut strings = suggestions
                .iter()
                .map(|item| {
                    let cmd = match &item.suggested_diff.from {
                        Some(from) => format!(
                            "cargo vet diff {} {} {}",
                            item.package.name(),
                            from,
                            item.suggested_diff.to
                        ),
                        None => format!(
                            "cargo vet inspect {} {}",
                            item.package.name(),
                            item.suggested_diff.to
                        ),
                    };
                    let publisher = item
                        .publisher_login
                        .clone()
                        .unwrap_or_else(|| "UNKNOWN".into());
                    let parents = FormatShortList::string(item.notable_parents.clone());
                    let diffstat = match &item.suggested_diff.from {
                        Some(_) => format!("{}", item.suggested_diff.diffstat),
                        None => format!("{} lines", item.suggested_diff.diffstat.count()),
                    };
                    (cmd, publisher, parents, diffstat, item)
                })
                .collect::<Vec<_>>();

            let (h0, h1, h2, h3) = ("Command", "Publisher", "Used By", "Audit Size");
            let mut max0 = console::measure_text_width(h0);
            let mut max1 = console::measure_text_width(h1);
            let mut max2 = console::measure_text_width(h2);
            for (s0, s1, s2, ..) in &mut strings {
                // If the command is too long (happens occasionally, particularly with @git
                // version specifiers), wrap subsequent columns to the next line.
                const MAX_COMMAND_CHARS: usize = 52;
                let command_width = console::measure_text_width(s0);
                if command_width > MAX_COMMAND_CHARS {
                    s0.push('\n');
                    s0.push_str(&" ".repeat(MAX_COMMAND_CHARS + 4));
                }
                max0 = max0.max(command_width.min(MAX_COMMAND_CHARS));
                max1 = max1.max(console::measure_text_width(s1));
                max2 = max2.max(console::measure_text_width(s2));
            }

            writeln!(
                out,
                "{}",
                out.style()
                    .bold()
                    .dim()
                    .apply_to(format_args!("    {h0:max0$}  {h1:max1$}  {h2:max2$}  {h3}"))
            );
            for (s0, s1, s2, s3, item) in strings {
                write!(
                    out,
                    "{}",
                    out.style()
                        .cyan()
                        .bold()
                        .apply_to(format_args!("    {s0:max0$}"))
                );
                writeln!(out, "  {s1:max1$}  {s2:max2$}  {s3}");

                let dim = out.style().dim();
                for suggestion in &item.registry_suggestion {
                    writeln!(
                        out,
                        "      {} {} {}",
                        dim.clone().apply_to("NOTE:"),
                        dim.clone()
                            .cyan()
                            .bold()
                            .apply_to(format_args!("cargo vet import {}", suggestion.name)),
                        dim.clone()
                            .apply_to(match suggestion.diff.diffstat.count() {
                                0 => "would eliminate this".to_owned(),
                                n => format!("would reduce this to a {n}-line diff"),
                            }),
                    );
                }
                if let Some(hint) = &item.trust_hint {
                    let trust = if hint.trusted_by.len() == 1 {
                        "trusts"
                    } else {
                        "trust"
                    };
                    let caveat = if !hint.exact_version {
                        ", who published another version of this crate"
                    } else {
                        ""
                    };
                    let publisher = &hint.publisher;
                    let trusted_by = FormatShortList::new(hint.trusted_by.clone());
                    writeln!(
                        out,
                        "      {} {}",
                        dim.clone().apply_to(format_args!(
                            "NOTE: {trusted_by} {trust} {publisher}{caveat} - consider",
                        )),
                        if item.is_sole_publisher {
                            let this_cmd = format!("cargo vet trust {}", item.package.name());
                            let all_cmd =
                                format!("cargo vet trust --all {}", publisher.as_identifier());
                            format!(
                                "{} {} {}",
                                dim.clone().cyan().apply_to(this_cmd),
                                dim.clone().apply_to("or"),
                                dim.clone().cyan().apply_to(all_cmd),
                            )
                        } else {
                            let cmd = format!(
                                "cargo vet trust {} {}",
                                item.package.name(),
                                publisher.as_identifier()
                            );
                            dim.clone().cyan().apply_to(cmd).to_string()
                        }
                    );
                }
            }

            writeln!(out);
        }

        writeln!(out, "estimated audit backlog: {} lines", self.total_lines);

        if !self.warnings.is_empty() {
            writeln!(out);
            for warning in &self.warnings {
                writeln!(
                    out,
                    "{}: {warning}",
                    out.style().yellow().apply_to("WARNING"),
                );
            }
        }

        writeln!(out);
        writeln!(out, "Use |cargo vet certify| to record the audits.");

        Ok(())
    }
}

impl FailForVet<'_> {
    fn print_human(
        &self,
        out: &Arc<dyn Out>,
        report: &ResolveReport<'_>,
        _cfg: &Config,
        suggest: Option<&Suggest>,
    ) -> Result<(), std::io::Error> {
        writeln!(out, "Vetting Failed!");
        writeln!(out);
        writeln!(out, "{} unvetted dependencies:", self.failures.len());
        let mut failures = self.failures.clone();
        failures.sort_by_key(|(failed, _)| failed.vet_version());
        failures.sort_by_key(|(failed, _)| failed.name());
        for (failed_package, failed_audit) in failures {
            let criteria = report
                .criteria_mapper
                .criteria_names(&failed_audit.criteria_failures)
                .collect::<Vec<_>>();

            let label = format!(
                "  {}:{}",
                failed_package.name(),
                failed_package.vet_version()
            );
            writeln!(out, "{label} missing {criteria:?}");
        }

        // Suggest output generally requires hitting the network.
        if let Some(suggest) = suggest {
            writeln!(out);
            suggest.print_human(out, report)?;
        }

        Ok(())
    }
}

impl FailForViolationConflict<'_> {
    fn print_human(
        &self,
        out: &Arc<dyn Out>,
        _report: &ResolveReport<'_>,
        _cfg: &Config,
    ) -> Result<(), std::io::Error> {
        writeln!(out, "Violations Found!");

        for (package, violations) in &self.violations {
            writeln!(out, "  {}:{}", package.name(), package.vet_version());
            for violation in violations {
                match violation {
                    ViolationConflict::UnauditedConflict {
                        violation_source,
                        violation,
                        exemptions,
                    } => {
                        write!(out, "    the ");
                        print_exemption(out, exemptions)?;
                        write!(out, "    conflicts with ");
                        print_entry(out, violation_source, violation)?;
                    }
                    ViolationConflict::AuditConflict {
                        violation_source,
                        violation,
                        audit_source,
                        audit,
                    } => {
                        write!(out, "    the ");
                        print_entry(out, audit_source, audit)?;
                        write!(out, "    conflicts with ");
                        print_entry(out, violation_source, violation)?;
                    }
                }
                writeln!(out);
            }
        }

        fn print_exemption(
            out: &Arc<dyn Out>,
            entry: &ExemptedDependency,
        ) -> Result<(), std::io::Error> {
            writeln!(out, "exemption {}", entry.version);
            writeln!(out, "      criteria: {:?}", entry.criteria);
            if let Some(notes) = &entry.notes {
                writeln!(out, "      notes: {notes}");
            }
            Ok(())
        }

        fn print_entry(
            out: &Arc<dyn Out>,
            source: &Option<ImportName>,
            entry: &AuditEntry,
        ) -> Result<(), std::io::Error> {
            match source {
                None => write!(out, "own "),
                Some(name) => write!(out, "foreign ({name}) "),
            }
            match &entry.kind {
                AuditKind::Full { version, .. } => {
                    writeln!(out, "audit {version}");
                }
                AuditKind::Delta { from, to, .. } => {
                    writeln!(out, "audit {from} -> {to}");
                }
                AuditKind::Violation { violation } => {
                    writeln!(out, "violation against {violation}");
                }
            }
            writeln!(out, "      criteria: {:?}", entry.criteria);
            for (idx, who) in entry.who.iter().enumerate() {
                if idx == 0 {
                    write!(out, "      who: {who}");
                } else {
                    write!(out, ", {who}");
                }
            }
            if !entry.who.is_empty() {
                writeln!(out);
            }
            if let Some(notes) = &entry.notes {
                writeln!(out, "      notes: {notes}");
            }
            Ok(())
        }

        Ok(())
    }
}

async fn suggest_delta(
    package_graph: &guppy::graph::PackageGraph,
    network: Option<&Network>,
    cache: &Cache,
    package_name: PackageStr<'_>,
    package_version: &VetVersion,
    failures: impl Iterator<Item = &SearchFailure>,
    warnings: &RefCell<Vec<String>>,
) -> Option<(DiffRecommendation, Option<DiffRecommendation>)> {
    // Fetch the set of known versions from crates.io so we know which versions
    // we'll have sources for.
    let known_versions = if let Some(network) = network {
        cache.published_versions(network, package_name).await.ok()
    } else {
        None
    };

    // Collect up the details of how we failed
    struct Reachable<'a> {
        from_root: SortedSet<&'a Option<VetVersion>>,
        from_target: SortedSet<&'a Option<VetVersion>>,
    }
    let mut reachable = None::<Reachable<'_>>;
    for SearchFailure {
        reachable_from_root,
        reachable_from_target,
    } in failures
    {
        if let Some(Reachable {
            from_root,
            from_target,
        }) = reachable.as_mut()
        {
            // This does the right thing in the common cases, by restricting
            // ourselves to the reachable nodes that are common to all failures,
            // so that we can suggest just one change that will fix everything.
            from_root.retain(|ver| reachable_from_root.contains(ver));
            from_target.retain(|ver| reachable_from_target.contains(ver));
        } else {
            let version_has_sources = |ver: &&Option<VetVersion>| -> bool {
                // We always have sources for an empty crate.
                let Some(ver) = ver else {
                    return true;
                };
                // We only have git sources for the package itself.
                if ver.git_rev.is_some() {
                    return ver == package_version;
                }
                // We have sources if the version has been published to crates.io.
                //
                // For testing fallbacks or when we're offline, assume we always
                // have sources if the index is unavailable.
                known_versions
                    .as_ref()
                    .is_none_or(|versions| versions.contains_key(&ver.semver))
            };
            reachable = Some(Reachable {
                from_root: reachable_from_root
                    .iter()
                    .filter(version_has_sources)
                    .collect(),
                from_target: reachable_from_target
                    .iter()
                    .filter(version_has_sources)
                    .collect(),
            });
        }
    }

    let Some(Reachable {
        from_root,
        from_target,
    }) = &mut reachable
    else {
        // Nothing failed, return a dummy suggestion for an empty diff.
        return Some((
            DiffRecommendation {
                from: Some(package_version.clone()),
                to: package_version.clone(),
                diffstat: DiffStat {
                    insertions: 0,
                    deletions: 0,
                    files_changed: 0,
                },
            },
            None,
        ));
    };

    // If we have a git revision, we want to ensure the nearest published
    // version has been audited before we suggest an audit for the git revision
    // itself.
    let published_version;
    let mut extra_delta = None;
    if package_version.git_rev.is_some() {
        // Find the largest published revision with an equal or lower semver
        // than the git revision. This will be the published version we
        // encourage auditing first.
        let closest_below = if let Some(known_versions) = &known_versions {
            known_versions
                .keys()
                .filter(|&v| v <= &package_version.semver)
                .max()
        } else {
            // For testing fallbacks, assume the bare version has been published
            // to crates.io.
            Some(&package_version.semver)
        };
        published_version = closest_below.map(|semver| VetVersion {
            semver: semver.clone(),
            git_rev: None,
        });
        // If the closest published version is not already audited, replace the
        // target version with `published_version` in the reachable from target
        // set, ensuring that a delta to that version is suggested rather than a
        // full audit for the git revision.
        if !from_root.contains(&published_version) {
            from_target.remove(&Some(package_version.clone()));
            if from_target.insert(&published_version) {
                extra_delta = Some(Delta {
                    from: published_version.clone(),
                    to: package_version.clone(),
                });
            }
        }
    }

    // Now suggest solutions of those failures
    let mut candidates = Vec::new();
    for &dest in &*from_target {
        let closest_above = from_root.range::<&Option<VetVersion>, _>(dest..).next();
        let closest_below = from_root
            .range::<&Option<VetVersion>, _>(..dest)
            .next_back();

        for &closest in closest_below.into_iter().chain(closest_above) {
            candidates.push(Delta {
                from: closest.clone(),
                to: dest.clone().unwrap(),
            });
        }
    }

    let do_fetch_and_diffstat = |delta| async move {
        match cache
            .fetch_and_diffstat_package(package_graph, network, package_name, &delta)
            .await
        {
            Ok(diffstat) => Some(DiffRecommendation {
                diffstat,
                from: delta.from.clone(),
                to: delta.to.clone(),
            }),
            Err(err) => {
                // We don't want to actually error out completely here,
                // as other packages might still successfully diff!
                warnings
                    .borrow_mut()
                    .push(format!("error diffing {}:{}: {}", package_name, delta, err));
                None
            }
        }
    };

    let diffstats = join_all(candidates.into_iter().map(do_fetch_and_diffstat)).await;

    // If we need an "extra delta" due to a git revision, also get the diffstat
    // for that entry.
    let extra_diffstat = if let Some(delta) = extra_delta {
        do_fetch_and_diffstat(delta).await
    } else {
        None
    };

    let recommendation = diffstats
        .into_iter()
        .flatten()
        .min_by_key(|diff| diff.diffstat.count())?;

    Some((recommendation, extra_diffstat))
}

/// Resolve which entries in the store and imports.lock are required to
/// successfully audit this package. May return `None` if the package cannot
/// successfully vet given the restrictions placed upon it.
///
/// NOTE: A package which does not exist in the dependency will return the empty
/// set, as it does not have any audit requirements.
///
/// [`SearchMode`] controls how edges are selected when searching for paths.
#[tracing::instrument(skip(package_graph, criteria_mapper, requirements, store))]
fn resolve_package_required_entries(
    package_graph: &PackageGraph,
    criteria_mapper: &CriteriaMapper,
    requirements: &FastMap<&PackageId, CriteriaSet>,
    store: &Store,
    package_name: PackageStr<'_>,
    search_mode: SearchMode,
) -> Option<SortedMap<RequiredEntry, CriteriaSet>> {
    // Collect the list of third-party packages with the given name, along with their requirements.
    let no_criteria = criteria_mapper.no_criteria();
    let packages: Vec<_> = package_graph
        .resolve_package_name(package_name)
        .packages(DependencyDirection::Forward)
        .filter(|package| package.is_third_party(&store.config.policy))
        .map(|package| {
            (
                package,
                requirements.get(package.id()).unwrap_or(&no_criteria),
            )
        })
        .collect();

    // If there are no third-party packages with the name, we definitely don't need any entries.
    if packages.is_empty() {
        return Some(SortedMap::new());
    }

    let Ok(audit_graph) = AuditGraph::build(store, criteria_mapper, package_name, None) else {
        // There were violations when building the audit graph, return `None` to
        // indicate that this package is failing.
        return None;
    };

    let mut required_entries = SortedMap::new();
    for &(package, reqs) in &packages {
        let version = package.vet_version();
        // Do the minimal set of searches to validate that the required criteria
        // are matched.
        for criteria_idx in criteria_mapper.minimal_indices(reqs) {
            let Ok(path) = audit_graph.search(criteria_idx, &version, search_mode) else {
                // This package failed to vet, return `None`.
                return None;
            };

            let mut add_entry = |entry: RequiredEntry| {
                required_entries
                    .entry(entry)
                    .or_insert_with(|| criteria_mapper.no_criteria())
                    .set_criteria(criteria_idx);
            };

            for origin in path {
                match origin {
                    DeltaEdgeOrigin::Exemption { exemption_index } => {
                        add_entry(RequiredEntry::Exemption { exemption_index });
                    }
                    DeltaEdgeOrigin::FreshExemption { version } => {
                        add_entry(RequiredEntry::FreshExemption { version });
                    }
                    DeltaEdgeOrigin::ImportedAudit {
                        import_index,
                        audit_index,
                    } => {
                        add_entry(RequiredEntry::Audit {
                            import_index,
                            audit_index,
                        });
                    }
                    DeltaEdgeOrigin::WildcardAudit {
                        import_index,
                        audit_index,
                        publisher_index,
                    } => {
                        if let Some(import_index) = import_index {
                            add_entry(RequiredEntry::WildcardAudit {
                                import_index,
                                audit_index,
                            })
                        }
                        add_entry(RequiredEntry::Publisher { publisher_index })
                    }
                    DeltaEdgeOrigin::Trusted { publisher_index } => {
                        add_entry(RequiredEntry::Publisher { publisher_index })
                    }
                    DeltaEdgeOrigin::Unpublished { unpublished_index } => {
                        add_entry(RequiredEntry::Unpublished { unpublished_index })
                    }
                    DeltaEdgeOrigin::StoredLocalAudit { audit_index, .. } => {
                        add_entry(RequiredEntry::LocalAudit { audit_index })
                    }
                }
            }
        }
        continue;
    }

    Some(required_entries)
}

/// Per-package options to control store pruning.
#[derive(Copy, Clone)]
pub struct UpdateMode {
    pub search_mode: SearchMode,
    pub prune_exemptions: bool,
    pub prune_non_importable_audits: bool,
    pub prune_imports: bool,
}

pub(crate) struct StoreUpdates {
    pub audits: SortedMap<String, Vec<AuditEntry>>,
    pub imports: ImportsFile,
    pub exemptions: SortedMap<PackageName, Vec<ExemptedDependency>>,
}

impl StoreUpdates {
    pub fn apply(self, store: &mut Store) {
        store.audits.audits = self.audits;
        store.imports = self.imports;
        store.config.exemptions = self.exemptions;
    }
}

/// Refresh the state of the store, importing required audits, and optionally
/// pruning unnecessary exemptions, audits, and/or imports.
pub fn update_store(
    cfg: &Config,
    store: &mut Store,
    mode: impl FnMut(PackageStr<'_>) -> UpdateMode,
) {
    get_store_updates(cfg, store, mode).apply(store);
}

/// Helper function to determine if we should be pruning imports.
///
/// We always prune if requested, but will also prune imports if a new audit or
/// publisher entry is being added for the crate.
fn should_prune_imports(
    store: &Store,
    required_entries: &Option<SortedMap<RequiredEntry, CriteriaSet>>,
    mode: UpdateMode,
    pkgname: PackageStr<'_>,
) -> bool {
    if mode.prune_imports {
        true
    } else if let Some(required_entries) = required_entries {
        let import = |idx| store.imported_audits().values().nth(idx).unwrap();
        required_entries.keys().any(|entry| match entry {
            RequiredEntry::Audit {
                import_index,
                audit_index,
            } => import(*import_index).audits[pkgname][*audit_index].is_fresh_import,
            RequiredEntry::WildcardAudit {
                import_index,
                audit_index,
            } => import(*import_index).wildcard_audits[pkgname][*audit_index].is_fresh_import,
            RequiredEntry::Publisher { publisher_index } => {
                store.publishers()[pkgname][*publisher_index].is_fresh_import
            }
            _ => false,
        })
    } else {
        false
    }
}

/// The non-mutating core of `update_store` for use in non-mutating situations.
pub(crate) fn get_store_updates(
    cfg: &Config,
    store: &Store,
    mut mode: impl FnMut(PackageStr<'_>) -> UpdateMode,
) -> StoreUpdates {
    // Compute the set of required entries from the store for all packages in
    // the dependency graph.
    let criteria_mapper = CriteriaMapper::new(&store.audits.criteria);

    // FIXME: The CargoResolverVersion should be based on the edition & version
    // in Cargo.toml!
    let requirements = resolve_requirements(
        &cfg.package_graph,
        &store.config,
        &criteria_mapper,
        cfg.resolver_version,
    );

    let mut required_entries = SortedMap::new();
    for package in cfg.package_graph.packages() {
        required_entries.entry(package.name()).or_insert_with(|| {
            resolve_package_required_entries(
                &cfg.package_graph,
                &criteria_mapper,
                &requirements,
                store,
                package.name(),
                mode(package.name()).search_mode,
            )
        });
    }

    // Remove unused non-importable audits.
    let mut new_audits = store.audits.audits.clone();
    for (pkg, entries) in &required_entries {
        if !mode(pkg).prune_non_importable_audits {
            continue;
        }
        let Some(entries) = entries else { continue };

        if let Some(audit_entries) = new_audits.get_mut(*pkg) {
            *audit_entries = std::mem::take(audit_entries)
                .into_iter()
                .enumerate()
                .filter(|&(audit_index, ref entry)| {
                    // Keep the entry if it's importable (i.e. it could be used externally) or it's
                    // used locally.
                    entry.importable
                        || entries.contains_key(&RequiredEntry::LocalAudit { audit_index })
                })
                .map(|(_, entry)| entry)
                .collect();
        }
    }

    // Dummy value to use if a package isn't found in `required_entries` - no
    // edges will be required.
    let no_required_entries = Some(SortedMap::new());

    let mut new_imports = ImportsFile {
        unpublished: SortedMap::new(),
        publisher: SortedMap::new(),
        audits: SortedMap::new(),
    };

    // Determine which live imports to keep in the imports.lock file.
    for (import_index, (import_name, live_audits_file)) in
        store.imported_audits().iter().enumerate()
    {
        let new_audits_file = AuditsFile {
            criteria: live_audits_file.criteria.clone(),

            wildcard_audits: live_audits_file
                .wildcard_audits
                .iter()
                .map(|(pkgname, wildcard_audits)| {
                    let required_entries = required_entries
                        .get(&pkgname[..])
                        .unwrap_or(&no_required_entries);
                    let prune_imports =
                        should_prune_imports(store, required_entries, mode(&pkgname[..]), pkgname);
                    (
                        pkgname,
                        wildcard_audits
                            .iter()
                            .enumerate()
                            .filter(|&(audit_index, entry)| {
                                // Keep existing if we're not pruning imports.
                                if !prune_imports && !entry.is_fresh_import {
                                    return true;
                                }

                                if let Some(required_entries) = required_entries {
                                    required_entries.contains_key(&RequiredEntry::WildcardAudit {
                                        import_index,
                                        audit_index,
                                    })
                                } else {
                                    !entry.is_fresh_import
                                }
                            })
                            .map(|(_, entry)| WildcardEntry {
                                is_fresh_import: false,
                                ..entry.clone()
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .filter(|(_, l)| !l.is_empty())
                .map(|(n, mut l)| {
                    l.sort();
                    (n.clone(), l)
                })
                .collect(),

            audits: live_audits_file
                .audits
                .iter()
                .map(|(pkgname, audits)| {
                    let (uses_package, required_entries) = match required_entries.get(&pkgname[..])
                    {
                        Some(e) => (true, e),
                        None => (false, &no_required_entries),
                    };
                    let prune_imports =
                        should_prune_imports(store, required_entries, mode(&pkgname[..]), pkgname);
                    (
                        pkgname,
                        audits
                            .iter()
                            .enumerate()
                            .filter(|&(audit_index, entry)| {
                                // Keep existing if we're not pruning imports.
                                if !prune_imports && !entry.is_fresh_import {
                                    return true;
                                }

                                // Keep violations if the package is used in the graph.
                                if matches!(entry.kind, AuditKind::Violation { .. }) {
                                    return uses_package;
                                }

                                if let Some(required_entries) = required_entries {
                                    required_entries.contains_key(&RequiredEntry::Audit {
                                        import_index,
                                        audit_index,
                                    })
                                } else {
                                    !entry.is_fresh_import
                                }
                            })
                            .map(|(_, entry)| AuditEntry {
                                is_fresh_import: false,
                                ..entry.clone()
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .filter(|(_, l)| !l.is_empty())
                .map(|(n, mut l)| {
                    l.sort();
                    (n.clone(), l)
                })
                .collect(),

            // We never import trusted entries in imports.lock.
            trusted: SortedMap::new(),
        };
        new_imports
            .audits
            .insert(import_name.clone(), new_audits_file);
    }

    // Determine which live publisher information to keep in the imports.lock file.
    for (pkgname, publishers) in store.publishers() {
        let required_entries = required_entries
            .get(&pkgname[..])
            .unwrap_or(&no_required_entries);
        let prune_imports =
            should_prune_imports(store, required_entries, mode(&pkgname[..]), pkgname);
        let mut publishers: Vec<_> = publishers
            .iter()
            .enumerate()
            .filter(|&(publisher_index, entry)| {
                // Keep existing if we're not pruning imports.
                if !prune_imports && !entry.is_fresh_import {
                    return true;
                }

                if let Some(required_entries) = required_entries {
                    required_entries.contains_key(&RequiredEntry::Publisher { publisher_index })
                } else {
                    !entry.is_fresh_import
                }
            })
            .map(|(_, entry)| CratesPublisher {
                is_fresh_import: false,
                ..entry.clone()
            })
            .collect();
        publishers.sort();
        if !publishers.is_empty() {
            new_imports.publisher.insert(pkgname.clone(), publishers);
        }
    }

    // Determine which live publisher information to keep in the imports.lock file.
    for (pkgname, unpublished) in store.unpublished() {
        // Although `unpublished` entries are stored in imports.lock, they're
        // more like automatically-managed delta-exemptions than imports, so
        // we'll prune them when pruning exemptions.
        let prune_exemptions = mode(&pkgname[..]).prune_exemptions;
        let required_entries = required_entries
            .get(&pkgname[..])
            .unwrap_or(&no_required_entries);
        let mut unpublished: Vec<_> = unpublished
            .iter()
            .enumerate()
            .filter(|&(unpublished_index, entry)| {
                // Keep existing if we're not pruning exemptions.
                if !prune_exemptions && !entry.is_fresh_import {
                    return true;
                }

                if let Some(required_entries) = required_entries {
                    required_entries.contains_key(&RequiredEntry::Unpublished { unpublished_index })
                } else {
                    !entry.is_fresh_import
                }
            })
            .map(|(_, entry)| UnpublishedEntry {
                is_fresh_import: false,
                ..entry.clone()
            })
            .collect();
        unpublished.sort();
        // Clean up any duplicate Unpublished entries now that `is_fresh_import`
        // has been cleared.  This ensures that even if we end up using
        // `PreferFreshImports` when not pruning exemptions, we won't end up
        // with duplicate unpublished entries.
        unpublished.dedup();
        if !unpublished.is_empty() {
            new_imports.unpublished.insert(pkgname.clone(), unpublished);
        }
    }

    let mut all_new_exemptions = SortedMap::new();

    // Enumerate existing exemptions to check for criteria changes.
    for (pkgname, exemptions) in &store.config.exemptions {
        let prune_exemptions = mode(pkgname).prune_exemptions;
        let required_entries = required_entries
            .get(&pkgname[..])
            .unwrap_or(&no_required_entries);

        let mut new_exemptions = Vec::with_capacity(exemptions.len());
        for (exemption_index, entry) in exemptions.iter().enumerate() {
            let original_criteria = criteria_mapper.criteria_from_list(&entry.criteria);

            // Determine the set of useful criteria from required_entries,
            // falling back to `original_criteria` if it failed to audit.
            let mut useful_criteria = if let Some(required_entries) = required_entries {
                required_entries
                    .get(&RequiredEntry::Exemption { exemption_index })
                    .cloned()
                    .unwrap_or_else(|| criteria_mapper.no_criteria())
            } else {
                original_criteria.clone()
            };

            // If we're not pruning exemptions, maintain all existing criteria.
            if !prune_exemptions {
                useful_criteria.unioned_with(&original_criteria);
            }
            if useful_criteria.is_empty() {
                continue; // Skip this exemption
            }

            // If we're expanding the criteria set and are `suggest = false`, we
            // can't update the existing entry, so try adding a new one, and
            // reset the existing node to the original criteria.
            // XXX: The behaviour around suggest here is a bit jank, we might
            // want to change it.
            if !entry.suggest && !original_criteria.contains(&useful_criteria) {
                let mut extra_criteria = useful_criteria.clone();
                extra_criteria.clear_criteria(&original_criteria);
                new_exemptions.push(ExemptedDependency {
                    version: entry.version.clone(),
                    criteria: criteria_mapper
                        .criteria_names(&extra_criteria)
                        .map(|n| n.to_owned().into())
                        .collect(),
                    suggest: true,
                    notes: None,
                });
                useful_criteria = original_criteria;
            }

            // Add the exemption with the determined minimal useful criteria.
            new_exemptions.push(ExemptedDependency {
                version: entry.version.clone(),
                criteria: criteria_mapper
                    .criteria_names(&useful_criteria)
                    .map(|n| n.to_owned().into())
                    .collect(),
                suggest: entry.suggest,
                notes: entry.notes.clone(),
            });
        }
        if !new_exemptions.is_empty() {
            all_new_exemptions.insert(pkgname.clone(), new_exemptions);
        }
    }

    // Check if we have any FreshExemption entries which should be converted
    // into new exemptions.
    for (&pkgname, required_entries) in &required_entries {
        let Some(required_entries) = required_entries else {
            continue;
        };

        for (entry, criteria) in required_entries.iter().rev() {
            let RequiredEntry::FreshExemption { version } = entry else {
                // FreshExemption entries always sort last in the BTreeMap, so
                // we can rely on there being no more FreshExemption entries
                // after we've seen one.
                break;
            };

            all_new_exemptions
                .entry(pkgname.to_owned())
                .or_default()
                .push(ExemptedDependency {
                    version: version.clone(),
                    criteria: criteria_mapper
                        .criteria_names(criteria)
                        .map(|n| n.to_owned().into())
                        .collect(),
                    suggest: true,
                    notes: None,
                });
        }
    }

    for exemptions in all_new_exemptions.values_mut() {
        exemptions.sort();
    }

    StoreUpdates {
        audits: new_audits,
        imports: new_imports,
        exemptions: all_new_exemptions,
    }
}
