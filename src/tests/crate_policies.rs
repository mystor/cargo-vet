use crate::errors::CratePolicyErrors;

use super::*;

struct CratePolicyTest(pub MockMetadata);

impl CratePolicyTest {
    pub fn no_errors<F>(&self, alter_config: F)
    where
        F: FnOnce(&mut ConfigFile),
    {
        self.check_crate_policies(alter_config)
            .expect("crate policy check should succeed");
    }

    pub fn insta_crate_policy_errors<N: AsRef<str>, F>(&self, name: N, alter_config: F)
    where
        F: FnOnce(&mut ConfigFile),
    {
        let e = self
            .check_crate_policies(alter_config)
            .expect_err("crate policy check should have failed");
        insta::assert_snapshot!(name.as_ref(), format!("{:?}", miette::Report::new(e)));
    }

    fn check_crate_policies<F>(&self, alter_config: F) -> Result<(), CratePolicyErrors>
    where
        F: FnOnce(&mut ConfigFile),
    {
        let metadata = self.0.metadata();
        let (mut config, audits, imports) = builtin_files_full_audited(&metadata);
        alter_config(&mut config);
        let store = Store::mock(config, audits, imports);
        let cfg = mock_cfg(&metadata);

        crate::check_crate_policies(&cfg, &store)
    }
}

/// Checks that if a third-party crate is present, and an unversioned policy is used _without_
/// `dependency-criteria`, no error occurs.
#[test]
fn simple_crate_policies_third_party_crates_dont_need_versions() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::overlapping()).no_errors(|config| {
        config.policy.insert(
            "third-party".into(),
            PackagePolicyEntry::Unversioned(Default::default()),
        );
    });
}

fn dep_criteria_policy_entry() -> PolicyEntry {
    PolicyEntry {
        dependency_criteria: [("foo".to_owned().into(), vec!["bar".to_owned().into()])].into(),
        ..Default::default()
    }
}

/// Checks that if a third-party crate is present, and an unversioned policy is used with
/// `dependency-criteria`, an error occurs indicating that versions need to be specified.
#[test]
fn simple_crate_policies_third_party_crates_imply_versions() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::overlapping()).insta_crate_policy_errors(
        "third_party_crates_imply_versions",
        |config| {
            config.policy.insert(
                "third-party".into(),
                PackagePolicyEntry::Unversioned(dep_criteria_policy_entry()),
            );
        },
    );
}

/// Checks that if a third-party crate is present and a versioned policy with `dependency-criteria`
/// is used for one version, an error occurs indicating that versions are needed for other versions
/// (regardless of whether they are considered first- or third-party).
#[test]
fn simple_crate_policies_third_party_crates_need_all_versions() {
    let _enter = TEST_RUNTIME.enter();

    let test = CratePolicyTest(MockMetadata::overlapping());

    for which in [1, 2] {
        test.insta_crate_policy_errors(
            format!("third_party_crates_need_all_versions_{which}"),
            |config| {
                config.policy.insert(
                    "third-party".into(),
                    PackagePolicyEntry::Versioned {
                        version: [(ver(which), dep_criteria_policy_entry())].into(),
                    },
                );
            },
        );
    }
}

/// If crate policies are provided for versions which aren't present in the graph, an error should
/// occur.
#[test]
fn simple_crate_policies_extraneous_crate_versions() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::overlapping()).insta_crate_policy_errors(
        "extraneous_crate_versions",
        |config| {
            config.policy.insert(
                "third-party".into(),
                PackagePolicyEntry::Versioned {
                    version: [
                        (ver(1), Default::default()),
                        (ver(2), Default::default()),
                        (ver(3), Default::default()),
                    ]
                    .into(),
                },
            );
        },
    );
}

/// If crate policies are provided for crates which aren't present in the graph, an error should
/// occur.
#[test]
fn simple_crate_policies_extraneous_crates() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::overlapping()).insta_crate_policy_errors(
        "extraneous_crates",
        |config| {
            config.policy.insert(
                "non-existent".into(),
                PackagePolicyEntry::Unversioned(Default::default()),
            );
        },
    );
}

#[test]
fn features_non_workspace_excluded() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::new(vec![
        MockPackage {
            name: "root",
            is_workspace: true,
            is_first_party: true,
            deps: vec![MockDependency {
                name: "third-party",
                ..Default::default()
            }],
            ..Default::default()
        },
        MockPackage {
            name: "third-party",
            features: BTreeMap::from([("unknown-feature", vec![])]),
            ..Default::default()
        },
    ]))
    .insta_crate_policy_errors("features-non-workspace-excluded", |config| {
        config.policy.insert(
            "third-party".into(),
            PackagePolicyEntry::Unversioned(PolicyEntry {
                dev_features: vec!["unknown-feature".to_string()],
                ..Default::default()
            }),
        );
    });
}

#[test]
fn features_excluded_unknown() {
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::new(vec![MockPackage {
        name: "root",
        is_workspace: true,
        is_first_party: true,
        features: BTreeMap::from([("known-feature", vec![])]),
        ..Default::default()
    }]))
    .insta_crate_policy_errors("features-excluded-unknown", |config| {
        config.policy.insert(
            "root".into(),
            PackagePolicyEntry::Unversioned(PolicyEntry {
                dev_features: vec!["known-feature".to_string(), "unknown-feature".to_string()],
                ..Default::default()
            }),
        );
    });
}

#[test]
fn features_excluded_implied_fail() {
    // FAIL: Errors because the implicit `third-party` feature is implied by the
    // non-excluded `feat` feature.
    let _enter = TEST_RUNTIME.enter();

    CratePolicyTest(MockMetadata::new(vec![
        MockPackage {
            name: "root",
            is_workspace: true,
            is_first_party: true,
            features: BTreeMap::from([("feat", vec!["third-party"]), ("feat2", vec!["feat"])]),
            deps: vec![MockDependency {
                name: "third-party",
                optional: true,
                ..Default::default()
            }],
            ..Default::default()
        },
        MockPackage {
            name: "third-party",
            ..Default::default()
        },
    ]))
    .insta_crate_policy_errors("features-excluded-implied-fail", |config| {
        config.policy.insert(
            "root".into(),
            PackagePolicyEntry::Unversioned(PolicyEntry {
                dev_features: vec!["third-party".to_string()],
                ..Default::default()
            }),
        );
    });
}
