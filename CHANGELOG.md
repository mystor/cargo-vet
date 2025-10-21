# Unreleased

* **BREAKING CHANGE** Re-implemented the crate graph backend with [`guppy`](https://github.com/guppy-rs/guppy).
  * Dependency resolution now reflects resolver v2 crate feature unification more accurately. A package which is built through two independent targets with different features should now reflect the actual features used by `cargo build` when propagating criteria requirements to dependencies.
  * **BREAKING CHANGE** Removed the `dump-graph` subcommand, as we now use `guppy`'s more complex build graph representation.
  * **BREAKING CHANGE** Removed the `--filter-graph` command line flag, as it no longer makes sense with `guppy`'s more complex build graph representation.
  * **BREAKING CHANGE** Removed the `--no-all-features`, `--no-default-features` and `--features` command line flags, as `guppy` requires that the cargo metadata be built with all features present.
  * **BREAKING CHANGE** Specific criteria requirements in edge cases (especially around multi-root crate graphs), has changed. This may reduce or increase the audit requirements on dependencies.
* Added support for declaring wildcard audits and trusted entries for crates published using ["Trusted Publishing"](https://crates.io/docs/trusted-publishing) (#671)
* `cargo vet check --frozen` (a disabled network) will infer the existence of crates using versions
  in audits when checking audit-as-crates-io policies (#661)

# Version 0.10.1 (2025-02-10)

* `cargo vet` will no longer prompt to renew expiring wildcard audits for inactive crates (#648)
* `cargo vet renew --expiring` will no longer renew expiring wildcard audits for inactive crates (#649)

# Version 0.10.0 (2024-10-03)

* Various improvements to the diff and inspect subcommands:
  * Added support for using [diff.rs](https://diff.rs) with the diff and inspect subcommands (#625, #633, #635)
  * The diff and inspect subcommands will remember the most recently used mode, and automatically use it next time (#633)
  * The default mode for diff and inspect was changed to diff.rs (#611, #633)

* Crates.io metadata caching was changed to avoid issues where incorrect crates.io state was being cached locally, leading to confusing results (#631)

* Unnecessary imports and publisher entries will be removed when adding importing another audit or publisher entry for the same crate (#621)
  * This is intended to reduce churn and unnecessary entries in `imports.lock` without running prune explicitly

* Network requests made by cargo vet will now respect the cargo `http.cainfo` config option (#615)

* Suggest output will now also mention criteria which implies the minimum required criteria (#614)

* Audit files being aggregated with the aggregate subcommand will now be validated before being aggregated, to avoid generating invalid aggregate audits files (#586)

* Local wildcard audits are now preferred over imported wildcard audits when determining audit paths (#588)

* Binary releases are now built in CI and [published to github](https://github.com/mozilla/cargo-vet/releases) using [`cargo dist`](https://github.com/axodotdev/cargo-dist) (#600)

