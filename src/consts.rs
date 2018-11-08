use semver::{Version, VersionReq};

lazy_static! {
    /// The current version of the melon crate
    pub static ref VERSION: Version = env!("CARGO_PKG_VERSION").parse().unwrap();
    pub static ref VERSION_REQ: VersionReq = {
        let mut version_string: String = env!("CARGO_PKG_VERSION")
            .split('.')
            .take(2)
            .collect::<Vec<_>>()
            .join(".");

        version_string.insert(0, '^');

        VersionReq::parse(&version_string).expect("unable to parse version requirement")
    };
}
