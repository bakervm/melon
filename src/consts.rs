use lazy_static::lazy_static;
use semver::{Version, VersionReq};

lazy_static! {
    /// The current version of the melon crate
    pub static ref VERSION: Version = env!("CARGO_PKG_VERSION").parse().unwrap();
    pub static ref VERSION_REQ: VersionReq = {
        let mut version_string: String = vec![VERSION.major.to_string(), VERSION.minor.to_string()].join(".");

        version_string.insert(0, '^');

        VersionReq::parse(&version_string).expect("unable to parse version requirement")
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requirement_matches() {
        assert!(VERSION_REQ.matches(&VERSION));
    }
}
