# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- Added `ProgramBuilder`
- Added matrix room to `README.md`
- Added Travis builds for all operating systems

### Changed
- Made all fields in `Program` private
- Changed field `target_version` in `Program` to type `semver::Version`
- Moved test debugger to `examples` directory

### Fixed
- Fixed a bug in the example debugger, where on normal exit the exit code was 1


[Unreleased]: https://github.com/bakervm/melon/compare/v0.13.1...HEAD
