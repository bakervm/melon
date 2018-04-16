# melon
A library for creating retro computing platforms

[![Build Status][travis-image]][travis-link]
[![Crates.io][crate-image]][crate-link]
[![code coverage][codecov-image]][codecov-link]
[![Docs.rs][docs-image]][docs-link]
[![dependency status][deps-image]][deps-link]

## Introduction
`melon` is like a virtual 16bit CPU. When building a retro computing platform e.g. a gaming console or old computer architecture, `melon` takes care of handling basic parts like stack management, calls, memory management and exception handling. Its most common interface, the `System` trait makes it possible to not only implement the CPU into any platform but makes it also really easy to extend its functionality.

The `Program` struct takes care of loading and saving programs written for an implementation of the `melon` backend. `melon` roms are gzipped msgpack files.

## Debugger
`melon` comes with an interactive debugger. You can install it using cargo:
```
cargo install melon
```
After that you can debug any `melon`-compatible rom file:
```
melon-dbg target/melon.rom
```

## Get in touch
If you have any questions do not hesitate joining me on *Freenode* in `#bakervm`. I try to be online as often as possible :grin:

[deps-image]: https://deps.rs/repo/github/bakervm/melon/status.svg
[deps-link]: https://deps.rs/repo/github/bakervm/melon
[crate-image]: https://img.shields.io/crates/v/melon.svg
[crate-link]: https://crates.io/crates/melon
[travis-image]: https://travis-ci.org/bakervm/melon.svg?branch=master
[travis-link]: https://travis-ci.org/bakervm/melon
[docs-image]: https://docs.rs/melon/badge.svg
[docs-link]: https://docs.rs/melon
[codecov-image]: https://codecov.io/gh/bakervm/melon/branch/master/graph/badge.svg
[codecov-link]: https://codecov.io/gh/bakervm/melon
