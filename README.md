# Uniswap V2 SDK Rust

[![Rust CI](https://github.com/shuhuiluo/uniswap-v2-sdk-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/shuhuiluo/uniswap-v2-sdk-rs/actions/workflows/rust.yml)
[![crates.io](https://img.shields.io/crates/v/uniswap-v2-sdk.svg)](https://crates.io/crates/uniswap-v2-sdk)

A Rust SDK for building applications on top of Uniswap V2.
Migration from the TypeScript [Uniswap/v2-sdk](https://github.com/Uniswap/v2-sdk).

## Quickstart

Add this to your Cargo.toml

```toml
[dependencies]
uniswap-v2-sdk = "2.0"
```

And this to your code:

```rust
use uniswap_v2_sdk::prelude::*;
```

## Supported Rust Versions (MSRV)

<!--
When updating this, also update:
- clippy.toml
- Cargo.toml
- .github/workflows/rust.yml
-->

The current MSRV (minimum supported rust version) is 1.85.

## Note on `no_std`

By default, this library does not depend on the standard library (`std`). However, the `std` feature can be enabled.

## License

This project is licensed under the MIT License - see the [LICENSE](./LICENSE) file for details.
