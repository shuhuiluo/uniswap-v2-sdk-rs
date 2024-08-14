# Uniswap V2 SDK Rust

[![Unit Tests](https://github.com/shuhuiluo/uniswap-v2-sdk-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/shuhuiluo/uniswap-v2-sdk-rs/actions/workflows/rust.yml)
[![crates.io](https://img.shields.io/crates/v/uniswap-v2-sdk.svg)](https://crates.io/crates/uniswap-v2-sdk)

A Rust SDK for building applications on top of Uniswap V3. Migration from the
TypeScript [Uniswap/v3-sdk](https://github.com/Uniswap/v3-sdk).

WIP.

## Features

- Opinionated Rust implementation of the Uniswap V2 SDK with a focus on readability and performance
- Usage of [alloy-rs](https://github.com/alloy-rs) types
- Extensive unit tests and benchmarks


## Getting started

Add the following to your `Cargo.toml` file:

```toml
uniswap-v2-sdk = "0.2.0"
```

### Usage

The package structure follows that of the TypeScript SDK, but with `snake_case` instead of `camelCase`.

For easy import, use the prelude:

```rust
use uniswap_v2_sdk;
```

## Contributing

Contributions are welcome. Please open an issue if you have any questions or suggestions.

### Testing

Tests are run with `cargo test`. To test a specific module, use `cargo test --test <module_name>`.

### Linting

Linting is done with `clippy` and `rustfmt`. To run the linter,
use `cargo clippy --all-targets --all-features -- -D warnings` and `cargo fmt --all -- --check`.

### Benchmarking

Benchmarking is done with `criterion`. To run the benchmarks, use `cargo bench`.

## License

This project is licensed under the [MIT License](LICENSE).

## Acknowledgements

This project is inspired by and adapted from the following projects:

- [Uniswap V2 SDK](https://github.com/Uniswap/v2-sdk)

