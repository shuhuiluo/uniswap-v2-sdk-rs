//! # uniswap-v2-sdk
//!
//! A Rust SDK for building applications on top of Uniswap V2.
//! Migration from the TypeScript [Uniswap/v2-sdk](https://github.com/Uniswap/v2-sdk).

#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![warn(
    missing_copy_implementations,
    missing_debug_implementations,
    unreachable_pub,
    clippy::missing_const_for_fn,
    clippy::missing_inline_in_public_items,
    clippy::needless_pass_by_value,
    clippy::redundant_clone,
    clippy::explicit_iter_loop,
    clippy::manual_assert,
    clippy::must_use_candidate,
    clippy::semicolon_if_nothing_returned,
    clippy::suspicious_operation_groupings,
    clippy::unseparated_literal_suffix,
    clippy::unused_self,
    clippy::use_debug,
    rustdoc::all
)]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![deny(unused_must_use, rust_2018_idioms)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

extern crate alloc;

pub mod constants;
pub mod entities;
pub mod error;
pub mod router;

#[cfg(test)]
mod tests;

pub mod prelude {
    pub use crate::{constants::*, entities::*, error::*, router::*};

    pub use uniswap_sdk_core as sdk_core;
}
