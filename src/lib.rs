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
    clippy::redundant_clone,
    rustdoc::all
)]
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![deny(unused_must_use, rust_2018_idioms)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

extern crate alloc;

pub mod constants;
pub mod entities;
pub mod error;

pub mod prelude {
    pub use crate::{constants::*, entities::*, error::*};
    pub use alloc::vec;
}
