use alloy_primitives::{address, b256, Address, B256};
use once_cell::sync::Lazy;
use rustc_hash::FxHashMap;
use uniswap_sdk_core::{
    addresses::V2_FACTORY_ADDRESSES,
    prelude::{BigInt, Percent},
};

pub const FACTORY_ADDRESS: Address = address!("5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f");

pub static FACTORY_ADDRESS_MAP: Lazy<FxHashMap<u64, Address>> =
    Lazy::new(|| V2_FACTORY_ADDRESSES.clone());

pub const INIT_CODE_HASH: B256 =
    b256!("96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f");

pub static MINIMUM_LIQUIDITY: Lazy<BigInt> = Lazy::new(|| BigInt::from(1000));

// exports for internal consumption
pub(crate) static _ZERO: Lazy<BigInt> = Lazy::new(|| BigInt::from(0));
pub(crate) static _ONE: Lazy<BigInt> = Lazy::new(|| BigInt::from(1));
pub(crate) static FIVE: Lazy<BigInt> = Lazy::new(|| BigInt::from(5));
pub(crate) static _997: Lazy<BigInt> = Lazy::new(|| BigInt::from(997));
pub(crate) static _1000: Lazy<BigInt> = Lazy::new(|| BigInt::from(1000));
pub(crate) static BASIS_POINTS: Lazy<BigInt> = Lazy::new(|| BigInt::from(10000));

pub(crate) static ZERO_PERCENT: Lazy<Percent> = Lazy::new(Percent::default);
pub(crate) static ONE_HUNDRED_PERCENT: Lazy<Percent> = Lazy::new(|| Percent::new(1, 1));
