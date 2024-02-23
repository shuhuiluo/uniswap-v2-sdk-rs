use alloy_primitives::{address, b256, uint, Address, B256, U256};
use once_cell::sync::Lazy;
use std::collections::HashMap;
use uniswap_sdk_core::{addresses::V2_FACTORY_ADDRESSES, prelude::Percent};

pub const FACTORY_ADDRESS: Address = address!("5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f");

pub static FACTORY_ADDRESS_MAP: Lazy<HashMap<u64, Address>> =
    Lazy::new(|| V2_FACTORY_ADDRESSES.clone());

pub const INIT_CODE_HASH: B256 =
    b256!("96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f");

pub const MINIMUM_LIQUIDITY: U256 = uint!(1000_U256);

// exports for internal consumption
pub(crate) const ZERO: U256 = U256::ZERO;
pub(crate) const ONE: U256 = U256::from_limbs([1, 0, 0, 0]);
pub(crate) const FIVE: U256 = U256::from_limbs([5, 0, 0, 0]);
pub(crate) const _997: U256 = U256::from_limbs([997, 0, 0, 0]);
pub(crate) const _1000: U256 = U256::from_limbs([1000, 0, 0, 0]);
pub(crate) const BASIS_POINTS: U256 = U256::from_limbs([10000, 0, 0, 0]);

pub(crate) static ZERO_PERCENT: Lazy<Percent> = Lazy::new(|| Percent::default());
pub(crate) static ONE_HUNDRED_PERCENT: Lazy<Percent> = Lazy::new(|| Percent::new(1, 1));
