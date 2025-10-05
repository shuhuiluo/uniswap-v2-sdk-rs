use alloy_primitives::{b256, Address, B256};
use once_cell::sync::Lazy;
use uniswap_sdk_core::prelude::{
    fastnum::i512, BigInt, HashMap, IsPercent, Percent, V2_FACTORY_ADDRESS, V2_FACTORY_ADDRESSES,
};

pub const FACTORY_ADDRESS: Address = V2_FACTORY_ADDRESS;

pub static FACTORY_ADDRESS_MAP: Lazy<HashMap<u64, Address>> =
    Lazy::new(|| V2_FACTORY_ADDRESSES.clone());

pub const INIT_CODE_HASH: B256 =
    b256!("96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f");

pub const MINIMUM_LIQUIDITY: BigInt = i512!(1000);

// exports for internal consumption
pub(crate) const FIVE: BigInt = i512!(5);
pub(crate) const _997: BigInt = i512!(997);
pub(crate) const _1000: BigInt = i512!(1000);
pub(crate) const BASIS_POINTS: BigInt = i512!(10000);

pub(crate) const ZERO_PERCENT: Percent = Percent {
    numerator: BigInt::ZERO,
    denominator: BigInt::ONE,
    meta: IsPercent,
};

pub(crate) const ONE_HUNDRED_PERCENT: Percent = Percent {
    numerator: BigInt::ONE,
    denominator: BigInt::ONE,
    meta: IsPercent,
};
