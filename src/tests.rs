use crate::entities::Pair;
use once_cell::sync::Lazy;
use uniswap_sdk_core::{prelude::*, token};

pub(crate) static ETHER: Lazy<Ether> = Lazy::new(|| Ether::on_chain(1));
pub(crate) static TOKEN0: Lazy<Token> = Lazy::new(|| {
    token!(
        1,
        "0000000000000000000000000000000000000001",
        18,
        "t0",
        "token0"
    )
});
pub(crate) static TOKEN1: Lazy<Token> = Lazy::new(|| {
    token!(
        1,
        "0000000000000000000000000000000000000002",
        18,
        "t1",
        "token1"
    )
});
pub(crate) static TOKEN2: Lazy<Token> = Lazy::new(|| {
    token!(
        1,
        "0000000000000000000000000000000000000003",
        18,
        "t2",
        "token2"
    )
});
pub(crate) static TOKEN3: Lazy<Token> = Lazy::new(|| {
    token!(
        1,
        "0000000000000000000000000000000000000004",
        18,
        "t3",
        "token3"
    )
});
pub(crate) static WETH: Lazy<Token> = Lazy::new(|| ETHER.wrapped().clone());
pub(crate) static DAI: Lazy<Token> = Lazy::new(|| {
    token!(
        1,
        "6B175474E89094C44Da98b954EedeAC495271d0F",
        18,
        "DAI",
        "DAI Stablecoin"
    )
});

pub(crate) static PAIR_0_1: Lazy<Pair> = Lazy::new(|| {
    Pair::new(
        CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
        CurrencyAmount::from_raw_amount(TOKEN1.clone(), 1000).unwrap(),
    )
    .unwrap()
});
pub(crate) static PAIR_WETH_0: Lazy<Pair> = Lazy::new(|| {
    Pair::new(
        CurrencyAmount::from_raw_amount(WETH.clone(), 1000).unwrap(),
        CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
    )
    .unwrap()
});
