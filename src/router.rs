//! # Router
//! Represents the Uniswap V2 Router, and has static methods for helping execute trades.

use crate::prelude::{Error, *};
use alloy_primitives::{Bytes, U256};
use alloy_sol_types::{sol, SolCall};
use uniswap_sdk_core::prelude::*;

/// Options for producing the arguments to send call to the router.
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct TradeOptions {
    /// How much the execution price is allowed to move unfavorably from the trade execution price.
    pub allowed_slippage: Percent,
    /// When the transaction expires.
    pub deadline: U256,
    /// The account that should receive the output of the swap.
    pub recipient: Address,
    /// Whether any of the tokens in the path are fee on transfer tokens, which should be handled
    /// with special methods
    pub fee_on_transfer: Option<bool>,
}

/// Generated method parameters for executing a call.
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct MethodParameters {
    /// The encoded calldata to perform the given operation
    pub calldata: Bytes,
    /// The amount of ether (wei) to send.
    pub value: U256,
}

/// Produces the on-chain method name to call and the hex encoded parameters to pass as arguments
/// for a given trade.
///
/// ## Arguments
///
/// * `trade`: The trade to produce call parameters for
/// * `options`: The options for the call parameters
#[inline]
pub fn swap_call_parameters<TInput: BaseCurrency, TOutput: BaseCurrency>(
    trade: &Trade<TInput, TOutput>,
    options: TradeOptions,
) -> Result<MethodParameters, Error> {
    let ether_in = trade.input_amount.currency.is_native();
    let ether_out = trade.output_amount.currency.is_native();
    // the router does not support both ether in and out
    assert!(!(ether_in && ether_out), "ETHER_IN_OUT");

    let deadline = options.deadline;
    let to = options.recipient;
    let amount_in: U256 = U256::from_big_int(
        trade
            .maximum_amount_in(options.allowed_slippage.clone())?
            .quotient(),
    );
    let amount_out: U256 = U256::from_big_int(
        trade
            .minimum_amount_out(options.allowed_slippage)?
            .quotient(),
    );
    let path: Vec<Address> = trade
        .route
        .path()
        .iter()
        .map(|token| token.address)
        .collect();

    let use_fee_on_transfer = options.fee_on_transfer.unwrap_or_default();

    let (calldata, value) = match trade.trade_type {
        TradeType::ExactInput => {
            if ether_in {
                let calldata = if use_fee_on_transfer {
                    swapExactETHForTokensSupportingFeeOnTransferTokensCall {
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                } else {
                    swapExactETHForTokensCall {
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                };
                (calldata, amount_in)
            } else if ether_out {
                let calldata = if use_fee_on_transfer {
                    swapExactTokensForETHSupportingFeeOnTransferTokensCall {
                        amountIn: amount_in,
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                } else {
                    swapExactTokensForETHCall {
                        amountIn: amount_in,
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                };
                (calldata, U256::ZERO)
            } else {
                let calldata = if use_fee_on_transfer {
                    swapExactTokensForTokensSupportingFeeOnTransferTokensCall {
                        amountIn: amount_in,
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                } else {
                    swapExactTokensForTokensCall {
                        amountIn: amount_in,
                        amountOutMin: amount_out,
                        path,
                        to,
                        deadline,
                    }
                    .abi_encode()
                };
                (calldata, U256::ZERO)
            }
        }
        TradeType::ExactOutput => {
            assert!(!use_fee_on_transfer, "EXACT_OUT_FOT");
            if ether_in {
                let calldata = swapETHForExactTokensCall {
                    amountOut: amount_out,
                    path,
                    to,
                    deadline,
                }
                .abi_encode();
                (calldata, amount_in)
            } else if ether_out {
                let calldata = swapTokensForExactETHCall {
                    amountOut: amount_out,
                    amountInMax: amount_in,
                    path,
                    to,
                    deadline,
                }
                .abi_encode();
                (calldata, U256::ZERO)
            } else {
                let calldata = swapTokensForExactTokensCall {
                    amountOut: amount_out,
                    amountInMax: amount_in,
                    path,
                    to,
                    deadline,
                }
                .abi_encode();
                (calldata, U256::ZERO)
            }
        }
    };
    Ok(MethodParameters {
        calldata: calldata.into(),
        value,
    })
}

sol! {
    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;
    use alloy_primitives::{address, hex, uint};

    static TRADE_OPTIONS: Lazy<TradeOptions> = Lazy::new(|| TradeOptions {
        allowed_slippage: Percent::new(1, 100),
        deadline: uint!(50_U256),
        recipient: address!("0000000000000000000000000000000000000004"),
        fee_on_transfer: None,
    });
    static TRADE_OPTIONS_FOT: Lazy<TradeOptions> = Lazy::new(|| TradeOptions {
        fee_on_transfer: Some(true),
        ..TRADE_OPTIONS.clone()
    });

    mod exact_in {
        use super::*;

        #[test]
        fn ether_to_token1() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_in(
                    Route::new(
                        vec![PAIR_WETH_0.clone(), PAIR_0_1.clone()],
                        ETHER.clone(),
                        TOKEN1.clone(),
                    ),
                    CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("7ff36ab500000000000000000000000000000000000000000000000000000000000000510000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000320000000000000000000000000000000000000000000000000000000000000003000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
            assert_eq!(value, uint!(100_U256));
        }

        #[test]
        fn token1_to_ether() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_in(
                    Route::new(
                        vec![PAIR_0_1.clone(), PAIR_WETH_0.clone()],
                        TOKEN1.clone(),
                        ETHER.clone(),
                    ),
                    CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("18cbafe50000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000005100000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"));
            assert_eq!(value, U256::ZERO);
        }

        #[test]
        fn token0_to_token1() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_in(
                    Route::new(vec![PAIR_0_1.clone()], TOKEN0.clone(), TOKEN1.clone()),
                    CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("38ed17390000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000005900000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
            assert_eq!(value, U256::ZERO);
        }
    }

    mod exact_out {
        use super::*;

        #[test]
        fn ether_to_token1() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_out(
                    Route::new(
                        vec![PAIR_WETH_0.clone(), PAIR_0_1.clone()],
                        ETHER.clone(),
                        TOKEN1.clone(),
                    ),
                    CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("fb3bdb4100000000000000000000000000000000000000000000000000000000000000640000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000320000000000000000000000000000000000000000000000000000000000000003000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
            assert_eq!(value, uint!(128_U256));
        }

        #[test]
        fn token1_to_ether() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_out(
                    Route::new(
                        vec![PAIR_0_1.clone(), PAIR_WETH_0.clone()],
                        TOKEN1.clone(),
                        ETHER.clone(),
                    ),
                    CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("4a25d94a0000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"));
            assert_eq!(value, U256::ZERO);
        }

        #[test]
        fn token0_to_token1() {
            let MethodParameters { calldata, value } = swap_call_parameters(
                &Trade::exact_out(
                    Route::new(vec![PAIR_0_1.clone()], TOKEN0.clone(), TOKEN1.clone()),
                    CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                )
                .unwrap(),
                TRADE_OPTIONS.clone(),
            )
            .unwrap();
            assert_eq!(calldata.to_vec(), hex!("8803dbee0000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000007100000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
            assert_eq!(value, U256::ZERO);
        }
    }

    mod fee_on_transfer {
        use super::*;

        mod exact_in {
            use super::*;

            #[test]
            fn ether_to_token1() {
                let MethodParameters { calldata, value } = swap_call_parameters(
                    &Trade::exact_in(
                        Route::new(
                            vec![PAIR_WETH_0.clone(), PAIR_0_1.clone()],
                            ETHER.clone(),
                            TOKEN1.clone(),
                        ),
                        CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
                assert_eq!(calldata.to_vec(), hex!("b6f9de9500000000000000000000000000000000000000000000000000000000000000510000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000320000000000000000000000000000000000000000000000000000000000000003000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
                assert_eq!(value, uint!(100_U256));
            }

            #[test]
            fn token1_to_ether() {
                let MethodParameters { calldata, value } = swap_call_parameters(
                    &Trade::exact_in(
                        Route::new(
                            vec![PAIR_0_1.clone(), PAIR_WETH_0.clone()],
                            TOKEN1.clone(),
                            ETHER.clone(),
                        ),
                        CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
                assert_eq!(calldata.to_vec(), hex!("791ac9470000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000005100000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"));
                assert_eq!(value, U256::ZERO);
            }

            #[test]
            fn token0_to_token1() {
                let MethodParameters { calldata, value } = swap_call_parameters(
                    &Trade::exact_in(
                        Route::new(vec![PAIR_0_1.clone()], TOKEN0.clone(), TOKEN1.clone()),
                        CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
                assert_eq!(calldata.to_vec(), hex!("5c11d7950000000000000000000000000000000000000000000000000000000000000064000000000000000000000000000000000000000000000000000000000000005900000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"));
                assert_eq!(value, U256::ZERO);
            }
        }

        mod exact_out {
            use super::*;

            #[test]
            #[should_panic(expected = "EXACT_OUT_FOT")]
            fn ether_to_token1() {
                swap_call_parameters(
                    &Trade::exact_out(
                        Route::new(
                            vec![PAIR_WETH_0.clone(), PAIR_0_1.clone()],
                            ETHER.clone(),
                            TOKEN1.clone(),
                        ),
                        CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
            }

            #[test]
            #[should_panic(expected = "EXACT_OUT_FOT")]
            fn token1_to_ether() {
                swap_call_parameters(
                    &Trade::exact_out(
                        Route::new(
                            vec![PAIR_0_1.clone(), PAIR_WETH_0.clone()],
                            TOKEN1.clone(),
                            ETHER.clone(),
                        ),
                        CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
            }

            #[test]
            #[should_panic(expected = "EXACT_OUT_FOT")]
            fn token0_to_token1() {
                swap_call_parameters(
                    &Trade::exact_out(
                        Route::new(vec![PAIR_0_1.clone()], TOKEN0.clone(), TOKEN1.clone()),
                        CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                    )
                    .unwrap(),
                    TRADE_OPTIONS_FOT.clone(),
                )
                .unwrap();
            }
        }
    }
}
