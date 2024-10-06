#[cfg(test)]
mod tests {

    use crate::entities::{Pair, Route, Trade};
    use alloy_primitives::address;
    use once_cell::sync::Lazy;
    use uniswap_sdk_core::prelude::*;

    const CHAIN_ID: u64 = 3;

    static WETH9: Lazy<Token> = Lazy::new(|| {
        Token::new(
            CHAIN_ID,
            address!("C02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2"),
            18,
            Some("WETH".to_string()),
            Some("Wrapped Ether".to_string()),
            None,
            None,
        )
    });
    static DECIMAL_PERMUTATIONS: [[u8; 3]; 3] = [[0, 0, 0], [0, 9, 18], [18, 18, 18]];

    fn decimalize(amount: u128, decimals: u8) -> BigInt {
        BigInt::from(amount) * BigInt::from(10).pow(decimals as u32)
    }

    #[test]
    fn test_entities() {
        fn setup_tokens(decimals: &[u8; 3]) -> Vec<Token> {
            let addresses: [Address; 3] = [
                address!("0000000000000000000000000000000000000001"),
                address!("0000000000000000000000000000000000000002"),
                address!("0000000000000000000000000000000000000003"),
            ];

            addresses
                .iter()
                .enumerate()
                .map(|(i, &addr)| {
                    let adde = addr;
                    Token::new(
                        CHAIN_ID,
                        adde,
                        decimals[i],
                        Some(format!("TOKEN{}", i + 1)),
                        None,
                        None,
                        None,
                    )
                })
                .collect()
        }
        for decimals in DECIMAL_PERMUTATIONS.iter() {
            let tokens = setup_tokens(decimals);

            // Test Pair
            let pairs = vec![
                Pair::new(
                    CurrencyAmount::from_raw_amount(
                        tokens[0].clone(),
                        decimalize(1, tokens[0].decimals),
                    )
                    .unwrap(),
                    CurrencyAmount::from_raw_amount(
                        tokens[1].clone(),
                        decimalize(1, tokens[1].decimals),
                    )
                    .unwrap(),
                )
                .unwrap(),
                Pair::new(
                    CurrencyAmount::from_raw_amount(
                        tokens[1].clone(),
                        decimalize(1, tokens[1].decimals),
                    )
                    .unwrap(),
                    CurrencyAmount::from_raw_amount(
                        tokens[2].clone(),
                        decimalize(1, tokens[2].decimals),
                    )
                    .unwrap(),
                )
                .unwrap(),
                Pair::new(
                    CurrencyAmount::from_raw_amount(
                        tokens[2].clone(),
                        decimalize(1, tokens[2].decimals),
                    )
                    .unwrap(),
                    CurrencyAmount::from_raw_amount(
                        WETH9.clone(),
                        decimalize(1234, WETH9.decimals),
                    )
                    .unwrap(),
                )
                .unwrap(),
            ];

            // Test Route
            let mut route = Route::new(pairs.clone(), tokens[0].clone(), WETH9.clone());
            assert_eq!(route.pairs, pairs);
            assert_eq!(
                route.path,
                vec![
                    tokens[0].clone(),
                    tokens[1].clone(),
                    tokens[2].clone(),
                    WETH9.clone()
                ]
            );
            assert_eq!(route.input, tokens[0]);
            assert_eq!(route.output, WETH9.clone());

            // Test midPrice
            let input_amount = CurrencyAmount::from_raw_amount(
                route.input.clone(),
                decimalize(1, route.input.decimals),
            )
            .unwrap();
            let output_amount = CurrencyAmount::from_raw_amount(
                route.output.clone(),
                decimalize(1234, route.output.decimals),
            )
            .unwrap();

            assert_eq!(
                route
                    .mid_price()
                    .unwrap()
                    .quote(input_amount.clone())
                    .unwrap(),
                output_amount
            );
            assert_eq!(
                route
                    .mid_price()
                    .unwrap()
                    .invert()
                    .quote(output_amount.clone())
                    .unwrap(),
                input_amount
            );

            assert_eq!(
                route
                    .mid_price()
                    .unwrap()
                    .invert()
                    .to_significant(5, Rounding::RoundDown)
                    .unwrap(),
                "0.00081037"
            );
            assert_eq!(
                route.mid_price().unwrap().to_fixed(2, Rounding::RoundDown),
                "1234.00"
            );
            assert_eq!(
                route
                    .mid_price()
                    .unwrap()
                    .invert()
                    .to_fixed(8, Rounding::RoundDown),
                "0.00081037"
            );

            // Test Trade
            let route = Route::new(
                vec![Pair::new(
                    CurrencyAmount::from_raw_amount(
                        tokens[1].clone(),
                        decimalize(5, tokens[1].decimals),
                    )
                    .unwrap(),
                    CurrencyAmount::from_raw_amount(WETH9.clone(), decimalize(10, WETH9.decimals))
                        .unwrap(),
                )
                .unwrap()],
                tokens[1].clone(),
                WETH9.clone(),
            );

            // TradeType.EXACT_INPUT
            let input_amount = CurrencyAmount::from_raw_amount(
                tokens[1].clone(),
                decimalize(1, tokens[1].decimals),
            )
            .unwrap();
            let expected_output_amount = CurrencyAmount::from_raw_amount(
                WETH9.clone(),
                BigInt::from_str("1662497915624478906").unwrap(),
            )
            .unwrap();
            let trade =
                Trade::new(route.clone(), input_amount.clone(), TradeType::ExactInput).unwrap();

            assert_eq!(trade.route, route);
            assert_eq!(trade.trade_type, TradeType::ExactInput);
            assert_eq!(trade.input_amount, input_amount);
            assert_eq!(trade.output_amount, expected_output_amount);

            assert_eq!(
                trade
                    .execution_price
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "1.6624979156244789"
            );
            assert_eq!(
                trade
                    .execution_price
                    .invert()
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "0.601504513540621865"
            );
            assert_eq!(
                trade
                    .execution_price
                    .quote(input_amount.clone())
                    .unwrap()
                    .quotient(),
                expected_output_amount.quotient()
            );
            assert_eq!(
                trade
                    .execution_price
                    .invert()
                    .quote(expected_output_amount.clone())
                    .unwrap()
                    .quotient(),
                input_amount.quotient()
            );

            assert_eq!(
                trade
                    .price_impact
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "16.8751042187760547"
            );

            // TradeType.EXACT_OUTPUT
            let output_amount = CurrencyAmount::from_raw_amount(
                WETH9.clone(),
                BigInt::from_str("1662497915624478906").unwrap(),
            )
            .unwrap();
            let expected_input_amount = CurrencyAmount::from_raw_amount(
                tokens[1].clone(),
                decimalize(1, tokens[1].decimals),
            )
            .unwrap();
            let trade =
                Trade::new(route.clone(), output_amount.clone(), TradeType::ExactOutput).unwrap();

            assert_eq!(trade.route, route);
            assert_eq!(trade.trade_type, TradeType::ExactOutput);
            assert_eq!(trade.output_amount, output_amount);
            assert_eq!(trade.input_amount, expected_input_amount);

            assert_eq!(
                trade
                    .execution_price
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "1.6624979156244789"
            );
            assert_eq!(
                trade
                    .execution_price
                    .invert()
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "0.601504513540621865"
            );
            assert_eq!(
                trade
                    .execution_price
                    .quote(expected_input_amount.clone())
                    .unwrap()
                    .quotient(),
                output_amount.quotient()
            );
            assert_eq!(
                trade
                    .execution_price
                    .invert()
                    .quote(output_amount)
                    .unwrap()
                    .quotient(),
                expected_input_amount.quotient()
            );

            assert_eq!(
                trade
                    .price_impact
                    .to_significant(18, Rounding::RoundDown)
                    .unwrap(),
                "16.8751042187760547"
            );

            // Minimum TradeType.EXACT_INPUT
            if [9, 18].contains(&tokens[1].decimals) {
                let route = Route::new(
                    vec![Pair::new(
                        CurrencyAmount::from_raw_amount(
                            tokens[1].clone(),
                            decimalize(1, tokens[1].decimals),
                        )
                        .unwrap(),
                        CurrencyAmount::from_raw_amount(
                            WETH9.clone(),
                            (decimalize(10, WETH9.decimals))
                                + if tokens[1].decimals == 9 {
                                    BigInt::from_str("30090280812437312").unwrap()
                                } else {
                                    BigInt::from_str("30090270812437322").unwrap()
                                },
                        )
                        .unwrap(),
                    )
                    .unwrap()],
                    tokens[1].clone(),
                    WETH9.clone(),
                );
                let input_amount =
                    CurrencyAmount::from_raw_amount(tokens[1].clone(), BigInt::from(1)).unwrap();
                let trade = Trade::new(route, input_amount, TradeType::ExactInput).unwrap();

                let expected_impact = if tokens[1].decimals == 9 {
                    "0.300000099400899901"
                } else {
                    "0.3000000000000001"
                };
                assert_eq!(
                    trade
                        .price_impact
                        .to_significant(18, Rounding::RoundDown)
                        .unwrap(),
                    expected_impact
                );
            }
        }
    }
}
