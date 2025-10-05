mod pair;
mod route;
mod trade;

pub use pair::{compute_pair_address, Pair};
pub use route::Route;
pub use trade::*;

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use alloc::vec;
    use once_cell::sync::Lazy;
    use uniswap_sdk_core::{prelude::*, token};

    const CHAIN_ID: u64 = 3;
    const ADDRESSES: [&str; 3] = [
        "0000000000000000000000000000000000000001",
        "0000000000000000000000000000000000000002",
        "0000000000000000000000000000000000000003",
    ];

    static WETH9: Lazy<Token> = Lazy::new(|| WETH9::on_chain(CHAIN_ID).unwrap());

    fn decimalize(amount: u64, decimals: u8) -> BigInt {
        BigInt::from(amount) * BigInt::from(10).pow(decimals as u32)
    }

    #[test]
    fn decimals_permutation_0_0_0() {
        let decimals = [0, 0, 0];
        test_decimal_permutation(&decimals);
    }

    #[test]
    fn decimals_permutation_0_9_18() {
        let decimals = [0, 9, 18];
        test_decimal_permutation(&decimals);
    }

    #[test]
    fn decimals_permutation_18_18_18() {
        let decimals = [18, 18, 18];
        test_decimal_permutation(&decimals);
    }

    fn test_decimal_permutation(decimals: &[u8; 3]) {
        let tokens: Vec<Token> = ADDRESSES
            .iter()
            .enumerate()
            .map(|(i, &address)| token!(CHAIN_ID, address, decimals[i]))
            .collect();

        // Test Pair creation
        let pairs = vec![
            Pair::new(
                CurrencyAmount::from_raw_amount(
                    tokens[0].clone(),
                    decimalize(1, tokens[0].decimals()),
                )
                .unwrap(),
                CurrencyAmount::from_raw_amount(
                    tokens[1].clone(),
                    decimalize(1, tokens[1].decimals()),
                )
                .unwrap(),
            )
            .unwrap(),
            Pair::new(
                CurrencyAmount::from_raw_amount(
                    tokens[1].clone(),
                    decimalize(1, tokens[1].decimals()),
                )
                .unwrap(),
                CurrencyAmount::from_raw_amount(
                    tokens[2].clone(),
                    decimalize(1, tokens[2].decimals()),
                )
                .unwrap(),
            )
            .unwrap(),
            Pair::new(
                CurrencyAmount::from_raw_amount(
                    tokens[2].clone(),
                    decimalize(1, tokens[2].decimals()),
                )
                .unwrap(),
                CurrencyAmount::from_raw_amount(WETH9.clone(), decimalize(1234, WETH9.decimals()))
                    .unwrap(),
            )
            .unwrap(),
        ];

        // Test Route creation
        let route = Route::new(pairs.clone(), tokens[0].clone(), WETH9.clone());
        assert_eq!(route.pairs, pairs);
        assert_eq!(route.path().len(), 4);
        assert_eq!(route.path()[0], tokens[0]);
        assert_eq!(route.path()[1], tokens[1]);
        assert_eq!(route.path()[2], tokens[2]);
        assert_eq!(route.path()[3], *WETH9);
        assert_eq!(route.input, tokens[0]);
        assert_eq!(route.output, *WETH9);

        // Test midPrice
        let input_amount = CurrencyAmount::from_raw_amount(
            route.input.clone(),
            decimalize(1, route.input.decimals()),
        )
        .unwrap();
        let output_amount = CurrencyAmount::from_raw_amount(
            route.output.clone(),
            decimalize(1234, route.output.decimals()),
        )
        .unwrap();

        let mid_price = route.mid_price().unwrap();
        let mid_price_quote = mid_price.quote(&input_amount).unwrap();
        assert_eq!(mid_price_quote.to_exact(), output_amount.to_exact());

        let inverted = mid_price.invert();
        let inverted_quote = inverted.quote(&output_amount).unwrap();
        assert_eq!(inverted_quote.to_exact(), input_amount.to_exact());

        assert_eq!(inverted.to_significant(5, None).unwrap(), "0.00081037");
        assert_eq!(mid_price.to_fixed(2, None), "1234.00");
        assert_eq!(inverted.to_fixed(8, None), "0.00081037");

        // Test Trade
        let route = Route::new(
            vec![Pair::new(
                CurrencyAmount::from_raw_amount(
                    tokens[1].clone(),
                    decimalize(5, tokens[1].decimals()),
                )
                .unwrap(),
                CurrencyAmount::from_raw_amount(WETH9.clone(), decimalize(10, WETH9.decimals()))
                    .unwrap(),
            )
            .unwrap()],
            tokens[1].clone(),
            WETH9.clone(),
        );

        // Test Trade with EXACT_INPUT
        test_exact_input_trade(&tokens, &route);

        // Test Trade with EXACT_OUTPUT
        test_exact_output_trade(&tokens, &route);

        // Test minimum EXACT_INPUT
        test_minimum_exact_input(&tokens, decimals);
    }

    fn test_exact_input_trade(tokens: &[Token], route: &Route<Token, Token>) {
        let input_amount =
            CurrencyAmount::from_raw_amount(tokens[1].clone(), decimalize(1, tokens[1].decimals()))
                .unwrap();

        let expected_output_amount =
            CurrencyAmount::from_raw_amount(WETH9.clone(), BigInt::from(1662497915624478906_i128))
                .unwrap();

        let trade = Trade::exact_in(route.clone(), input_amount.clone()).unwrap();

        assert_eq!(trade.route, *route);
        assert_eq!(trade.trade_type, TradeType::ExactInput);
        assert_eq!(trade.input_amount, input_amount);
        assert_eq!(trade.output_amount, expected_output_amount);

        assert_eq!(
            trade.execution_price.to_significant(18, None).unwrap(),
            "1.66249791562447891"
        );
        assert_eq!(
            trade
                .execution_price
                .invert()
                .to_significant(18, None)
                .unwrap(),
            "0.601504513540621866"
        );
        assert_eq!(
            trade
                .execution_price
                .quote(&input_amount)
                .unwrap()
                .quotient(),
            expected_output_amount.quotient()
        );
        assert_eq!(
            trade
                .execution_price
                .invert()
                .quote(&expected_output_amount)
                .unwrap()
                .quotient(),
            input_amount.quotient()
        );

        assert_eq!(
            trade.price_impact.to_significant(18, None).unwrap(),
            "16.8751042187760547"
        );
    }

    fn test_exact_output_trade(tokens: &[Token], route: &Route<Token, Token>) {
        let output_amount =
            CurrencyAmount::from_raw_amount(WETH9.clone(), BigInt::from(1662497915624478906_i128))
                .unwrap();

        let expected_input_amount =
            CurrencyAmount::from_raw_amount(tokens[1].clone(), decimalize(1, tokens[1].decimals()))
                .unwrap();

        let trade = Trade::exact_out(route.clone(), output_amount.clone()).unwrap();

        assert_eq!(trade.route, *route);
        assert_eq!(trade.trade_type, TradeType::ExactOutput);
        assert_eq!(trade.output_amount, output_amount);
        assert_eq!(trade.input_amount, expected_input_amount);

        assert_eq!(
            trade.execution_price.to_significant(18, None).unwrap(),
            "1.66249791562447891"
        );
        assert_eq!(
            trade
                .execution_price
                .invert()
                .to_significant(18, None)
                .unwrap(),
            "0.601504513540621866"
        );
        assert_eq!(
            trade
                .execution_price
                .quote(&expected_input_amount)
                .unwrap()
                .quotient(),
            output_amount.quotient()
        );
        assert_eq!(
            trade
                .execution_price
                .invert()
                .quote(&output_amount)
                .unwrap()
                .quotient(),
            expected_input_amount.quotient()
        );

        assert_eq!(
            trade.price_impact.to_significant(18, None).unwrap(),
            "16.8751042187760547"
        );
    }

    fn test_minimum_exact_input(tokens: &[Token], decimals: &[u8; 3]) {
        if decimals[1] == 9 || decimals[1] == 18 {
            let route = Route::new(
                vec![Pair::new(
                    CurrencyAmount::from_raw_amount(
                        tokens[1].clone(),
                        decimalize(1, tokens[1].decimals()),
                    )
                    .unwrap(),
                    CurrencyAmount::from_raw_amount(
                        WETH9.clone(),
                        decimalize(10, WETH9.decimals())
                            + if tokens[1].decimals() == 9 {
                                BigInt::from(30090280812437312_i128)
                            } else {
                                BigInt::from(30090270812437322_i128)
                            },
                    )
                    .unwrap(),
                )
                .unwrap()],
                tokens[1].clone(),
                WETH9.clone(),
            );

            let output_amount = CurrencyAmount::from_raw_amount(tokens[1].clone(), 1).unwrap();
            let trade = Trade::exact_in(route, output_amount).unwrap();

            assert_eq!(
                trade.price_impact.to_significant(18, None).unwrap(),
                if tokens[1].decimals() == 9 {
                    "0.300000099400899902"
                } else {
                    "0.3000000000000001"
                }
            );
        }
    }
}
