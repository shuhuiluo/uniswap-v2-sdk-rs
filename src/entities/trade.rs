use crate::prelude::{Error, *};
use alloc::vec;
use core::cmp::Ordering;
use uniswap_sdk_core::prelude::*;

#[allow(clippy::too_long_first_doc_paragraph)]
/// Comparator function to allow sorting of trades by their output amounts, in decreasing order, and
/// then input amounts in increasing order. i.e. the best trades have the most outputs for the least
/// inputs and are sorted first.
#[inline]
pub fn input_output_comparator<TInput: BaseCurrency, TOutput: BaseCurrency>(
    a: &Trade<TInput, TOutput>,
    b: &Trade<TInput, TOutput>,
) -> Ordering {
    // must have same input and output token for comparison
    assert!(
        a.input_amount.currency.equals(&b.input_amount.currency),
        "INPUT_CURRENCY"
    );
    assert!(
        a.output_amount.currency.equals(&b.output_amount.currency),
        "OUTPUT_CURRENCY"
    );
    let a_input = a.input_amount.as_fraction();
    let b_input = b.input_amount.as_fraction();
    let a_output = a.output_amount.as_fraction();
    let b_output = b.output_amount.as_fraction();
    if a_output == b_output {
        a_input.cmp(&b_input)
    } else {
        // tradeA has less output than trade B, so should come second
        if a_output < b_output {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }
}

/// Extension of the input output comparator that also considers other dimensions of the trade in
/// ranking them.
#[inline]
pub fn trade_comparator<TInput: BaseCurrency, TOutput: BaseCurrency>(
    a: &Trade<TInput, TOutput>,
    b: &Trade<TInput, TOutput>,
) -> Ordering {
    let io_comp = input_output_comparator(a, b);
    if io_comp != Ordering::Equal {
        return io_comp;
    }

    // consider lowest slippage next, since these are less likely to fail
    match a.price_impact.cmp(&b.price_impact) {
        Ordering::Less => Ordering::Less,
        Ordering::Greater => Ordering::Greater,
        Ordering::Equal => {
            // consider the number of hops since each hop costs gas
            a.route.pairs.len().cmp(&b.route.pairs.len())
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct BestTradeOptions {
    /// how many results to return
    pub max_num_results: Option<usize>,
    /// the maximum number of hops a trade should contain
    pub max_hops: Option<usize>,
}

/// Represents a trade executed against a list of pairs.
///
/// Does not account for slippage, i.e. trades that front run this trade and move the price.
#[derive(Clone, PartialEq, Debug)]
pub struct Trade<TInput: BaseCurrency, TOutput: BaseCurrency> {
    /// The route of the trade, i.e. which pairs the trade goes through and the input/output
    /// currencies.
    pub route: Route<TInput, TOutput>,
    /// The type of the trade, either exact in or exact out.
    pub trade_type: TradeType,
    /// The input amount for the trade assuming no slippage.
    pub input_amount: CurrencyAmount<TInput>,
    /// The output amount for the trade assuming no slippage.
    pub output_amount: CurrencyAmount<TOutput>,
    /// The price expressed in terms of output amount/input amount.
    pub execution_price: Price<TInput, TOutput>,
    /// The percent difference between the mid price before the trade and the trade execution
    /// price.
    pub price_impact: Percent,
}

impl<TInput: BaseCurrency, TOutput: BaseCurrency> Trade<TInput, TOutput> {
    #[inline]
    pub fn new(
        route: Route<TInput, TOutput>,
        amount: CurrencyAmount<impl BaseCurrency>,
        trade_type: TradeType,
    ) -> Result<Self, Error> {
        let mut token_amount: CurrencyAmount<Token> = amount.wrapped_owned()?;
        let input_amount: CurrencyAmount<TInput>;
        let output_amount: CurrencyAmount<TOutput>;
        if trade_type == TradeType::ExactInput {
            assert!(amount.currency.equals(&route.input), "INPUT");
            for pair in &route.pairs {
                (token_amount, _) = pair.get_output_amount(&token_amount, false)?;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                amount.numerator,
                amount.denominator,
            )?;
            output_amount = CurrencyAmount::from_fractional_amount(
                route.output.clone(),
                token_amount.numerator,
                token_amount.denominator,
            )?;
        } else {
            assert!(amount.currency.equals(&route.output), "OUTPUT");
            for pair in route.pairs.iter().rev() {
                (token_amount, _) = pair.get_input_amount(&token_amount, false)?;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                token_amount.numerator,
                token_amount.denominator,
            )?;
            output_amount = CurrencyAmount::from_fractional_amount(
                route.output.clone(),
                amount.numerator,
                amount.denominator,
            )?;
        }
        let price_impact =
            compute_price_impact(&route.mid_price()?, &input_amount, &output_amount)?;
        let execution_price = Price::new(
            input_amount.currency.clone(),
            output_amount.currency.clone(),
            input_amount.quotient(),
            output_amount.quotient(),
        );
        Ok(Trade {
            route,
            trade_type,
            input_amount,
            output_amount,
            execution_price,
            price_impact,
        })
    }

    /// Constructs an exact in trade with the given amount in and route
    ///
    /// ## Arguments
    ///
    /// * `route`: The route of the exact in trade
    /// * `amount_in`: The amount being passed in
    #[inline]
    pub fn exact_in(
        route: Route<TInput, TOutput>,
        amount_in: CurrencyAmount<TInput>,
    ) -> Result<Self, Error> {
        Trade::new(route, amount_in, TradeType::ExactInput)
    }

    /// Constructs an exact out trade with the given amount out and route
    ///
    /// ## Arguments
    ///
    /// * `route`: The route of the exact out trade
    /// * `amount_out`: The amount returned by the trade
    #[inline]
    pub fn exact_out(
        route: Route<TInput, TOutput>,
        amount_out: CurrencyAmount<TOutput>,
    ) -> Result<Self, Error> {
        Trade::new(route, amount_out, TradeType::ExactOutput)
    }

    /// Get the minimum amount that must be received from this trade for the given slippage
    /// tolerance
    ///
    /// ## Arguments
    ///
    /// * `slippage_tolerance`: The tolerance of unfavorable slippage from the execution price of
    ///   this trade
    #[inline]
    pub fn minimum_amount_out(
        &self,
        slippage_tolerance: Percent,
    ) -> Result<CurrencyAmount<TOutput>, Error> {
        assert!(
            slippage_tolerance >= Percent::new(0, 1),
            "SLIPPAGE_TOLERANCE"
        );
        if self.trade_type == TradeType::ExactOutput {
            return Ok(self.output_amount.clone());
        }
        let slippage_adjusted_amount_out = ((Percent::new(1, 1) + slippage_tolerance).invert()
            * Percent::new(self.output_amount.quotient(), 1))
        .quotient();
        CurrencyAmount::from_raw_amount(
            self.output_amount.currency.clone(),
            slippage_adjusted_amount_out,
        )
        .map_err(Error::Core)
    }

    /// Get the maximum amount in that can be spent via this trade for the given slippage tolerance
    ///
    /// ## Arguments
    ///
    /// * `slippage_tolerance`: The tolerance of unfavorable slippage from the execution price of
    ///   this trade
    #[inline]
    pub fn maximum_amount_in(
        &self,
        slippage_tolerance: Percent,
    ) -> Result<CurrencyAmount<TInput>, Error> {
        assert!(
            slippage_tolerance >= Percent::new(0, 1),
            "SLIPPAGE_TOLERANCE"
        );
        if self.trade_type == TradeType::ExactInput {
            return Ok(self.input_amount.clone());
        }
        let slippage_adjusted_amount_in = ((Percent::new(1, 1) + slippage_tolerance)
            * Percent::new(self.input_amount.quotient(), 1))
        .quotient();
        CurrencyAmount::from_raw_amount(
            self.input_amount.currency.clone(),
            slippage_adjusted_amount_in,
        )
        .map_err(Error::Core)
    }

    /// Given a list of pairs, and a fixed amount in, returns the top `max_num_results` trades that
    /// go from an input token amount to an output token, making at most `max_hops` hops.
    ///
    /// Note this does not consider aggregation, as routes are linear. It's possible a better route
    /// exists by splitting the amount in among multiple routes.
    ///
    /// ## Arguments
    ///
    /// * `pairs`: The pairs to consider in finding the best trade
    /// * `currency_amount_in`: The exact amount of input currency to spend
    /// * `currency_out`: The desired currency out
    /// * `best_trade_options`: Maximum number of results to return and maximum number of hops a
    ///   returned trade can make, e.g. 1 hop goes through a single pair
    /// * `current_pairs`: Used in recursion; the current list of pairs
    /// * `next_amount_in`: Used in recursion; the original value of the currency_amount_in
    ///   parameter
    /// * `best_trades`: Used in recursion; the current list of best trades
    #[inline]
    #[allow(clippy::needless_pass_by_value)]
    pub fn best_trade_exact_in<'a>(
        pairs: Vec<Pair>,
        currency_amount_in: &'a CurrencyAmount<TInput>,
        currency_out: &'a TOutput,
        best_trade_options: BestTradeOptions,
        current_pairs: Vec<Pair>,
        next_amount_in: Option<CurrencyAmount<Token>>,
        best_trades: &'a mut Vec<Self>,
    ) -> Result<&'a mut Vec<Self>, Error> {
        assert!(!pairs.is_empty(), "PAIRS");
        let max_num_results = best_trade_options.max_num_results.unwrap_or(3);
        let max_hops = best_trade_options.max_hops.unwrap_or(3);
        assert!(max_hops > 0, "MAX_HOPS");
        let amount_in = match next_amount_in {
            Some(amount_in) => {
                assert!(!current_pairs.is_empty(), "INVALID_RECURSION");
                amount_in
            }
            None => currency_amount_in.wrapped_owned()?,
        };
        let token_out = currency_out.wrapped();
        for pair in &pairs {
            // pair irrelevant
            if !pair.involves_token(&amount_in.currency) {
                continue;
            }
            if pair.reserve1().quotient().is_zero() || pair.reserve0().quotient().is_zero() {
                continue;
            }
            let amount_out = match pair.get_output_amount(&amount_in, false) {
                Ok((amount_out, _)) => amount_out,
                Err(Error::InsufficientInputAmount) => continue,
                Err(e) => return Err(e),
            };
            // we have arrived at the output token, so this is the final trade of one of the paths
            if amount_out.currency.equals(token_out) {
                let mut next_pairs = current_pairs.clone();
                next_pairs.push(pair.clone());
                let trade = Self::new(
                    Route::new(
                        next_pairs,
                        currency_amount_in.currency.clone(),
                        currency_out.clone(),
                    ),
                    currency_amount_in.clone(),
                    TradeType::ExactInput,
                )?;
                sorted_insert(best_trades, trade, max_num_results, trade_comparator);
            } else if max_hops > 1 && pairs.len() > 1 {
                let pairs_excluding_this_pair = pairs
                    .iter()
                    .filter(|&p| p.address() != pair.address())
                    .cloned()
                    .collect();
                // otherwise, consider all the other paths that lead from this token as long as we
                // have not exceeded maxHops
                let mut next_pairs = current_pairs.clone();
                next_pairs.push(pair.clone());
                Self::best_trade_exact_in(
                    pairs_excluding_this_pair,
                    currency_amount_in,
                    currency_out,
                    BestTradeOptions {
                        max_num_results: Some(max_num_results),
                        max_hops: Some(max_hops - 1),
                    },
                    next_pairs,
                    Some(amount_out),
                    best_trades,
                )?;
            }
        }
        Ok(best_trades)
    }

    /// Return the execution price after accounting for slippage tolerance
    ///
    /// ## Arguments
    ///
    /// * `slippage_tolerance`: The allowed tolerated slippage
    #[inline]
    pub fn worst_execution_price(
        &self,
        slippage_tolerance: Percent,
    ) -> Result<Price<TInput, TOutput>, Error> {
        Ok(Price::new(
            self.input_amount.currency.clone(),
            self.output_amount.currency.clone(),
            self.maximum_amount_in(slippage_tolerance.clone())?
                .quotient(),
            self.minimum_amount_out(slippage_tolerance)?.quotient(),
        ))
    }

    /// Given a list of pairs, and a fixed amount out, returns the top `max_num_results` trades that
    /// go from an input token to an output token amount, making at most `max_hops` hops.
    ///
    /// Note this does not consider aggregation, as routes are linear. It's possible a better route
    /// exists by splitting the amount in among multiple routes.
    ///
    /// ## Arguments
    ///
    /// * `pairs`: The pairs to consider in finding the best trade
    /// * `currency_in`: The currency to spend
    /// * `currency_amount_out`: The desired currency amount out
    /// * `best_trade_options`: Maximum number of results to return and maximum number of hops a
    ///   returned trade can make, e.g. 1 hop goes through a single pair
    /// * `current_pairs`: Used in recursion; the current list of pairs
    /// * `next_amount_out`: Used in recursion; the exact amount of currency out
    /// * `best_trades`: Used in recursion; the current list of best trades
    #[inline]
    #[allow(clippy::needless_pass_by_value)]
    pub fn best_trade_exact_out<'a>(
        pairs: Vec<Pair>,
        currency_in: &'a TInput,
        currency_amount_out: &'a CurrencyAmount<TOutput>,
        best_trade_options: BestTradeOptions,
        current_pairs: Vec<Pair>,
        next_amount_out: Option<CurrencyAmount<Token>>,
        best_trades: &'a mut Vec<Self>,
    ) -> Result<&'a mut Vec<Self>, Error> {
        assert!(!pairs.is_empty(), "PAIRS");
        let max_num_results = best_trade_options.max_num_results.unwrap_or(3);
        let max_hops = best_trade_options.max_hops.unwrap_or(3);
        assert!(max_hops > 0, "MAX_HOPS");
        let amount_out = match next_amount_out {
            Some(amount_out) => {
                assert!(!current_pairs.is_empty(), "INVALID_RECURSION");
                amount_out
            }
            None => currency_amount_out.wrapped_owned()?,
        };
        let token_in = currency_in.wrapped();
        for pair in &pairs {
            // pair irrelevant
            if !pair.involves_token(&amount_out.currency) {
                continue;
            }
            if pair.reserve1().quotient().is_zero() || pair.reserve0().quotient().is_zero() {
                continue;
            }
            let amount_in = match pair.get_input_amount(&amount_out, false) {
                Ok((amount_in, _)) => amount_in,
                Err(Error::InsufficientReserves) => continue,
                Err(e) => return Err(e),
            };
            // we have arrived at the input token, so this is the first trade of one of the paths
            if amount_in.currency.equals(token_in) {
                let mut next_pairs = vec![pair.clone()];
                next_pairs.extend(current_pairs.clone());
                let trade = Self::new(
                    Route::new(
                        next_pairs,
                        currency_in.clone(),
                        currency_amount_out.currency.clone(),
                    ),
                    currency_amount_out.clone(),
                    TradeType::ExactOutput,
                )?;
                sorted_insert(best_trades, trade, max_num_results, trade_comparator);
            } else if max_hops > 1 && pairs.len() > 1 {
                let pairs_excluding_this_pair = pairs
                    .iter()
                    .filter(|&p| p.address() != pair.address())
                    .cloned()
                    .collect();
                // otherwise, consider all the other paths that arrive at this token as long as we
                // have not exceeded maxHops
                let mut next_pairs = vec![pair.clone()];
                next_pairs.extend(current_pairs.clone());
                Self::best_trade_exact_out(
                    pairs_excluding_this_pair,
                    currency_in,
                    currency_amount_out,
                    BestTradeOptions {
                        max_num_results: Some(max_num_results),
                        max_hops: Some(max_hops - 1),
                    },
                    next_pairs,
                    Some(amount_in),
                    best_trades,
                )?;
            }
        }
        Ok(best_trades)
    }
}

#[allow(dead_code)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;

    static PAIR_0_2: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN2.clone(), 1100).unwrap(),
        )
        .unwrap()
    });
    static PAIR_0_3: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN3.clone(), 900).unwrap(),
        )
        .unwrap()
    });
    static PAIR_1_2: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 1200).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN2.clone(), 1000).unwrap(),
        )
        .unwrap()
    });
    static PAIR_1_3: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 1200).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN3.clone(), 1300).unwrap(),
        )
        .unwrap()
    });
    static EMPTY_PAIR_0_1: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 0).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 0).unwrap(),
        )
        .unwrap()
    });

    mod new {
        use super::*;

        #[test]
        fn can_be_constructed_with_ether_as_input() {
            let trade = Trade::new(
                Route::new(vec![PAIR_WETH_0.clone()], ETHER.clone(), TOKEN0.clone()),
                CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                TradeType::ExactInput,
            )
            .unwrap();
            assert_eq!(trade.input_amount.currency, ETHER.clone());
            assert_eq!(trade.output_amount.currency, TOKEN0.clone());
        }

        #[test]
        fn can_be_constructed_with_ether_as_input_for_exact_output() {
            let trade = Trade::new(
                Route::new(vec![PAIR_WETH_0.clone()], ETHER.clone(), TOKEN0.clone()),
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                TradeType::ExactOutput,
            )
            .unwrap();
            assert_eq!(trade.input_amount.currency, ETHER.clone());
            assert_eq!(trade.output_amount.currency, TOKEN0.clone());
        }

        #[test]
        fn can_be_constructed_with_ether_as_output() {
            let trade = Trade::new(
                Route::new(vec![PAIR_WETH_0.clone()], TOKEN0.clone(), ETHER.clone()),
                CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                TradeType::ExactOutput,
            )
            .unwrap();
            assert_eq!(trade.input_amount.currency, TOKEN0.clone());
            assert_eq!(trade.output_amount.currency, ETHER.clone());
        }

        #[test]
        fn can_be_constructed_with_ether_as_output_for_exact_input() {
            let trade = Trade::new(
                Route::new(vec![PAIR_WETH_0.clone()], TOKEN0.clone(), ETHER.clone()),
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                TradeType::ExactInput,
            )
            .unwrap();
            assert_eq!(trade.input_amount.currency, TOKEN0.clone());
            assert_eq!(trade.output_amount.currency, ETHER.clone());
        }
    }

    mod best_trade_exact_in {
        use super::*;

        #[test]
        #[should_panic(expected = "PAIRS")]
        fn throws_with_empty_pairs() {
            Trade::best_trade_exact_in(
                vec![],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                &TOKEN2.clone(),
                Default::default(),
                vec![],
                None,
                &mut vec![],
            )
            .unwrap();
        }

        #[test]
        #[should_panic(expected = "MAX_HOPS")]
        fn throws_with_max_hops_of_0() {
            Trade::best_trade_exact_in(
                vec![PAIR_0_2.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                &TOKEN2.clone(),
                BestTradeOptions {
                    max_hops: Some(0),
                    ..Default::default()
                },
                vec![],
                None,
                &mut vec![],
            )
            .unwrap();
        }

        #[test]
        fn provides_the_best_route() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                &TOKEN2.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].route.pairs.len(), 1);
            assert_eq!(result[0].route.path(), vec![TOKEN0.clone(), TOKEN2.clone()]);
            assert_eq!(
                result[0].input_amount,
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap()
            );
            assert_eq!(
                result[0].output_amount,
                CurrencyAmount::from_raw_amount(TOKEN2.clone(), 99).unwrap()
            );
            assert_eq!(result[1].route.pairs.len(), 2);
            assert_eq!(
                result[1].route.path(),
                vec![TOKEN0.clone(), TOKEN1.clone(), TOKEN2.clone()]
            );
            assert_eq!(
                result[1].input_amount,
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap()
            );
            assert_eq!(
                result[1].output_amount,
                CurrencyAmount::from_raw_amount(TOKEN2.clone(), 69).unwrap()
            );
        }

        #[test]
        fn doesnt_throw_for_zero_liquidity_pairs() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![EMPTY_PAIR_0_1.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
                &TOKEN1.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn respects_max_hops() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 10).unwrap(),
                &TOKEN2.clone(),
                BestTradeOptions {
                    max_hops: Some(1),
                    ..Default::default()
                },
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
            assert_eq!(result[0].route.pairs.len(), 1);
            assert_eq!(result[0].route.path(), vec![TOKEN0.clone(), TOKEN2.clone()]);
        }

        #[test]
        fn insufficient_input_for_one_pair() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1).unwrap(),
                &TOKEN2.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
            assert_eq!(result[0].route.pairs.len(), 1);
            assert_eq!(result[0].route.path(), vec![TOKEN0.clone(), TOKEN2.clone()]);
            assert_eq!(
                result[0].output_amount,
                CurrencyAmount::from_raw_amount(TOKEN2.clone(), 1).unwrap()
            );
        }

        #[test]
        fn respects_max_num_results() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 10).unwrap(),
                &TOKEN2.clone(),
                BestTradeOptions {
                    max_num_results: Some(1),
                    ..Default::default()
                },
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
        }

        #[test]
        fn no_path() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![PAIR_0_1.clone(), PAIR_0_3.clone(), PAIR_1_3.clone()],
                &CurrencyAmount::from_raw_amount(TOKEN0.clone(), 10).unwrap(),
                &TOKEN2.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn works_for_ether_currency_input() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![
                    PAIR_WETH_0.clone(),
                    PAIR_0_1.clone(),
                    PAIR_0_3.clone(),
                    PAIR_1_3.clone(),
                ],
                &CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                &TOKEN3.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].input_amount.currency, ETHER.clone());
            assert_eq!(
                result[0].route.path(),
                vec![WETH.clone(), TOKEN0.clone(), TOKEN1.clone(), TOKEN3.clone()],
            );
            assert_eq!(result[0].output_amount.currency, TOKEN3.clone());
            assert_eq!(result[1].input_amount.currency, ETHER.clone());
            assert_eq!(
                result[1].route.path(),
                vec![WETH.clone(), TOKEN0.clone(), TOKEN3.clone()]
            );
            assert_eq!(result[1].output_amount.currency, TOKEN3.clone());
        }

        #[test]
        fn works_for_ether_currency_output() {
            let result = &mut vec![];
            Trade::best_trade_exact_in(
                vec![
                    PAIR_WETH_0.clone(),
                    PAIR_0_1.clone(),
                    PAIR_0_3.clone(),
                    PAIR_1_3.clone(),
                ],
                &CurrencyAmount::from_raw_amount(TOKEN3.clone(), 100).unwrap(),
                &ETHER.clone(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].input_amount.currency, TOKEN3.clone());
            assert_eq!(
                result[0].route.path(),
                vec![TOKEN3.clone(), TOKEN0.clone(), WETH.clone()]
            );
            assert_eq!(result[0].output_amount.currency, ETHER.clone());
            assert_eq!(result[1].input_amount.currency, TOKEN3.clone());
            assert_eq!(
                result[1].route.path(),
                vec![TOKEN3.clone(), TOKEN1.clone(), TOKEN0.clone(), WETH.clone()]
            );
            assert_eq!(result[1].output_amount.currency, ETHER.clone());
        }
    }

    static EXACT_IN_TRADE: Lazy<Trade<Token, Token>> = Lazy::new(|| {
        Trade::new(
            Route::new(
                vec![PAIR_0_1.clone(), PAIR_1_2.clone()],
                TOKEN0.clone(),
                TOKEN2.clone(),
            ),
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
            TradeType::ExactInput,
        )
        .unwrap()
    });

    static EXACT_OUT_TRADE: Lazy<Trade<Token, Token>> = Lazy::new(|| {
        Trade::new(
            Route::new(
                vec![PAIR_0_1.clone(), PAIR_1_2.clone()],
                TOKEN0.clone(),
                TOKEN2.clone(),
            ),
            CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap(),
            TradeType::ExactOutput,
        )
        .unwrap()
    });

    mod maximum_amount_in {
        use super::*;

        mod exact_input {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_IN_TRADE
                    .maximum_amount_in(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .maximum_amount_in(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_IN_TRADE.input_amount
                );
            }

            #[test]
            fn returns_exact_if_non_zero() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .maximum_amount_in(Percent::new(5, 100))
                        .unwrap(),
                    EXACT_IN_TRADE.input_amount
                );
                assert_eq!(
                    EXACT_IN_TRADE
                        .maximum_amount_in(Percent::new(200, 100))
                        .unwrap(),
                    EXACT_IN_TRADE.input_amount
                );
            }
        }

        mod exact_output {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_OUT_TRADE
                    .maximum_amount_in(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .maximum_amount_in(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_OUT_TRADE.input_amount
                );
            }

            #[test]
            fn returns_slippage_amount_if_non_zero() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .maximum_amount_in(Percent::new(5, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN0.clone(), 163).unwrap()
                );
                assert_eq!(
                    EXACT_OUT_TRADE
                        .maximum_amount_in(Percent::new(200, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN0.clone(), 468).unwrap()
                );
            }
        }
    }

    mod minimum_amount_out {
        use super::*;

        mod exact_input {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_IN_TRADE
                    .minimum_amount_out(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .minimum_amount_out(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_IN_TRADE.output_amount
                );
            }

            #[test]
            fn returns_exact_if_non_zero() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .minimum_amount_out(Percent::new(5, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN2.clone(), 65).unwrap()
                );
                assert_eq!(
                    EXACT_IN_TRADE
                        .minimum_amount_out(Percent::new(200, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN2.clone(), 23).unwrap()
                );
            }
        }

        mod exact_output {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_OUT_TRADE
                    .minimum_amount_out(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .minimum_amount_out(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_OUT_TRADE.output_amount
                );
            }

            #[test]
            fn returns_slippage_amount_if_non_zero() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .minimum_amount_out(Percent::new(5, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap()
                );
                assert_eq!(
                    EXACT_OUT_TRADE
                        .minimum_amount_out(Percent::new(200, 100))
                        .unwrap(),
                    CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap()
                );
            }
        }
    }

    mod worst_execution_price {
        use super::*;

        mod exact_input {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_IN_TRADE
                    .worst_execution_price(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .worst_execution_price(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_IN_TRADE.execution_price
                );
            }

            #[test]
            fn returns_exact_if_non_zero() {
                assert_eq!(
                    EXACT_IN_TRADE
                        .worst_execution_price(Percent::new(0, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 100, 69)
                );
                assert_eq!(
                    EXACT_IN_TRADE
                        .worst_execution_price(Percent::new(5, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 100, 65)
                );
                assert_eq!(
                    EXACT_IN_TRADE
                        .worst_execution_price(Percent::new(200, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 100, 23)
                );
            }
        }

        mod exact_output {
            use super::*;

            #[test]
            #[should_panic(expected = "SLIPPAGE_TOLERANCE")]
            fn throws_if_less_than_0() {
                EXACT_OUT_TRADE
                    .worst_execution_price(Percent::new(-1, 100))
                    .unwrap();
            }

            #[test]
            fn returns_exact_if_0() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .worst_execution_price(Percent::new(0, 100))
                        .unwrap(),
                    EXACT_OUT_TRADE.execution_price
                );
            }

            #[test]
            fn returns_slippage_amount_if_non_zero() {
                assert_eq!(
                    EXACT_OUT_TRADE
                        .worst_execution_price(Percent::new(0, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 156, 100)
                );
                assert_eq!(
                    EXACT_OUT_TRADE
                        .worst_execution_price(Percent::new(5, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 163, 100)
                );
                assert_eq!(
                    EXACT_OUT_TRADE
                        .worst_execution_price(Percent::new(200, 100))
                        .unwrap(),
                    Price::new(TOKEN0.clone(), TOKEN2.clone(), 468, 100)
                );
            }
        }
    }

    mod best_trade_exact_out {
        use super::*;

        #[test]
        #[should_panic(expected = "PAIRS")]
        fn throws_with_empty_pairs() {
            Trade::best_trade_exact_out(
                vec![],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap(),
                Default::default(),
                vec![],
                None,
                &mut vec![],
            )
            .unwrap();
        }

        #[test]
        #[should_panic(expected = "MAX_HOPS")]
        fn throws_with_max_hops_of_0() {
            Trade::best_trade_exact_out(
                vec![PAIR_0_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap(),
                BestTradeOptions {
                    max_hops: Some(0),
                    ..Default::default()
                },
                vec![],
                None,
                &mut vec![],
            )
            .unwrap();
        }

        #[test]
        fn provides_the_best_route() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].route.pairs.len(), 1);
            assert_eq!(result[0].route.path(), vec![TOKEN0.clone(), TOKEN2.clone()]);
            assert_eq!(
                result[0].input_amount,
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 101).unwrap()
            );
            assert_eq!(
                result[0].output_amount,
                CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap()
            );
            assert_eq!(result[1].route.pairs.len(), 2);
            assert_eq!(
                result[1].route.path(),
                vec![TOKEN0.clone(), TOKEN1.clone(), TOKEN2.clone()]
            );
            assert_eq!(
                result[1].input_amount,
                CurrencyAmount::from_raw_amount(TOKEN0.clone(), 156).unwrap()
            );
            assert_eq!(
                result[1].output_amount,
                CurrencyAmount::from_raw_amount(TOKEN2.clone(), 100).unwrap()
            );
        }

        #[test]
        fn doesnt_throw_for_zero_liquidity_pairs() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![EMPTY_PAIR_0_1.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN1.clone(), 100).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn respects_max_hops() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 10).unwrap(),
                BestTradeOptions {
                    max_hops: Some(1),
                    ..Default::default()
                },
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
            assert_eq!(result[0].route.pairs.len(), 1);
            assert_eq!(result[0].route.path(), vec![TOKEN0.clone(), TOKEN2.clone()]);
        }

        #[test]
        fn insufficient_liquidity() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 1200).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn insufficient_liquidity_in_one_pair_but_not_the_other() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 1050).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
        }

        #[test]
        fn respects_max_num_results() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_2.clone(), PAIR_1_2.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 10).unwrap(),
                BestTradeOptions {
                    max_num_results: Some(1),
                    ..Default::default()
                },
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 1);
        }

        #[test]
        fn no_path() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![PAIR_0_1.clone(), PAIR_0_3.clone(), PAIR_1_3.clone()],
                &TOKEN0.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN2.clone(), 10).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn works_for_ether_currency_input() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![
                    PAIR_WETH_0.clone(),
                    PAIR_0_1.clone(),
                    PAIR_0_3.clone(),
                    PAIR_1_3.clone(),
                ],
                &ETHER.clone(),
                &CurrencyAmount::from_raw_amount(TOKEN3.clone(), 100).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].input_amount.currency, ETHER.clone());
            assert_eq!(
                result[0].route.path(),
                vec![WETH.clone(), TOKEN0.clone(), TOKEN1.clone(), TOKEN3.clone()],
            );
            assert_eq!(result[0].output_amount.currency, TOKEN3.clone());
            assert_eq!(result[1].input_amount.currency, ETHER.clone());
            assert_eq!(
                result[1].route.path(),
                vec![WETH.clone(), TOKEN0.clone(), TOKEN3.clone()]
            );
            assert_eq!(result[1].output_amount.currency, TOKEN3.clone());
        }

        #[test]
        fn works_for_ether_currency_output() {
            let result = &mut vec![];
            Trade::best_trade_exact_out(
                vec![
                    PAIR_WETH_0.clone(),
                    PAIR_0_1.clone(),
                    PAIR_0_3.clone(),
                    PAIR_1_3.clone(),
                ],
                &TOKEN3.clone(),
                &CurrencyAmount::from_raw_amount(ETHER.clone(), 100).unwrap(),
                Default::default(),
                vec![],
                None,
                result,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].input_amount.currency, TOKEN3.clone());
            assert_eq!(
                result[0].route.path(),
                vec![TOKEN3.clone(), TOKEN0.clone(), WETH.clone()]
            );
            assert_eq!(result[0].output_amount.currency, ETHER.clone());
            assert_eq!(result[1].input_amount.currency, TOKEN3.clone());
            assert_eq!(
                result[1].route.path(),
                vec![TOKEN3.clone(), TOKEN1.clone(), TOKEN0.clone(), WETH.clone()]
            );
            assert_eq!(result[1].output_amount.currency, ETHER.clone());
        }
    }
}
