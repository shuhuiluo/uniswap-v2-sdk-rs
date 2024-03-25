use crate::prelude::{Pair, Route};
use anyhow::Result;
use uniswap_sdk_core::prelude::sorted_insert::sorted_insert;
use uniswap_sdk_core::prelude::{compute_price_impact::compute_price_impact, *};

/// Comparator function to allow sorting of trades by their output amounts, in decreasing order, and
/// then input amounts in increasing order. i.e. the best trades have the most outputs for the least
/// inputs and are sorted first.
pub fn input_output_comparator<TInput: CurrencyTrait, TOutput: CurrencyTrait>(
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
pub fn trade_comparator<TInput: CurrencyTrait, TOutput: CurrencyTrait>(
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
            a.route.path.len().cmp(&b.route.path.len())
        }
    }
}

#[derive(Clone, PartialEq, Debug, Default)]
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
pub struct Trade<TInput: CurrencyTrait, TOutput: CurrencyTrait> {
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

impl<TInput: CurrencyTrait, TOutput: CurrencyTrait> Trade<TInput, TOutput> {
    pub fn new(
        route: Route<TInput, TOutput>,
        amount: CurrencyAmount<impl CurrencyTrait>,
        trade_type: TradeType,
    ) -> Result<Self> {
        let len = route.path.len();
        let mut token_amount: CurrencyAmount<Token>;
        let input_amount: CurrencyAmount<TInput>;
        let output_amount: CurrencyAmount<TOutput>;
        if trade_type == TradeType::ExactInput {
            assert!(amount.currency.equals(&route.input), "INPUT");
            token_amount = amount.wrapped()?;
            for i in 0..len - 1 {
                let pair = &route.pairs[i];
                let (output_amount, _) = pair.get_output_amount(&token_amount, false)?;
                token_amount = output_amount;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                amount.numerator(),
                amount.denominator(),
            )?;
            output_amount = CurrencyAmount::from_fractional_amount(
                route.output.clone(),
                token_amount.numerator(),
                token_amount.denominator(),
            )?;
        } else {
            assert!(amount.currency.equals(&route.output), "OUTPUT");
            token_amount = amount.wrapped()?;
            for i in (1..len).rev() {
                let pair = &route.pairs[i - 1];
                let (input_amount, _) = pair.get_input_amount(&token_amount, false)?;
                token_amount = input_amount;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                token_amount.numerator(),
                token_amount.denominator(),
            )?;
            output_amount = CurrencyAmount::from_fractional_amount(
                route.output.clone(),
                amount.numerator(),
                amount.denominator(),
            )?;
        }
        let execution_price = Price::new(
            input_amount.currency.clone(),
            output_amount.currency.clone(),
            input_amount.quotient(),
            output_amount.quotient(),
        );
        let price_impact = compute_price_impact(
            route.clone().mid_price()?,
            input_amount.clone(),
            output_amount.clone(),
        )?;
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
    pub fn exact_in(
        route: Route<TInput, TOutput>,
        amount_in: CurrencyAmount<TInput>,
    ) -> Result<Self> {
        Trade::new(route, amount_in, TradeType::ExactInput)
    }

    /// Constructs an exact out trade with the given amount out and route
    ///
    /// ## Arguments
    ///
    /// * `route`: The route of the exact out trade
    /// * `amount_out`: The amount returned by the trade
    pub fn exact_out(
        route: Route<TInput, TOutput>,
        amount_out: CurrencyAmount<TOutput>,
    ) -> Result<Self> {
        Trade::new(route, amount_out, TradeType::ExactOutput)
    }

    /// Get the minimum amount that must be received from this trade for the given slippage
    /// tolerance
    ///
    /// ## Arguments
    ///
    /// * `slippage_tolerance`: The tolerance of unfavorable slippage from the execution price of
    ///   this trade
    pub fn minimum_amount_out(
        &mut self,
        slippage_tolerance: Percent,
    ) -> Result<CurrencyAmount<TOutput>> {
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
        .map_err(|e| e.into())
    }

    /// Get the maximum amount in that can be spent via this trade for the given slippage tolerance
    ///
    /// ## Arguments
    ///
    /// * `slippage_tolerance`: The tolerance of unfavorable slippage from the execution price of
    ///   this trade
    pub fn maximum_amount_in(
        &mut self,
        slippage_tolerance: Percent,
    ) -> Result<CurrencyAmount<TInput>> {
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
        .map_err(|e| e.into())
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
    pub fn best_trade_exact_in(
        pairs: Vec<Pair>,
        currency_amount_in: CurrencyAmount<TInput>,
        currency_out: TOutput,
        best_trade_options: BestTradeOptions,
        current_pairs: Vec<Pair>,
        next_amount_in: Option<CurrencyAmount<Token>>,
        best_trades: &mut Vec<Self>,
    ) -> Result<&mut Vec<Self>> {
        assert!(!pairs.is_empty(), "PAIRS");
        let max_num_results = best_trade_options.max_num_results.unwrap_or(3);
        let max_hops = best_trade_options.max_hops.unwrap_or(3);
        assert!(max_hops > 0, "MAX_HOPS");
        let amount_in = match next_amount_in {
            Some(amount_in) => {
                assert!(!current_pairs.is_empty(), "INVALID_RECURSION");
                amount_in
            }
            None => currency_amount_in.wrapped()?,
        };
        let token_out = currency_out.wrapped();
        for pair in pairs.iter() {
            // pair irrelevant
            if !pair.token0().equals(&amount_in.currency)
                && !pair.token1().equals(&amount_in.currency)
            {
                continue;
            }
            if pair.reserve1().quotient().is_zero() || pair.reserve0().quotient().is_zero() {
                continue;
            }
            let (amount_out, _) = pair.get_output_amount(&amount_in, false)?;
            // we have arrived at the output token, so this is the final trade of one of the paths
            if amount_out.currency.equals(&token_out) {
                let mut next_pairs = current_pairs.clone();
                next_pairs.push(pair.clone());
                let trade = Self::new(
                    Route::new(
                        next_pairs,
                        currency_amount_in.currency.clone(),
                        currency_out.clone(),
                    ),
                    currency_amount_in.wrapped()?,
                    TradeType::ExactInput,
                )?;
                sorted_insert(best_trades, trade, max_num_results, trade_comparator)?;
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
                    currency_amount_in.clone(),
                    currency_out.clone(),
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
    pub fn worst_execution_price(
        &mut self,
        slippage_tolerance: Percent,
    ) -> Result<Price<TInput, TOutput>> {
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
    pub fn best_trade_exact_out(
        pairs: Vec<Pair>,
        currency_in: TInput,
        currency_amount_out: CurrencyAmount<TOutput>,
        best_trade_options: BestTradeOptions,
        current_pairs: Vec<Pair>,
        next_amount_out: Option<CurrencyAmount<Token>>,
        best_trades: &mut Vec<Self>,
    ) -> Result<&mut Vec<Self>> {
        assert!(!pairs.is_empty(), "PAIRS");
        let max_num_results = best_trade_options.max_num_results.unwrap_or(3);
        let max_hops = best_trade_options.max_hops.unwrap_or(3);
        assert!(max_hops > 0, "MAX_HOPS");
        let amount_out = match next_amount_out {
            Some(amount_out) => {
                assert!(!current_pairs.is_empty(), "INVALID_RECURSION");
                amount_out
            }
            None => currency_amount_out.wrapped()?,
        };
        let token_in = currency_in.wrapped();
        for pair in pairs.iter() {
            // pair irrelevant
            if !pair.token0().equals(&amount_out.currency)
                && !pair.token1().equals(&amount_out.currency)
            {
                continue;
            }
            if pair.reserve1().quotient().is_zero() || pair.reserve0().quotient().is_zero() {
                continue;
            }
            let (amount_in, _) = pair.get_input_amount(&amount_out, false)?;
            // we have arrived at the input token, so this is the first trade of one of the paths
            if amount_in.currency.equals(&token_in) {
                let mut next_pairs = vec![pair.clone()];
                next_pairs.extend(current_pairs.clone());
                let trade = Self::new(
                    Route::new(
                        next_pairs,
                        currency_in.clone(),
                        currency_amount_out.currency.clone(),
                    ),
                    currency_amount_out.wrapped()?,
                    TradeType::ExactOutput,
                )?;
                sorted_insert(best_trades, trade, max_num_results, trade_comparator)?;
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
                    currency_in.clone(),
                    currency_amount_out.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use once_cell::sync::Lazy;
    use uniswap_sdk_core::token;

    static ETHER: Lazy<Ether> = Lazy::new(|| Ether::on_chain(1));
    static TOKEN0: Lazy<Token> =
        Lazy::new(|| token!(1, "0000000000000000000000000000000000000001", 18, "t0"));
    static TOKEN1: Lazy<Token> =
        Lazy::new(|| token!(1, "0000000000000000000000000000000000000002", 18, "t1"));
    static TOKEN2: Lazy<Token> =
        Lazy::new(|| token!(1, "0000000000000000000000000000000000000003", 18, "t2"));
    static TOKEN3: Lazy<Token> =
        Lazy::new(|| token!(1, "0000000000000000000000000000000000000004", 18, "t3"));
    static WETH: Lazy<Token> = Lazy::new(|| ETHER.wrapped());
    static PAIR_0_1: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 1000).unwrap(),
        )
        .unwrap()
    });
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
    static PAIR_WETH_0: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(WETH.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 1000).unwrap(),
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
}
