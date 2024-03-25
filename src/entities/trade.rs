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
        let mut token_amounts: Vec<CurrencyAmount<Token>> = Vec::with_capacity(len);
        let input_amount: CurrencyAmount<TInput>;
        let output_amount: CurrencyAmount<TOutput>;
        if trade_type == TradeType::ExactInput {
            assert!(amount.currency.equals(&route.input), "INPUT");
            token_amounts[0] = amount.wrapped()?;
            for i in 0..len - 1 {
                let pair = &route.pairs[i];
                let (output_amount, _) = pair.get_output_amount(&token_amounts[i], false)?;
                token_amounts[i + 1] = output_amount;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                amount.numerator(),
                amount.denominator(),
            )?;
            output_amount = CurrencyAmount::from_fractional_amount(
                route.output.clone(),
                token_amounts[len - 1].numerator(),
                token_amounts[len - 1].denominator(),
            )?;
        } else {
            assert!(amount.currency.equals(&route.output), "OUTPUT");
            token_amounts[len - 1] = amount.wrapped()?;
            for i in (1..len).rev() {
                let pair = &route.pairs[i - 1];
                let (input_amount, _) = pair.get_input_amount(&token_amounts[i], false)?;
                token_amounts[i - 1] = input_amount;
            }
            input_amount = CurrencyAmount::from_fractional_amount(
                route.input.clone(),
                token_amounts[0].numerator(),
                token_amounts[0].denominator(),
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

    //   /**
    //    * Given a list of pairs, and a fixed amount in, returns the top `maxNumResults` trades
    //      that go from an input token
    //    * amount to an output token, making at most `maxHops` hops.
    //    * Note this does not consider aggregation, as routes are linear. It's possible a better
    //      route exists by splitting
    //    * the amount in among multiple routes.
    //    * @param pairs the pairs to consider in finding the best trade
    //    * @param nextAmountIn exact amount of input currency to spend
    //    * @param currencyOut the desired currency out
    //    * @param maxNumResults maximum number of results to return
    //    * @param maxHops maximum number of hops a returned trade can make, e.g. 1 hop goes through
    //      a single pair
    //    * @param currentPairs used in recursion; the current list of pairs
    //    * @param currencyAmountIn used in recursion; the original value of the currencyAmountIn
    //      parameter
    //    * @param bestTrades used in recursion; the current list of best trades
    //    */
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
}
