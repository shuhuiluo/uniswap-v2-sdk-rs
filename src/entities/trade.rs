use crate::prelude::Route;
use uniswap_sdk_core::prelude::*;

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
