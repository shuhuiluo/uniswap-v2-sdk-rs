use crate::prelude::{Error, Pair};
use alloy_primitives::ChainId;
use uniswap_sdk_core::prelude::*;

/// Represents a list of pairs through which a swap can occur
#[derive(Clone, PartialEq, Debug)]
pub struct Route<TInput: BaseCurrency, TOutput: BaseCurrency> {
    pub pairs: Vec<Pair>,
    /// The input token
    pub input: TInput,
    /// The output token
    pub output: TOutput,
    _mid_price: Option<Price<TInput, TOutput>>,
}

impl<TInput: BaseCurrency, TOutput: BaseCurrency> Route<TInput, TOutput> {
    /// Creates an instance of [`Route`].
    ///
    /// ## Arguments
    ///
    /// * `pairs`: An array of [`Pair`] objects, ordered by the route the swap will take
    /// * `input`: The input token
    /// * `output`: The output token
    #[inline]
    pub fn new(pairs: Vec<Pair>, input: TInput, output: TOutput) -> Self {
        assert!(!pairs.is_empty(), "PAIRS");
        let chain_id = pairs[0].chain_id();
        assert!(
            pairs.iter().all(|pair| pair.chain_id() == chain_id),
            "CHAIN_IDS"
        );

        let wrapped_input = input.wrapped();
        assert!(pairs[0].involves_token(wrapped_input), "INPUT");
        let wrapped_output = output.wrapped();
        assert!(
            pairs.last().unwrap().involves_token(wrapped_output),
            "OUTPUT"
        );

        let mut current_input_token = wrapped_input;
        for pair in &pairs {
            current_input_token = if current_input_token.equals(pair.token0()) {
                pair.token1()
            } else if current_input_token.equals(pair.token1()) {
                pair.token0()
            } else {
                panic!("PATH")
            };
        }
        assert!(current_input_token.equals(wrapped_output), "PATH");

        Route {
            pairs,
            input,
            output,
            _mid_price: None,
        }
    }

    #[inline]
    pub fn path(&self) -> Vec<Token> {
        let mut path: Vec<Token> = Vec::with_capacity(self.pairs.len() + 1);
        path.push(self.input.wrapped().clone());
        for (i, pair) in self.pairs.iter().enumerate() {
            let output = if path[i].equals(pair.token0()) {
                pair.token1()
            } else {
                pair.token0()
            };
            path.push(output.clone());
        }
        path
    }

    #[inline]
    pub fn chain_id(&self) -> ChainId {
        self.pairs[0].chain_id()
    }

    /// Returns the mid price of the route
    #[inline]
    pub fn mid_price(&self) -> Result<Price<TInput, TOutput>, Error> {
        let mut price = self.pairs[0].price_of(self.input.wrapped())?;
        for pair in &self.pairs[1..] {
            price = price.multiply(&pair.price_of(&price.quote_currency)?)?;
        }
        Ok(Price::new(
            self.input.clone(),
            self.output.clone(),
            price.denominator,
            price.numerator,
        ))
    }

    /// Returns the mid price of the route
    #[inline]
    pub fn mid_price_cached(&mut self) -> Result<Price<TInput, TOutput>, Error> {
        if let Some(mid_price) = &self._mid_price {
            return Ok(mid_price.clone());
        }
        let mid_price = self.mid_price()?;
        self._mid_price = Some(mid_price.clone());
        Ok(mid_price)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;

    static PAIR_0_1: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 200).unwrap(),
        )
        .unwrap()
    });
    static PAIR_0_WETH: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN0.clone(), 100).unwrap(),
            CurrencyAmount::from_raw_amount(WETH.clone(), 100).unwrap(),
        )
        .unwrap()
    });
    static PAIR_1_WETH: Lazy<Pair> = Lazy::new(|| {
        Pair::new(
            CurrencyAmount::from_raw_amount(TOKEN1.clone(), 175).unwrap(),
            CurrencyAmount::from_raw_amount(WETH.clone(), 100).unwrap(),
        )
        .unwrap()
    });

    #[test]
    fn constructs_a_path_from_the_tokens() {
        let route = Route::new(vec![PAIR_0_1.clone()], TOKEN0.clone(), TOKEN1.clone());
        assert_eq!(route.pairs, vec![PAIR_0_1.clone()]);
        assert_eq!(route.path(), vec![TOKEN0.clone(), TOKEN1.clone()]);
        assert_eq!(route.input, TOKEN0.clone());
        assert_eq!(route.output, TOKEN1.clone());
        assert_eq!(route.chain_id(), 1);
    }

    #[test]
    fn can_have_a_token_as_both_input_and_output() {
        let route = Route::new(
            vec![PAIR_0_WETH.clone(), PAIR_0_1.clone(), PAIR_1_WETH.clone()],
            WETH.clone(),
            WETH.clone(),
        );
        assert_eq!(
            route.pairs,
            vec![PAIR_0_WETH.clone(), PAIR_0_1.clone(), PAIR_1_WETH.clone()]
        );
        assert_eq!(route.input, WETH.clone());
        assert_eq!(route.output, WETH.clone());
    }

    #[test]
    fn supports_ether_input() {
        let route = Route::new(vec![PAIR_0_WETH.clone()], ETHER.clone(), TOKEN0.clone());
        assert_eq!(route.pairs, vec![PAIR_0_WETH.clone()]);
        assert_eq!(route.input, ETHER.clone());
        assert_eq!(route.output, TOKEN0.clone());
    }

    #[test]
    fn supports_ether_output() {
        let route = Route::new(vec![PAIR_0_WETH.clone()], TOKEN0.clone(), ETHER.clone());
        assert_eq!(route.pairs, vec![PAIR_0_WETH.clone()]);
        assert_eq!(route.input, TOKEN0.clone());
        assert_eq!(route.output, ETHER.clone());
    }
}
