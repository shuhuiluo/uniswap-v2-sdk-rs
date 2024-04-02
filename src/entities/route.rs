use crate::prelude::Pair;
use alloy_primitives::ChainId;
use anyhow::Result;
use uniswap_sdk_core::prelude::*;

/// Represents a list of pairs through which a swap can occur
#[derive(Clone, PartialEq, Debug)]
pub struct Route<TInput: CurrencyTrait, TOutput: CurrencyTrait> {
    pub pairs: Vec<Pair>,
    pub path: Vec<Token>,
    /// The input token
    pub input: TInput,
    /// The output token
    pub output: TOutput,
    _mid_price: Option<Price<TInput, TOutput>>,
}

impl<TInput: CurrencyTrait, TOutput: CurrencyTrait> Route<TInput, TOutput> {
    /// Creates an instance of [`Route`].
    ///
    /// ## Arguments
    ///
    /// * `pairs`: An array of [`Pair`] objects, ordered by the route the swap will take
    /// * `input`: The input token
    /// * `output`: The output token
    pub fn new(pairs: Vec<Pair>, input: TInput, output: TOutput) -> Self {
        assert!(!pairs.is_empty(), "PAIRS");
        let chain_id = pairs[0].chain_id();
        assert!(
            pairs.iter().all(|pair| pair.chain_id() == chain_id),
            "CHAIN_IDS"
        );

        let wrapped_input = input.wrapped();
        assert!(pairs[0].involves_token(&wrapped_input), "INPUT");
        assert!(
            pairs.last().unwrap().involves_token(&output.wrapped()),
            "OUTPUT"
        );

        let mut path: Vec<Token> = Vec::with_capacity(pairs.len() + 1);
        path.push(wrapped_input);
        for (i, pair) in pairs.iter().enumerate() {
            let current_input = &path[i];
            assert!(
                current_input.equals(pair.token0()) || current_input.equals(pair.token1()),
                "PATH"
            );
            let output = if current_input.equals(pair.token0()) {
                pair.token1()
            } else {
                pair.token0()
            };
            path.push(output.clone());
        }
        assert!(path.last().unwrap().equals(&output.wrapped()), "PATH");

        Route {
            pairs,
            path,
            input,
            output,
            _mid_price: None,
        }
    }

    pub fn chain_id(&self) -> ChainId {
        self.pairs[0].chain_id()
    }

    /// Returns the mid price of the route
    pub fn mid_price(&mut self) -> Result<Price<TInput, TOutput>> {
        if let Some(mid_price) = &self._mid_price {
            return Ok(mid_price.clone());
        }
        let mut price: Price<Token, Token>;
        let mut next_input: &Token;
        if self.pairs[0].token0().equals(&self.input.wrapped()) {
            price = self.pairs[0].token0_price();
            next_input = self.pairs[0].token1();
        } else {
            price = self.pairs[0].token1_price();
            next_input = self.pairs[0].token0();
        }
        for pair in self.pairs[1..].iter() {
            if next_input.equals(pair.token0()) {
                next_input = pair.token1();
                price = price.multiply(&pair.token0_price())?;
            } else {
                next_input = pair.token0();
                price = price.multiply(&pair.token1_price())?;
            }
        }
        self._mid_price = Some(Price::new(
            self.input.clone(),
            self.output.clone(),
            price.denominator(),
            price.numerator(),
        ));
        Ok(self._mid_price.clone().unwrap())
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
    static WETH: Lazy<Token> = Lazy::new(|| ETHER.wrapped());
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
        assert_eq!(route.path, vec![TOKEN0.clone(), TOKEN1.clone()]);
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
