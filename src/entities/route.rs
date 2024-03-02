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
    /// Creates an instance of route.
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

        let mut path: Vec<Token> = vec![wrapped_input];
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
