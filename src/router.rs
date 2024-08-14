use crate::{
    errors::Error,
    prelude::{Pair, Route, Trade},
};
use alloy_primitives::ChainId;
use anyhow::Result;
use uniswap_sdk_core::prelude::*;

/// Represents a router that can find the best trade path and execute trades
#[derive(Clone, PartialEq, Debug)]
pub struct Router {
    pub pairs: Vec<Pair>,
}

impl Router {
    /// Creates an instance of [`Router`].
    ///
    /// ## Arguments
    ///
    /// * `pairs`: An array of [`Pair`] objects available for trading
    pub fn new(pairs: Vec<Pair>) -> Self {
        assert!(!pairs.is_empty(), "PAIRS");
        let chain_id = pairs[0].chain_id();
        assert!(
            pairs.iter().all(|pair| pair.chain_id() == chain_id),
            "CHAIN_IDS"
        );

        Router { pairs }
    }

    pub fn chain_id(&self) -> ChainId {
        self.pairs[0].chain_id()
    }

    /// best trade path for a given input and output token
    ///
    /// ## Arguments
    ///
    /// * `input_amount`: The input amount
    /// * `output_token`: The output token
    /// * `max_hops`: The maximum number of hops allowed in the trade path
    pub fn find_best_path<TInput, TOutput>(
        &self,
        input_amount: CurrencyAmount<TInput>,
        output_token: TOutput,
        max_hops: usize,
    ) -> Result<Option<Trade<TInput, TOutput>>>
    where
        TInput: CurrencyTrait,
        TOutput: CurrencyTrait,
    {
        let input_token = input_amount.currency.wrapped();
        let output_token_wrapped = output_token.wrapped();

        if max_hops == 0 {
            return Ok(None);
        }

        // Check for direct pair
        if let Some(direct_pair) = self.find_pair(&input_token, &output_token_wrapped) {
            let route = Route::new(
                vec![direct_pair.clone()],
                input_amount.currency.clone(),
                output_token,
            );
            let trade = Trade::exact_in(route, input_amount.clone())?;
            return Ok(Some(trade));
        }

        // Check multi-hop paths
        let mut best_trade: Option<Trade<TInput, TOutput>> = None;

        for i in 0..self.pairs.len() {
            let pair = &self.pairs[i];
            if !pair.involves_token(&input_token) {
                continue;
            }

            let output_of_first_pair = if pair.token0().equals(&input_token) {
                pair.token1()
            } else {
                pair.token0()
            };

            if output_of_first_pair.equals(&output_token_wrapped) && max_hops > 1 {
                let route = Route::new(
                    vec![pair.clone()],
                    input_amount.currency.clone(),
                    output_token.clone(),
                );
                let trade = Trade::exact_in(route, input_amount.clone())?;
                best_trade = Some(trade);
                break;
            } else if max_hops > 1 {
                let remaining_hops = max_hops - 1;
                let remaining_pairs = self.pairs[i + 1..].to_vec();
                let router = Router::new(remaining_pairs);
                if let Some(best_remaining_trade) = router.find_best_path(
                    CurrencyAmount::from_raw_amount(
                        output_of_first_pair.clone(),
                        input_amount.quotient(),
                    )
                    .map_err(|_| Error::WrappingFailed)?,
                    output_token.clone(),
                    remaining_hops,
                )? {
                    let mut combined_path = vec![pair.clone()];
                    combined_path.extend(best_remaining_trade.route.pairs.clone());
                    let route = Route::new(
                        combined_path,
                        input_amount.currency.clone(),
                        output_token.clone(),
                    );
                    let trade = Trade::exact_in(route, input_amount.clone())?;

                    if best_trade.is_none()
                        || trade.output_amount.to_decimal()
                            > best_trade.as_ref().unwrap().output_amount.to_decimal()
                    {
                        best_trade = Some(trade);
                    }
                }
            }
        }

        Ok(best_trade)
    }

    fn find_pair(&self, token0: &Token, token1: &Token) -> Option<&Pair> {
        self.pairs
            .iter()
            .find(|pair| pair.involves_token(token0) && pair.involves_token(token1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use uniswap_sdk_core::token;

    fn create_token(address: &str, decimals: u8, symbol: &str) -> Token {
        token!(1, address, decimals, symbol)
    }

    #[test]
    fn test_router_creation() {
        let token_a = create_token("0x1000000000000000000000000000000000000000", 18, "A");
        let token_b = create_token("0x2000000000000000000000000000000000000000", 18, "B");
        let pair = Pair::new(
            CurrencyAmount::from_raw_amount(token_a.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(token_b.clone(), 1000).unwrap(),
        )
        .unwrap();

        let router = Router::new(vec![pair]);
        assert_eq!(router.chain_id(), ChainId::from(1_u64));
    }

    #[test]
    fn test_find_best_path_direct() {
        let token_a = create_token("0x1000000000000000000000000000000000000000", 18, "A");
        let token_b = create_token("0x2000000000000000000000000000000000000000", 18, "B");
        let pair = Pair::new(
            CurrencyAmount::from_raw_amount(token_a.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(token_b.clone(), 1000).unwrap(),
        )
        .unwrap();

        let router = Router::new(vec![pair]);
        let amount_in = CurrencyAmount::from_raw_amount(token_a.clone(), 100).unwrap();
        let best_trade = router
            .find_best_path(amount_in, token_b.clone(), 2)
            .unwrap();

        assert!(best_trade.is_some());
        assert_eq!(best_trade.unwrap().route.pairs.len(), 1);
    }

    #[test]
    fn test_find_best_path_multi_hop() {
        let token_a = create_token("0x1000000000000000000000000000000000000000", 18, "A");
        let token_b = create_token("0x2000000000000000000000000000000000000000", 18, "B");
        let token_c = create_token("0x3000000000000000000000000000000000000000", 18, "C");

        let pair_ab = Pair::new(
            CurrencyAmount::from_raw_amount(token_a.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(token_b.clone(), 1000).unwrap(),
        )
        .unwrap();
        let pair_bc = Pair::new(
            CurrencyAmount::from_raw_amount(token_b.clone(), 1000).unwrap(),
            CurrencyAmount::from_raw_amount(token_c.clone(), 1000).unwrap(),
        )
        .unwrap();

        let router = Router::new(vec![pair_ab, pair_bc]);
        let amount_in = CurrencyAmount::from_raw_amount(token_a.clone(), 100).unwrap();
        let best_trade = router
            .find_best_path(amount_in, token_c.clone(), 2)
            .unwrap();

        assert!(best_trade.is_some());
        assert_eq!(best_trade.unwrap().route.pairs.len(), 2);
    }
}
