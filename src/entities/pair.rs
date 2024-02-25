use crate::{constants::*, errors::Error};
use alloy_primitives::keccak256;
use alloy_sol_types::SolValue;
use anyhow::{anyhow, Result};
use uniswap_sdk_core::{prelude::*, token};

pub fn compute_pair_address(factory: Address, token_a: Address, token_b: Address) -> Address {
    let (token_0, token_1) = if token_a < token_b {
        (token_a, token_b)
    } else {
        (token_b, token_a)
    };
    factory.create2(
        keccak256((token_0, token_1).abi_encode_packed()),
        INIT_CODE_HASH,
    )
}

#[derive(Clone, PartialEq, Debug)]
pub struct Pair {
    pub liquidity_token: Token,
    token_amounts: [CurrencyAmount<Token>; 2],
}

impl Pair {
    pub fn get_address(token_a: &Token, token_b: &Token) -> Address {
        let factory_address = FACTORY_ADDRESS_MAP
            .get(&token_a.chain_id)
            .unwrap_or(&FACTORY_ADDRESS);
        compute_pair_address(*factory_address, token_a.address(), token_b.address())
    }

    pub fn new(
        currency_amount_a: CurrencyAmount<Token>,
        token_amount_b: CurrencyAmount<Token>,
    ) -> Result<Self> {
        let token_amounts = if currency_amount_a
            .currency
            .sorts_before(&token_amount_b.currency)?
        {
            [currency_amount_a, token_amount_b]
        } else {
            [token_amount_b, currency_amount_a]
        };
        let liquidity_token = token!(
            token_amounts[0].currency.chain_id,
            Pair::get_address(&token_amounts[0].currency, &token_amounts[1].currency),
            18,
            "UNI-V2",
            "Uniswap V2"
        );
        Ok(Self {
            liquidity_token,
            token_amounts,
        })
    }

    /// Returns true if the token is either token0 or token1
    ///
    /// ## Arguments
    ///
    /// * `token`: token to check
    pub fn involves_token(&self, token: &Token) -> bool {
        token.equals(&self.token_amounts[0].currency)
            || token.equals(&self.token_amounts[1].currency)
    }

    /// Returns the current mid price of the pair in terms of token0, i.e. the ratio of reserve1 to reserve0
    pub fn token0_price(&self) -> Result<Price<Token, Token>> {
        let result = self.token_amounts[1].divide(&self.token_amounts[0])?;
        Ok(Price::new(
            self.token0().clone(),
            self.token1().clone(),
            result.denominator(),
            result.numerator(),
        ))
    }

    /// Returns the current mid price of the pair in terms of token1, i.e. the ratio of reserve0 to reserve1
    pub fn token1_price(&self) -> Result<Price<Token, Token>> {
        let result = self.token_amounts[0].divide(&self.token_amounts[1])?;
        Ok(Price::new(
            self.token1().clone(),
            self.token0().clone(),
            result.denominator(),
            result.numerator(),
        ))
    }

    /// Return the price of the given token in terms of the other token in the pair.
    ///
    /// ## Arguments
    ///
    /// * `token`: token to return price of
    pub fn price_of(&self, token: &Token) -> Result<Price<Token, Token>> {
        if self.involves_token(token) {
            if token.equals(self.token0()) {
                self.token0_price()
            } else {
                self.token1_price()
            }
        } else {
            Err(anyhow!("TOKEN"))
        }
    }

    pub fn chain_id(&self) -> u64 {
        self.token0().chain_id
    }

    pub fn token0(&self) -> &Token {
        &self.token_amounts[0].currency
    }

    pub fn token1(&self) -> &Token {
        &self.token_amounts[1].currency
    }

    pub fn reserve0(&self) -> &CurrencyAmount<Token> {
        &self.token_amounts[0]
    }

    pub fn reserve1(&self) -> &CurrencyAmount<Token> {
        &self.token_amounts[1]
    }

    pub fn reserve_of(&self, token: &Token) -> Result<&CurrencyAmount<Token>> {
        if self.involves_token(token) {
            Ok(if token.equals(self.token0()) {
                self.reserve0()
            } else {
                self.reserve1()
            })
        } else {
            Err(anyhow!("TOKEN"))
        }
    }

    pub fn get_output_amount(
        &self,
        input_amount: &CurrencyAmount<Token>,
        calculate_fot_fees: bool,
    ) -> Result<(CurrencyAmount<Token>, Self)> {
        if !self.involves_token(&input_amount.currency) {
            return Err(anyhow!("TOKEN"));
        }
        if self.reserve0().quotient().is_zero() || self.reserve1().quotient().is_zero() {
            return Err(Error::InsufficientReserves.into());
        }
        let input_reserve = self.reserve_of(&input_amount.currency)?;
        let output_reserve = self.reserve_of(if input_amount.currency.equals(self.token0()) {
            self.token1()
        } else {
            self.token0()
        })?;

        let percent_after_sell_fees = if calculate_fot_fees {
            self.derive_percent_after_sell_fees(input_amount)?
        } else {
            ZERO_PERCENT.clone()
        };
        let input_amount_after_tax = if percent_after_sell_fees > ZERO_PERCENT.clone() {
            CurrencyAmount::from_raw_amount(
                input_amount.currency.clone(),
                (percent_after_sell_fees.as_fraction() * input_amount.as_fraction()).quotient(),
            )?
        } else {
            input_amount.clone()
        };

        let input_amount_with_fee_and_after_tax = input_amount_after_tax.quotient() * _997.clone();
        let numerator = &input_amount_with_fee_and_after_tax * output_reserve.quotient();
        let denominator =
            input_reserve.quotient() * _1000.clone() + &input_amount_with_fee_and_after_tax;
        let output_amount = CurrencyAmount::from_raw_amount(
            if input_amount.currency.equals(self.token0()) {
                self.token1().clone()
            } else {
                self.token0().clone()
            },
            numerator / denominator,
        )?;

        if output_amount.quotient().is_zero() {
            return Err(Error::InsufficientInputAmount.into());
        }

        let percent_after_buy_fees = if calculate_fot_fees {
            self.derive_percent_after_buy_fees(&output_amount)?
        } else {
            ZERO_PERCENT.clone()
        };
        let output_amount_after_tax = if percent_after_buy_fees > ZERO_PERCENT.clone() {
            CurrencyAmount::from_raw_amount(
                output_amount.currency.clone(),
                (percent_after_buy_fees.as_fraction() * output_amount.as_fraction()).quotient(),
            )?
        } else {
            output_amount.clone()
        };
        if output_amount_after_tax.quotient().is_zero() {
            return Err(Error::InsufficientInputAmount.into());
        }

        let pair = Self::new(
            input_reserve.add(&input_amount_after_tax)?,
            output_reserve.subtract(&output_amount_after_tax)?,
        )?;
        Ok((output_amount_after_tax, pair))
    }

    pub fn get_input_amount(
        &self,
        output_amount: &CurrencyAmount<Token>,
        calculate_fot_fees: bool,
    ) -> Result<(CurrencyAmount<Token>, Self)> {
        if !self.involves_token(&output_amount.currency) {
            return Err(anyhow!("TOKEN"));
        }
        let percent_after_buy_fees = if calculate_fot_fees {
            self.derive_percent_after_buy_fees(output_amount)?
        } else {
            ZERO_PERCENT.clone()
        };
        let output_amount_before_tax = if percent_after_buy_fees > ZERO_PERCENT.clone() {
            CurrencyAmount::from_raw_amount(
                output_amount.currency.clone(),
                (output_amount.as_fraction() / percent_after_buy_fees.as_fraction()).quotient()
                    + BigInt::from(1),
            )?
        } else {
            output_amount.clone()
        };

        if self.reserve0().quotient().is_zero()
            || self.reserve1().quotient().is_zero()
            || output_amount.quotient() >= self.reserve_of(&output_amount.currency)?.quotient()
            || output_amount_before_tax.quotient()
                >= self.reserve_of(&output_amount.currency)?.quotient()
        {
            return Err(Error::InsufficientReserves.into());
        }

        let output_reserve = self.reserve_of(&output_amount.currency)?;
        let input_reserve = self.reserve_of(if output_amount.currency.equals(self.token0()) {
            self.token1()
        } else {
            self.token0()
        })?;

        let numerator =
            input_reserve.quotient() * output_amount_before_tax.quotient() * _1000.clone();
        let denominator =
            (output_reserve.quotient() - output_amount_before_tax.quotient()) * _997.clone();
        let input_amount = CurrencyAmount::from_raw_amount(
            if output_amount.currency.equals(self.token0()) {
                self.token1().clone()
            } else {
                self.token0().clone()
            },
            numerator / denominator + BigInt::from(1),
        )?;

        let percent_after_sell_fees = if calculate_fot_fees {
            self.derive_percent_after_sell_fees(&input_amount)?
        } else {
            ZERO_PERCENT.clone()
        };
        let input_amount_before_tax = if percent_after_sell_fees > ZERO_PERCENT.clone() {
            CurrencyAmount::from_raw_amount(
                input_amount.currency.clone(),
                (input_amount.as_fraction() / percent_after_sell_fees.as_fraction()).quotient()
                    + BigInt::from(1),
            )?
        } else {
            input_amount.clone()
        };

        let pair = Self::new(
            input_reserve.add(&input_amount)?,
            output_reserve.subtract(output_amount)?,
        )?;
        Ok((input_amount_before_tax, pair))
    }

    pub fn get_liquidity_minted(
        &self,
        total_supply: &CurrencyAmount<Token>,
        token_amount_a: &CurrencyAmount<Token>,
        token_amount_b: &CurrencyAmount<Token>,
    ) -> Result<CurrencyAmount<Token>> {
        if !total_supply.currency.equals(&self.liquidity_token) {
            return Err(anyhow!("LIQUIDITY"));
        }
        let token_amounts = if token_amount_a
            .currency
            .sorts_before(&token_amount_b.currency)?
        {
            (token_amount_a, token_amount_b)
        } else {
            (token_amount_b, token_amount_a)
        };
        if !token_amounts.0.currency.equals(self.token0())
            || !token_amounts.1.currency.equals(self.token1())
        {
            return Err(anyhow!("TOKEN"));
        }

        let liquidity = if total_supply.quotient().is_zero() {
            (token_amounts.0.quotient() * token_amounts.1.quotient()).sqrt()
                - MINIMUM_LIQUIDITY.clone()
        } else {
            let amount0 =
                (token_amounts.0.quotient() * total_supply.quotient()) / self.reserve0().quotient();
            let amount1 =
                (token_amounts.1.quotient() * total_supply.quotient()) / self.reserve1().quotient();
            amount0.min(amount1)
        };
        if liquidity.is_zero() {
            return Err(Error::InsufficientInputAmount.into());
        }
        CurrencyAmount::from_raw_amount(self.liquidity_token.clone(), liquidity)
            .map_err(|_| anyhow!("LIQUIDITY"))
    }

    pub fn get_liquidity_value(
        &self,
        token: &Token,
        total_supply: &CurrencyAmount<Token>,
        liquidity: &CurrencyAmount<Token>,
        fee_on: bool,
        k_last: Option<BigInt>,
    ) -> Result<CurrencyAmount<Token>> {
        if !self.involves_token(token) {
            return Err(anyhow!("TOKEN"));
        }
        if !total_supply.currency.equals(&self.liquidity_token) {
            return Err(anyhow!("TOTAL_SUPPLY"));
        }
        if !liquidity.currency.equals(&self.liquidity_token) {
            return Err(anyhow!("LIQUIDITY"));
        }
        if liquidity.quotient() > total_supply.quotient() {
            return Err(anyhow!("LIQUIDITY"));
        }

        let total_supply_adjusted = if !fee_on {
            total_supply.clone()
        } else {
            if let Some(k_last) = k_last {
                if k_last.is_zero() {
                    total_supply.clone()
                } else {
                    let root_k = (self.reserve0().quotient() * self.reserve1().quotient()).sqrt();
                    let root_k_last = k_last.sqrt();
                    if root_k > root_k_last {
                        let numerator = total_supply.quotient() * (&root_k - &root_k_last);
                        let denominator = root_k * FIVE.clone() + root_k_last;
                        let fee_liquidity = numerator / denominator;
                        total_supply.add(&CurrencyAmount::from_raw_amount(
                            self.liquidity_token.clone(),
                            fee_liquidity,
                        )?)?
                    } else {
                        total_supply.clone()
                    }
                }
            } else {
                return Err(anyhow!("K_LAST"));
            }
        };

        let result = liquidity.quotient() * self.reserve_of(token)?.quotient()
            / total_supply_adjusted.quotient();
        CurrencyAmount::from_raw_amount(token.clone(), result).map_err(|_| anyhow!("TOKEN"))
    }

    fn derive_percent_after_sell_fees(
        &self,
        input_amount: &CurrencyAmount<Token>,
    ) -> Result<Percent> {
        let sell_fee_bips = if self.token0().equals(&input_amount.currency.wrapped()) {
            self.token0().meta.sell_fee_bps.clone()
        } else {
            self.token1().meta.sell_fee_bps.clone()
        }
        .unwrap_or(BigUint::zero());
        if sell_fee_bips > BigUint::zero() {
            Ok(ONE_HUNDRED_PERCENT.clone() - Percent::new(sell_fee_bips, BASIS_POINTS.clone()))
        } else {
            Ok(ZERO_PERCENT.clone())
        }
    }

    fn derive_percent_after_buy_fees(
        &self,
        output_amount: &CurrencyAmount<Token>,
    ) -> Result<Percent> {
        let buy_fee_bips = if self.token0().equals(&output_amount.currency.wrapped()) {
            self.token0().meta.buy_fee_bps.clone()
        } else {
            self.token1().meta.buy_fee_bps.clone()
        }
        .unwrap_or(BigUint::zero());
        if buy_fee_bips > BigUint::zero() {
            Ok(ONE_HUNDRED_PERCENT.clone() - Percent::new(buy_fee_bips, BASIS_POINTS.clone()))
        } else {
            Ok(ZERO_PERCENT.clone())
        }
    }
}
