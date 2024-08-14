use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    /// Indicates that the pair has insufficient reserves for a desired output amount. I.e. the
    /// amount of output cannot be obtained by sending any amount of input.
    #[error("Insufficient reserves")]
    InsufficientReserves,

    /// Indicates that the input amount is too small to produce any amount of output. I.e. the
    /// amount of input sent is less than the price of a single unit of output after fees.
    #[error("Insufficient input amount")]
    InsufficientInputAmount,

    #[error("Token is not part of this pair")]
    TokenNotInPair,

    #[error("Error creating currency amount")]
    CurrencyAmountError,

    #[error("Arithmetic error")]
    ArithmeticError,

    ///Triggers when the Compared values are not equal
    #[error("not equal")]
    NotEqual(),

    #[error("Insufficient liquidity for the operation")]
    InsufficientLiquidity,

    #[error("Liquidity overflow occurred")]
    LiquidityOverflow,

    /// Triggers when The value is incorrect
    #[error("incorrect")]
    Incorrect(),

    /// Indicates
    #[error("incorrect price calculation")]
    PriceCalculationFailed,

    #[error("Wrapping operation failed")]
    WrappingFailed,
}
