use uniswap_sdk_core::error::Error as CoreError;

#[derive(Clone, Copy, Debug, thiserror::Error)]
pub enum Error {
    /// Indicates that the pair has insufficient reserves for a desired output amount. I.e. the
    /// amount of output cannot be obtained by sending any amount of input.
    #[error("Insufficient reserves")]
    InsufficientReserves,

    /// Indicates that the input amount is too small to produce any amount of output. I.e. the
    /// amount of input sent is less than the price of a single unit of output after fees.
    #[error("Insufficient input amount")]
    InsufficientInputAmount,

    #[error("Invalid token")]
    InvalidToken,

    #[error("{0}")]
    Core(CoreError),

    #[error("Insufficient liquidity")]
    InsufficientLiquidity,
}

impl From<CoreError> for Error {
    fn from(error: CoreError) -> Self {
        Error::Core(error)
    }
}
