use uniswap_sdk_core::error::Error as CoreError;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error {
    /// Indicates that the pair has insufficient reserves for a desired output amount. I.e. the
    /// amount of output cannot be obtained by sending any amount of input.
    #[cfg_attr(feature = "std", error("Insufficient reserves"))]
    InsufficientReserves,

    /// Indicates that the input amount is too small to produce any amount of output. I.e. the
    /// amount of input sent is less than the price of a single unit of output after fees.
    #[cfg_attr(feature = "std", error("Insufficient input amount"))]
    InsufficientInputAmount,

    #[cfg_attr(feature = "std", error("Insufficient liquidity"))]
    InsufficientLiquidity,

    #[cfg_attr(feature = "std", error("Invalid token"))]
    InvalidToken,

    #[cfg_attr(feature = "std", error("{0}"))]
    Core(CoreError),
}

impl From<CoreError> for Error {
    #[inline]
    fn from(error: CoreError) -> Self {
        Error::Core(error)
    }
}
