//! Candle 集成草案模块（可选特性 `candle` 启用时有效）

#[cfg(feature = "candle")]
pub mod candle_compat {
    pub fn is_available() -> bool {
        true
    }
}
