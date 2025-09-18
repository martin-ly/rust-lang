//! DFDx 集成草案模块（可选特性 `dfdx` 启用时有效）

#[cfg(feature = "dfdx")]
pub mod dfdx_compat {
    pub fn is_available() -> bool {
        true
    }
}
