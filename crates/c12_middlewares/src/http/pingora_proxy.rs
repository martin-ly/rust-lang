#[cfg(feature = "proxy-nix")]
pub struct PingoraProxy;

#[cfg(feature = "proxy-nix")]
impl PingoraProxy {
    // 占位：Pingora 需要较多样板与运行时初始化，这里暂不提供完整实现
    pub async fn start(_addr: &str) -> anyhow::Result<()> {
        Ok(())
    }
}
