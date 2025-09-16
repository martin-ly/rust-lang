//! async-std 示例与对比
use std::time::Duration;

/// 使用 async-std 计时器的简单示例（若启用 async-std 依赖可替换 tokio）
pub async fn demo_sleep() -> u64 {
    // 此处为占位，项目当前未引入 async-std 依赖，保持接口以便后续对比
    tokio::time::sleep(Duration::from_millis(1)).await;
    1
}
