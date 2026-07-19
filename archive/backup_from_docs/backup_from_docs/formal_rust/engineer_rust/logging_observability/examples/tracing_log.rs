// 日志与可观测性：tracing结构化日志示例
// Logging & Observability: Tracing Structured Log Example
use tracing::info;

fn main() {
    tracing_subscriber::fmt::init();
    info!(user_id = 42, action = "login", "User login event");
} 