# 系统基础设施场景

> **Bloom 层级**: 应用 → 分析
> **来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)** · **来源: [tokio](https://tokio.rs/) / [hyper](https://hyper.rs/) / axum 生态** ✅

---

## 场景 1：高性能反向代理

**背景**: 替代 Nginx，处理 100K+ RPS，低延迟。

**约束**:

- 延迟: p99 < 1ms
- 连接: 100K+ 并发
- 协议: HTTP/1.1, HTTP/2, HTTP/3

**Rust 方案**:

```rust
use axum::{Router, routing::get};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/api/:service/*path", get(proxy_request));

    // HTTP/2 + TLS
    let tls_config = rustls::ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(cert, key)
        .unwrap();

    let listener = TcpListener::bind("0.0.0.0:443").await.unwrap();
    axum::serve(listener, app)
        .await
        .unwrap();
}
```

**关键决策**:

- 运行时: tokio（work-stealing，高并发）
- HTTP: axum + hyper
- TLS: rustls（内存安全替代 OpenSSL）

---

## 场景 2：分布式键值存储

**背景**: 类 etcd 的共识存储，Raft 协议。

**约束**:

- 一致性: 线性一致
- 可用性: 5 节点容忍 2 故障
- 存储: 持久化 WAL + snapshot

**Rust 方案**:

```rust
use raft::{Config, Raft, storage::MemStorage};

struct KvStore {
    raft: Raft<MemStorage>,
    db: sled::Db,
}

impl KvStore {
    async fn propose(&mut self, cmd: Command) -> Result<()> {
        let data = bincode::serialize(&cmd)?;
        self.raft.propose(vec![], data).await?;
        Ok(())
    }

    fn apply(&mut self, entry: Entry) -> Result<()> {
        let cmd: Command = bincode::deserialize(&entry.data)?;
        match cmd {
            Command::Set { key, value } => {
                self.db.insert(key, value)?;
            }
            Command::Delete { key } => {
                self.db.remove(key)?;
            }
        }
        Ok(())
    }
}
```

**关键决策**:

- 共识: `raft` crate 或 `openraft`
- 存储: `sled`（嵌入式 KV）或 `rocksdb`
- 序列化: `bincode` / `prost`

---

## 场景 3：CLI 开发工具

**背景**: 替代 Node.js 构建工具，快速启动。

**约束**:

- 启动: < 50ms
- 跨平台: Linux/macOS/Windows
- 插件: WASM 扩展

**Rust 方案**:

```rust
use clap::Parser;
use anyhow::Result;

#[derive(Parser)]
#[command(name = "mytool")]
struct Cli {
    #[arg(short, long)]
    config: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Build { target: String },
    Test { filter: Option<String> },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Build { target } => {
            build_target(&target)?;
        }
        Commands::Test { filter } => {
            run_tests(filter.as_deref())?;
        }
    }

    Ok(())
}
```

**关键决策**:

- CLI: `clap`（派生宏）
- 错误处理: `anyhow` + `thiserror`
- 配置: `serde` + `toml`
- 颜色输出: `owo-colors` / `console`

---

> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
