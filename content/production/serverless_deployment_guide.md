# Rust Serverless 部署指南

> **定位**: Rust 函数在主流 Serverless 平台的部署与优化
> **适用**: AWS Lambda、Azure Functions、Cloudflare Workers
> **工具链**: cargo-lambda, azure-functions-rs, worker
> **Rust 版本**: 1.96.0+

---

## 📋 目录

- [Rust Serverless 部署指南](#rust-serverless-部署指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [☁️ AWS Lambda](#️-aws-lambda)
    - [基础示例](#基础示例)
    - [Cargo Lambda 工具链](#cargo-lambda-工具链)
  - [☁️ Azure Functions](#️-azure-functions)
    - [HTTP 触发器示例](#http-触发器示例)
    - [自定义 Handler](#自定义-handler)
  - [☁️ Cloudflare Workers](#️-cloudflare-workers)
    - [Worker Crate 示例](#worker-crate-示例)
    - [Wrangler 部署](#wrangler-部署)
  - [⚡ 冷启动优化](#-冷启动优化)
  - [📦 二进制体积优化](#-二进制体积优化)
  - [🌲 决策树：选择哪个平台](#-决策树选择哪个平台)
  - [📊 平台对比矩阵](#-平台对比矩阵)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

Rust 的零成本抽象和极小的运行时使其成为 Serverless 场景的理想语言：

- **冷启动快**: 无 GC、无运行时初始化，启动时间可低至毫秒级
- **内存占用低**: 相同负载下内存仅为 Node.js/Python 的 1/5 ~ 1/10
- **二进制自包含**: 静态链接后可部署到最小化执行环境

```text
各平台 Rust 支持状态:
├─ AWS Lambda: 官方 Runtime + cargo-lambda 生态成熟
├─ Azure Functions: Custom Handler + 原生绑定 (预览)
└─ Cloudflare Workers: worker crate + WASM 目标成熟
```

---

## ☁️ AWS Lambda

### 基础示例

使用 `lambda_runtime` crate 构建标准 Lambda Handler：

```rust
use lambda_runtime::{service_fn, LambdaEvent, Error};
use serde_json::{json, Value};

#[tokio::main]
async fn main() -> Result<(), Error> {
    let func = service_fn(handler);
    lambda_runtime::run(func).await?;
    Ok(())
}

async fn handler(
    event: LambdaEvent<Value>,
) -> Result<Value, Error> {
    let name = event.payload["name"]
        .as_str()
        .unwrap_or("world");

    Ok(json!({
        "statusCode": 200,
        "headers": {
            "Content-Type": "application/json"
        },
        "body": json!({
            "message": format!("Hello, {}!", name),
            "request_id": event.context.request_id,
        }).to_string(),
    }))
}
```

**Cargo.toml 关键依赖**：

```toml
[dependencies]
lambda_runtime = "0.13"
tokio = { version = "1", features = ["macros"] }
serde_json = "1"
```

### Cargo Lambda 工具链

```bash
# 安装
cargo install cargo-lambda

# 本地模拟测试
cargo lambda watch

# 交叉编译 (x86_64)
cargo lambda build --release \
    --target x86_64-unknown-linux-musl

# 交叉编译 (ARM64) — 推荐，性价比更高
cargo lambda build --release \
    --target aarch64-unknown-linux-musl

# 部署
cargo lambda deploy --region us-east-1 \
    --iam-role arn:aws:iam::ACCOUNT:role/lambda-role
```

---

## ☁️ Azure Functions

Azure Functions 对 Rust 的支持通过 **Custom Handler** 或 **WASM 绑定** 实现。

### HTTP 触发器示例

```rust
use std::env;
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct HttpRequest {
    name: Option<String>,
}

#[derive(Serialize)]
struct HttpResponse {
    outputs: Outputs,
    logs: Vec<String>,
    return_response: ReturnResponse,
}

#[derive(Serialize)]
struct Outputs {
    res: ResponseBody,
}

#[derive(Serialize)]
struct ResponseBody {
    status: u16,
    body: String,
}

#[derive(Serialize)]
struct ReturnResponse {
    status: u16,
    body: String,
}

fn main() {
    let func_port = env::var("FUNCTIONS_CUSTOMHANDLER_PORT")
        .unwrap_or_else(|_| "3000".to_string());

    // 使用标准 HTTP 框架（如 Axum/Actix）监听 func_port
    // Azure Functions Host 通过 HTTP 调用 Custom Handler
}
```

### 自定义 Handler

```json
// host.json
{
  "version": "2.0",
  "customHandler": {
    "description": {
      "defaultExecutablePath": "handler",
      "workingDirectory": "",
      "arguments": []
    },
    "enableForwardingHttpRequest": true
  },
  "extensions": {
    "http": {
      "routePrefix": "api"
    }
  }
}
```

---

## ☁️ Cloudflare Workers

Cloudflare Workers 使用 V8 Isolate 运行 WASM，Rust 通过 `wasm32-unknown-unknown` 目标编译。

### Worker Crate 示例

```rust
use worker::*;

#[event(fetch)]
pub async fn main(req: Request, env: Env, _ctx: Context) -> Result<Response> {
    match req.path().as_str() {
        "/api/hello" => {
            let name = req.url()?.query_pairs()
                .find(|(k, _)| k == "name")
                .map(|(_, v)| v.to_string())
                .unwrap_or_else(|| "world".to_string());

            Response::ok(format!("Hello, {}!", name))
        }
        "/api/kv" => {
            let kv = env.kv("MY_KV")?;
            let value = kv.get("key").text().await?;
            Response::ok(value.unwrap_or_default())
        }
        _ => Response::error("Not Found", 404),
    }
}
```

**Cargo.toml**：

```toml
[package]
name = "cf-worker"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
worker = "0.5"
serde_json = "1"
console_error_panic_hook = "0.1"
```

### Wrangler 部署

```bash
# 安装 Wrangler
npm install -g wrangler

# 登录 Cloudflare
wrangler login

# 本地开发
wrangler dev

# 发布
cargo install wasm-pack
wasm-pack build --target web
wrangler deploy
```

---

## ⚡ 冷启动优化

冷启动（Cold Start）是 Serverless 的核心指标。Rust 天生具备优势，但仍需针对性优化：

| 优化手段 | 效果 | 实施方式 |
|----------|------|----------|
| 静态链接 musl | -50% 启动时间 | `x86_64-unknown-linux-musl` |
| 精简依赖树 | -30% 二进制体积 | `cargo tree -d` 去重 |
| 延迟初始化 | -20% 首响延迟 | `lazy_static` / `once_cell` |
| 预编译模板 | -15% 首次渲染 | 编译期生成响应结构 |
| 连接池预热 | -40% DB 首查延迟 | 在 `main()` 中提前建立连接 |

```rust
// ❌ 每次调用都创建客户端
async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    let client = reqwest::Client::new(); // 昂贵！
    let resp = client.get("...").await?;
    // ...
}

// ✅ 使用 Lazy 全局复用
use std::sync::LazyLock;

static CLIENT: LazyLock<reqwest::Client> =
    LazyLock::new(|| reqwest::Client::builder()
        .timeout(Duration::from_secs(5))
        .build()
        .unwrap()
    );

async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    let resp = CLIENT.get("...").await?; // 复用连接池
    // ...
}
```

---

## 📦 二进制体积优化

Serverless 平台通常对部署包大小有限制（如 Lambda 250MB 解压后）：

```toml
# Cargo.toml 体积优化配置
[profile.release]
opt-level = "z"        # 优化体积
lto = true             # 链接时优化
codegen-units = 1      # 单代码生成单元
panic = "abort"        # 移除 panic 展开
strip = true           # 移除符号表
```

| 技术 | 体积减少 | 代价 |
|------|----------|------|
| `opt-level = "z"` | ~20% | 运行速度略降 |
| `lto = true` | ~15% | 编译时间翻倍 |
| `panic = "abort"` | ~10% | 无栈回溯 |
| `strip = true` | ~30% | 无法调试 |
| `upx` 压缩 | ~50% | 启动时解压开销 |

```bash
# 使用 cargo-bloat 分析体积膨胀点
cargo install cargo-bloat
cargo bloat --release --crates

# 使用 twiggy 分析 WASM 体积 (Cloudflare)
cargo install twiggy
twiggy top -n 10 pkg/worker_bg.wasm
```

---

## 🌲 决策树：选择哪个平台

```text
开始
│
├─ 需要 < 50ms 冷启动且全球边缘部署？
│   └─ 是 → Cloudflare Workers (V8 Isolate, 0ms 冷启动)
│
├─ 需要深度 AWS 生态集成 (S3, DynamoDB, SQS, EventBridge)？
│   └─ 是 → AWS Lambda (原生 SDK, 最成熟)
│
├─ 需要与 Azure 生态集成 (CosmosDB, ServiceBus, EntraID)？
│   └─ 是 → Azure Functions (Custom Handler)
│
├─ 需要 WASM 生态和浏览器端复用？
│   └─ 是 → Cloudflare Workers
│
├─ 需要最低的按调用成本？
│   └─ 比较:
│       ├─ 高频 (>1M/月): Cloudflare Workers 免费额度最慷慨
│       ├─ 中频: AWS Lambda ARM64 性价比最高
│       └─ 低频: Azure Functions 消费计划计费粒度细
│
└─ 需要最长的执行时间？
    └─ AWS Lambda: 15min
    └─ Azure Functions: 10min (消费) / 无限制 (专用)
    └─ Cloudflare Workers: 30s (免费) / 5min (付费)
```

---

## 📊 平台对比矩阵

| 维度 | AWS Lambda | Azure Functions | Cloudflare Workers |
|------|------------|-----------------|-------------------|
| **运行模型** | 进程级容器 | 进程级容器 | V8 Isolate |
| **Rust 支持** | ⭐⭐⭐ 官方 Runtime | ⭐⭐ Custom Handler | ⭐⭐⭐ WASM 原生 |
| **冷启动** | 10~100ms | 50~200ms | **~0ms** |
| **最大内存** | 10GB | 16GB | 128MB ~ 1GB |
| **最大超时** | 15分钟 | 10分钟 | 30秒 ~ 5分钟 |
| **构建目标** | `x86_64/aarch64-linux-musl` | `x86_64-linux` | `wasm32-unknown-unknown` |
| **核心 crate** | `lambda_runtime` | `hyper` / `axum` | `worker` |
| **部署工具** | `cargo-lambda` | Azure CLI / Func Core Tools | `wrangler` |
| **边缘节点** | CloudFront (额外) | Front Door (额外) | **全球 300+ 节点内置** |
| **免费额度** | 100万请求/月 | 100万请求/月 | **1000万请求/月** |
| **典型场景** | 数据处理、ETL、API | 企业集成、定时任务 | 边缘计算、A/B 测试 |

---

## 🔗 参考资源

- [AWS Lambda Rust Runtime](https://github.com/awslabs/aws-lambda-rust-runtime)
- [Cargo Lambda](https://www.cargo-lambda.info/)
- [Azure Functions Custom Handlers](https://learn.microsoft.com/azure/azure-functions/functions-custom-handlers)
- [Cloudflare Workers Rust](https://developers.cloudflare.com/workers/languages/rust/)
- [worker-rs 文档](https://docs.rs/worker/latest/worker/)
- [Rust Serverless Optimization Guide](https://github.com/john-shaffer/rust-serverless)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
