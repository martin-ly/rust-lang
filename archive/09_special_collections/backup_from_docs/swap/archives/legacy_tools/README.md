# 工具与配置 (Tools)

本目录包含Rust异步编程的开发工具、调试工具和监控配置。

## 📚 内容列表

### 文档

- **[tokio_console_tracing.md](./tokio_console_tracing.md)**  
  Tokio Console和分布式追踪工具使用指南

### 配置文件

- **[dashboards/](./dashboards/)** - 监控面板配置
  - `gateway_dashboard.json` - 网关监控面板
  - `hybrid_dashboard.json` - 混合服务监控面板

---

## 🔧 主要工具

### Tokio Console

**功能**: 运行时可视化监控

```bash
# 安装
cargo install tokio-console

# 启用追踪
[dependencies]
console-subscriber = "0.2"

# 运行
tokio-console
```

**监控内容**:

- 任务状态
- 任务执行时间
- 任务等待时间
- 资源使用情况

---

### Tracing

**功能**: 分布式追踪和日志

```rust
use tracing::{info, instrument};

#[instrument]
async fn my_function() {
    info!("执行中...");
}
```

**特点**:

- 结构化日志
- 分布式追踪
- 性能分析
- 与tokio-console集成

---

### Criterion

**功能**: 性能基准测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_async(c: &mut Criterion) {
    c.bench_function("async_task", |b| {
        b.iter(|| {
            tokio::runtime::Runtime::new()
                .unwrap()
                .block_on(async_task())
        });
    });
}
```

---

## 📊 监控面板

### gateway_dashboard.json

网关服务监控面板，包含：

- 请求吞吐量
- 响应延迟
- 错误率
- 连接数

### hybrid_dashboard.json

混合服务监控面板，包含：

- CPU使用率
- 内存使用
- 任务队列长度
- 各服务状态

**使用方式**:
导入到Grafana等监控系统

---

## 🚀 快速开始

### 1. 启用Tokio Console

```toml
[dependencies]
tokio = { version = "1.35", features = ["full", "tracing"] }
console-subscriber = "0.2"
```

```rust
fn main() {
    console_subscriber::init();
    // 你的代码
}
```

### 2. 配置Tracing

```rust
use tracing_subscriber;

fn main() {
    tracing_subscriber::fmt::init();
    // 你的代码
}
```

### 3. 运行基准测试

```bash
cargo bench
```

---

## 💡 调试技巧

### 1. 任务hang住

使用tokio-console查看：

- 任务在等什么
- 是否有死锁
- 哪个任务最慢

### 2. 性能问题

使用tracing分析：

- 哪里最耗时
- 调用链路
- 性能瓶颈

### 3. 内存问题

使用监控面板：

- 内存增长趋势
- 是否有泄漏
- 峰值使用情况

---

## 🔗 相关资源

- [tokio-console文档](https://docs.rs/tokio-console/)
- [tracing文档](https://docs.rs/tracing/)
- [criterion文档](https://docs.rs/criterion/)

**最后更新**: 2025-10-19
