# 运行时指南 (Runtimes)

本目录包含Rust主流异步运行时的对比分析、最佳实践和使用指南。

## 📚 文档列表

### [01_comparison_2025.md](./01_comparison_2025.md) - 运行时对比 ⭐⭐⭐⭐⭐

**必读文档**:

2025年最新运行时全面对比：

- Tokio vs async-std vs Smol
- 性能基准测试
- 功能特性对比
- 生态系统成熟度
- 选择决策树

**适合**: 选择运行时前必读

---

### [02_tokio_best_practices.md](./02_tokio_best_practices.md) - Tokio最佳实践 ⭐⭐⭐⭐

**生产环境推荐**:

Tokio运行时最佳实践：

- 运行时配置优化
- 任务管理策略
- 资源控制
- 监控和调试
- 常见陷阱

**适合**: 使用Tokio的生产项目

---

### [03_smol_best_practices.md](./03_smol_best_practices.md) - Smol最佳实践 ⭐⭐⭐

**轻量级方案**:

Smol运行时最佳实践：

- 极简配置
- 嵌入式应用
- 低资源消耗优化
- 与其他运行时对比

**适合**: 嵌入式或轻量级应用

---

### [04_cookbook.md](./04_cookbook.md) - 实战手册 ⭐⭐⭐⭐

**实用参考**:

Tokio和Smol实战代码示例：

- 常见使用场景
- 代码模板
- 最佳实践代码
- 性能优化技巧

**适合**: 日常开发参考

---

## 🎯 运行时选择指南

### 快速决策树

```text
需要选择运行时？
│
├─ 生产环境Web服务？
│  └─ ✅ Tokio (成熟、高性能、生态丰富)
│
├─ 学习异步编程？
│  └─ ✅ async-std (API类似标准库，易学)
│
├─ 嵌入式或资源受限？
│  └─ ✅ Smol (极轻量，~1500行代码)
│
└─ 需要自定义运行时？
   └─ ✅ 参考 [../core/02_runtime_and_execution_model.md](../core/02_runtime_and_execution_model.md)
```

---

## 📊 运行时对比速览

| 特性 | Tokio | async-std | Smol |
|------|-------|-----------|------|
| **成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **生态** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **易用性** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **体积** | 大 | 中 | 小 |
| **学习曲线** | 中等 | 平缓 | 陡峭 |

详细对比见 [01_comparison_2025.md](./01_comparison_2025.md)

---

## 💡 使用建议

### Tokio - 生产首选

**优势**:

- 性能最优
- 生态最丰富（Axum, Tonic, etc.）
- 企业级支持
- 监控工具完善（tokio-console）

**适用场景**:

- Web服务器
- gRPC服务
- WebSocket服务
- 高性能代理

**示例**:

```rust
#[tokio::main]
async fn main() {
    // Tokio代码
}
```

---

### async-std - 学习友好

**优势**:

- API设计类似标准库
- 学习曲线平缓
- 文档优秀
- 适合教学

**适用场景**:

- 学习项目
- 原型开发
- 不需要极致性能的应用

**示例**:

```rust
use async_std::task;

fn main() {
    task::block_on(async {
        // async-std代码
    });
}
```

---

### Smol - 轻量之选

**优势**:

- 代码量极小（~1500行）
- 资源消耗低
- 适合嵌入式
- 易于理解实现

**适用场景**:

- 嵌入式系统
- CLI工具
- 学习运行时原理
- 需要自定义运行时

**示例**:

```rust
use smol;

fn main() {
    smol::block_on(async {
        // Smol代码
    });
}
```

---

## 🚀 快速开始

### Tokio

```toml
[dependencies]
tokio = { version = "1.35", features = ["full"] }
```

```rust
#[tokio::main]
async fn main() {
    println!("Hello from Tokio!");
}
```

### async-std

```toml
[dependencies]
async-std = { version = "1.12", features = ["attributes"] }
```

```rust
#[async_std::main]
async fn main() {
    println!("Hello from async-std!");
}
```

### Smol

```toml
[dependencies]
smol = "2.0"
```

```rust
fn main() {
    smol::block_on(async {
        println!("Hello from Smol!");
    });
}
```

---

## 📖 相关资源

### 本模块资源

- [../guides/](../guides/) - 基础学习指南
- [../core/02_runtime_and_execution_model.md](../core/02_runtime_and_execution_model.md) - 运行时原理
- [../performance/](../performance/) - 性能优化指南

### 外部资源

- [Tokio官方文档](https://tokio.rs/)
- [async-std官方文档](https://async.rs/)
- [Smol官方文档](https://docs.rs/smol/)

### 示例代码

```bash
cd ../../examples/runtimes/
cargo run --example tokio_basic
cargo run --example async_std_basic
cargo run --example smol_basic
```

---

## ⚠️ 常见陷阱

### 1. 运行时不兼容

```rust
// ❌ 错误：混用不同运行时
#[tokio::main]
async fn main() {
    async_std::task::sleep(...).await; // 不兼容！
}

// ✅ 正确：使用同一运行时的API
#[tokio::main]
async fn main() {
    tokio::time::sleep(...).await;
}
```

### 2. 阻塞运行时

```rust
// ❌ 错误：在异步上下文阻塞
async fn bad() {
    std::thread::sleep(...); // 会阻塞整个线程！
}

// ✅ 正确：使用spawn_blocking
async fn good() {
    tokio::task::spawn_blocking(|| {
        std::thread::sleep(...);
    }).await;
}
```

### 3. 过度使用spawn

```rust
// ❌ 低效：过度spawn
for i in 0..1000 {
    tokio::spawn(async move {
        do_work(i).await;
    });
}

// ✅ 更好：批量处理
use futures::future::join_all;
let tasks: Vec<_> = (0..1000)
    .map(|i| do_work(i))
    .collect();
join_all(tasks).await;
```

---

## 📝 最佳实践总结

### 配置

- ✅ 根据负载调整worker线程数
- ✅ 配置合理的堆栈大小
- ✅ 启用所需的feature即可

### 任务管理

- ✅ 合理使用spawn和join
- ✅ 避免创建过多任务
- ✅ 及时取消不需要的任务

### 资源控制

- ✅ 使用连接池
- ✅ 限制并发数（Semaphore）
- ✅ 设置超时

### 监控调试

- ✅ 使用tokio-console监控
- ✅ 添加合适的日志
- ✅ 性能分析工具

---

## 🔄 运行时迁移

从一个运行时迁移到另一个？

### Tokio → async-std

主要API差异：

- `tokio::main` → `async_std::main`
- `tokio::spawn` → `async_std::task::spawn`
- `tokio::time::sleep` → `async_std::task::sleep`

### async-std → Tokio

反向迁移通常是为了性能或生态系统。

### 通用抽象

考虑使用运行时无关的抽象：

- `futures` crate提供的trait
- `async-trait`用于trait中的async
- 条件编译处理差异

---

**目录状态**: ✅ 完整  
**最后更新**: 2025-10-19
