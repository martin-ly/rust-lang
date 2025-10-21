# 第2层：系统编程层 (System Programming Layer)

> **定位**: 系统级编程所需的并发、内存、I/O 等核心能力  
> **特点**: 高性能、零成本抽象、安全并发  
> **版本**: Rust 1.90 (2025)

---

## 📋 核心类别

### 1. 异步运行时 ([`async_runtime/`](./async_runtime/))

| 库名 | 特点 | 生态 | 推荐度 |
|------|------|------|--------|
| **tokio** | 功能最全、生态最大 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **async-std** | 类似标准库 API | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **smol** | 轻量级、高性能 | ⭐⭐⭐ | ⭐⭐⭐⭐ |

**快速示例** (tokio):

```rust
#[tokio::main]
async fn main() {
    tokio::spawn(async {
        println!("Hello from spawn!");
    }).await.unwrap();
}
```

---

### 2. 并发原语 ([`concurrency/`](./concurrency/))

| 库名 | 用途 | 推荐度 |
|------|------|--------|
| **rayon** | 数据并行 | ⭐⭐⭐⭐⭐ |
| **crossbeam** | 并发数据结构 | ⭐⭐⭐⭐⭐ |
| **parking_lot** | 高性能锁 | ⭐⭐⭐⭐⭐ |

**快速示例** (rayon):

```rust
use rayon::prelude::*;

let sum: i32 = (1..=1000)
    .into_par_iter()
    .map(|x| x * x)
    .sum();
```

---

### 3. 内存管理 ([`memory/`](./memory/))

| 库名 | 用途 | 推荐度 |
|------|------|--------|
| **bytes** | 字节缓冲区 | ⭐⭐⭐⭐⭐ |
| **bumpalo** | 竞技场分配器 | ⭐⭐⭐⭐ |

---

### 4. 网络编程 ([`networking/`](./networking/))

| 库名 | 层次 | 推荐度 |
|------|------|--------|
| **mio** | 底层事件驱动 | ⭐⭐⭐⭐ |
| **socket2** | Socket API | ⭐⭐⭐⭐ |

---

### 5. 文件 I/O ([`io/`](./io/))

| 库名 | 特点 | 推荐度 |
|------|------|--------|
| **tokio::fs** | 异步文件 I/O | ⭐⭐⭐⭐⭐ |
| **async-std::fs** | 异步文件 I/O | ⭐⭐⭐⭐ |

---

### 6. 通道 ([`channels/`](./channels/))

| 库名 | 类型 | 推荐度 |
|------|------|--------|
| **flume** | MPMC | ⭐⭐⭐⭐ |
| **crossbeam-channel** | MPMC | ⭐⭐⭐⭐⭐ |
| **tokio::sync::mpsc** | 异步 MPSC | ⭐⭐⭐⭐⭐ |

---

## 📚 学习路径

1. **第1周**: tokio 基础 - spawn, join, select
2. **第2周**: rayon 数据并行
3. **第3周**: crossbeam 并发数据结构
4. **第4周**: 综合项目 - 高并发服务器

---

**详细文档**: [系统编程完整指南 →](./guides/)

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
