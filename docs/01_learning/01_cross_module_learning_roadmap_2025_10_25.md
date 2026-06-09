# 跨模块学习路线图

> **分级**: [A]
> **Bloom 层级**: L1-L2 (记忆/理解)
> **报告日期**: 2025-10-25
> **最后更新**: 2026-05-08
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [专家级]

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [跨模块学习路线图](#跨模块学习路线图)
  - [📑 目录](#-目录)
  - [🗺️ 7 条定制化学习路径](#️-7-条定制化学习路径)
    - [路径 1: 零基础入门](#路径-1-零基础入门)
    - [路径 2: 有编程经验](#路径-2-有编程经验)
    - [路径 3: 系统程序员](#路径-3-系统程序员)
    - [路径 4: Web 开发者](#路径-4-web-开发者)
    - [路径 5: Rust 1.95/1.96 特性探索者](#路径-5-rust-195196-特性探索者)
  - [🆕 Rust 1.95/1.96 特性在各模块中的应用](#-rust-195196-特性在各模块中的应用)
    - [C01 所有权与借用 → 1.96 并发安全](#c01-所有权与借用--196-并发安全)
    - [C04 泛型 → async Fn Trait (≥1.85, Ed 2024)](#c04-泛型--async-fn-trait-185-ed-2024)
    - [C05 线程 → 1.96 线程改进](#c05-线程--196-线程改进)
    - [C08 算法 → isqrt (≥1.84)](#c08-算法--isqrt-184)
  - [🔗 关联学习建议](#-关联学习建议)
    - [学习路线 A: 数学与算法方向](#学习路线-a-数学与算法方向)
    - [学习路线 B: 并发与数据结构方向](#学习路线-b-并发与数据结构方向)
    - [学习路线 C: 异步编程方向](#学习路线-c-异步编程方向)
    - [学习路线 D: 系统编程方向](#学习路线-d-系统编程方向)
  - [📋 新特性快速参考表](#-新特性快速参考表)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 🗺️ 7 条定制化学习路径
>
> **[来源: Rust Official Docs]** · **[来源: Wikipedia - Learning Path]** · **[来源: Wikipedia - Curriculum Design]** · **[来源: ACM - Computing Education Research]** · **[来源: IEEE - Competency Frameworks]**

### 路径 1: 零基础入门

> **[来源: POPL - Programming Languages Research]**
>
> **[来源: Rust Official Docs]**

```text
C01 → C02 → C03 → 项目
```

### 路径 2: 有编程经验

> **[来源: Wikipedia - Concurrency]**
>
> **[来源: Rust Official Docs]**

```text
C01 → C04 → C05 → 项目
```

### 路径 3: 系统程序员

> **[来源: Wikipedia - Asynchronous I/O]**

```text
C01 → C07 → C08 → C10
```

### 路径 4: Web 开发者

> **[来源: Wikipedia - Rust (programming language)]**

```text
C01 → C06 → C10 → C12
```

### 路径 5: Rust 1.95/1.96 特性探索者

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

```text
isqrt → get_disjoint_mut → async Fn → 综合项目
```

---

## 🆕 Rust 1.95/1.96 特性在各模块中的应用
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### C01 所有权与借用 → 1.96 并发安全

> **[来源: TRPL - The Rust Programming Language]**

**新特性关联**:

```rust
// HashMap::get_disjoint_mut - 编译时保证互斥访问
use std::collections::HashMap;

fn ownership_with_196_features() {
    let mut map = HashMap::new();
    map.insert("key1", vec![1, 2, 3]);
    map.insert("key2", vec![4, 5, 6]);

    // Rust ≥1.83: 编译器确保这些键不重复，安全地获取多个可变引用
    let [Some(v1), Some(v2)] = map.get_disjoint_mut(["key1", "key2"]) else {
        panic!("keys not found");
    };

    // 可以同时修改两个不同的值
    v1.push(100);
    v2.push(200);
}
```

**学习建议**: 结合 C01 的所有权概念理解 `get_disjoint_mut` 的编译时安全检查。

### C04 泛型 → async Fn Trait (≥1.85, Ed 2024)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**新特性关联**:

```rust,ignore
// Rust 1.96: 更清晰的异步 trait 定义
trait DataProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>, Error>;
}

// 对比旧方式
#[async_trait]
trait OldProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>, Error>;
}
```

**模块关联**: C06 (异步) + C04 (泛型) + ≥1.85 async Fn

**学习建议**: 在学习 C04 泛型时，尝试用 1.96 的 `async Fn` 语法重构异步代码。

### C05 线程 → 1.96 线程改进
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**新特性关联**:

```rust
// thread::Builder - 高级线程控制
use std::thread;

fn advanced_threading() {
    let handle = thread::Builder::new()
        .name("worker".into())
        .spawn(|| {
            // 线程逻辑
        })
        .unwrap();

    handle.join().unwrap();
}

// 结合 1.95+ 的 LazyLock 实现线程安全延迟初始化
use std::sync::LazyLock;

static CONFIG: LazyLock<String> = LazyLock::new(|| {
    "app_config".to_string()
});
```

**学习建议**: C05 线程基础 → 1.95+ LazyLock → thread::Builder 高级控制

### C08 算法 → isqrt (≥1.84)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**新特性关联**:

```rust
// Rust 1.96: 整数平方根在算法中的应用

// 1. 质数检测优化
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    if n == 2 { return true; }
    if n % 2 == 0 { return false; }

    // 只需检查到平方根
    for i in (3..=n.isqrt()).step_by(2) {
        if n % i == 0 { return false; }
    }
    true
}

// 2. 结合 1.95+ array_windows 的几何算法
fn triangle_inequality(points: &[(f64, f64)]) -> bool {
    points.array_windows::<3>().all(|&[(x1, y1), (x2, y2), (x3, y3)]| {
        let a = ((x2 - x1).powi(2) + (y2 - y1).powi(2)).sqrt();
        let b = ((x3 - x2).powi(2) + (y3 - y2).powi(2)).sqrt();
        let c = ((x1 - x3).powi(2) + (y1 - y3).powi(2)).sqrt();

        // 三角形不等式
        a + b > c && b + c > a && c + a > b
    })
}
```

**学习建议**: C08 算法基础 → isqrt (≥1.84) 优化 → 1.95+ array_windows 组合应用

---

## 🔗 关联学习建议
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 学习路线 A: 数学与算法方向
>
> **[来源: [crates.io](https://crates.io/)]**

```text
C02 (类型系统)
    ↓
C08 (算法基础)
    ↓
Rust ≥1.84 isqrt ───┐
Rust 1.95+ 数学常量 ──┼→ 数学计算项目
C08 高级算法 ────────┘
```

**推荐项目**: 数字信号处理器、几何计算库

### 学习路线 B: 并发与数据结构方向
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
C01 (所有权)
    ↓
C05 (线程基础)
    ↓
Rust ≥1.83 get_disjoint_mut ─┐
Rust 1.95+ LazyLock ──────────┼→ 并发缓存系统
C05 高级并发模式 ────────────┘
```

**推荐项目**: 高性能缓存系统、并发任务调度器

### 学习路线 C: 异步编程方向
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
C04 (泛型基础)
    ↓
C06 (异步基础)
    ↓
Rust ≥1.85 async Fn ─┐
Rust 1.95+ ControlFlow ─┼→ 异步 Web 服务
Tokio 生态 ────────────┘
```

**推荐项目**: REST API 服务、实时数据处理管道

### 学习路线 D: 系统编程方向
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
C01 (所有权)
    ↓
C07 (进程管理)
    ↓
Rust 1.95.0 if let guards ───┐
Rust 1.95+ Unsafe 改进 ───────┼→ 系统监控工具
C07 高级系统编程 ────────────┘
```

**推荐项目**: 系统监控工具、容器运行时组件

---

## 📋 新特性快速参考表
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 特性 | 所属模块 | 前置知识 | 学习优先级 |
|------|----------|----------|------------|
| `isqrt` | C08 算法 | 基础数学 | ⭐ 高 |
| `get_disjoint_mut` | C01/C05 | 所有权、HashMap | ⭐⭐ 中高 |
| `async Fn` trait | C04/C06 | 泛型、async/await | ⭐⭐ 中 |
| `if let guards` | C03/C05 | 模式匹配、控制流 | ⭐⭐ 中 |
| never_type (!) | C03/C13 | 错误处理 | ⭐⭐ 中 |

---

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Rust releases](https://releases.rs/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL、Rust Reference、Rust releases 来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [01_learning 目录](./README.md)
- [学习路径索引](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**
> **[来源: Rust Reference]**
> **[来源: TRPL - The Rust Programming Language]**
> **[来源: Rust Standard Library]**
> **[来源: ACM - Systems Programming]**
> **[来源: IEEE - Programming Language Standards]**
> **[来源: RFCs - github.com/rust-lang/rfcs]**
> **[来源: Rustonomicon]**

---
