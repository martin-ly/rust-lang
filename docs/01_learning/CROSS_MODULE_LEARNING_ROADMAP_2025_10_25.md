# 跨模块学习路线图

> **报告日期**: 2025-10-25
> **最后更新**: 2026-04-10

---

## 🗺️ 7 条定制化学习路径

### 路径 1: 零基础入门

```
C01 → C02 → C03 → 项目
```

### 路径 2: 有编程经验

```
C01 → C04 → C05 → 项目
```

### 路径 3: 系统程序员

```
C01 → C07 → C08 → C10
```

### 路径 4: Web 开发者

```
C01 → C06 → C10 → C12
```

### 路径 5: Rust 1.96 新特性探索者

```
isqrt → get_disjoint_mut → async Fn → 综合项目
```

---

## 🆕 Rust 1.96 新特性在各模块中的应用

### C01 所有权与借用 → 1.96 并发安全

**新特性关联**:

```rust
// HashMap::get_disjoint_mut - 编译时保证互斥访问
use std::collections::HashMap;

fn ownership_with_196_features() {
    let mut map = HashMap::new();
    map.insert("key1", vec![1, 2, 3]);
    map.insert("key2", vec![4, 5, 6]);

    // Rust 1.96: 编译器确保这些键不重复，安全地获取多个可变引用
    let [Some(v1), Some(v2)] = map.get_disjoint_mut(["key1", "key2"]) else {
        panic!("keys not found");
    };

    // 可以同时修改两个不同的值
    v1.push(100);
    v2.push(200);
}
```

**学习建议**: 结合 C01 的所有权概念理解 `get_disjoint_mut` 的编译时安全检查。

### C04 泛型 → 1.96 async Fn Trait

**新特性关联**:

```rust
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

**模块关联**: C06 (异步) + C04 (泛型) + 1.96 async Fn

**学习建议**: 在学习 C04 泛型时，尝试用 1.96 的 `async Fn` 语法重构异步代码。

### C05 线程 → 1.96 线程改进

**新特性关联**:

```rust
// spawn_unchecked - 高级线程控制 (unsafe)
use std::thread;

unsafe fn advanced_threading() {
    // 跳过某些运行时检查，用于极端性能场景
    let handle = thread::Builder::new()
        .spawn_unchecked(|| {
            // 线程逻辑
        })
        .unwrap();

    handle.join().unwrap();
}

// 结合 1.94 的 LazyLock 实现线程安全延迟初始化
use std::sync::LazyLock;

static WORKER_POOL: LazyLock<thread::Thread> = LazyLock::new(|| {
    thread::current() // 示例
});
```

**学习建议**: C05 线程基础 → 1.94 LazyLock → 1.96 spawn_unchecked

### C08 算法 → 1.96 isqrt

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

// 2. 结合 1.94 array_windows 的几何算法
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

**学习建议**: C08 算法基础 → 1.96 isqrt 优化 → 1.94 array_windows 组合应用

---

## 🔗 关联学习建议

### 学习路线 A: 数学与算法方向

```
C02 (类型系统)
    ↓
C08 (算法基础)
    ↓
Rust 1.96 isqrt ─────┐
Rust 1.94 数学常量 ──┼→ 数学计算项目
C08 高级算法 ────────┘
```

**推荐项目**: 数字信号处理器、几何计算库

### 学习路线 B: 并发与数据结构方向

```
C01 (所有权)
    ↓
C05 (线程基础)
    ↓
Rust 1.96 get_disjoint_mut ──┐
Rust 1.94 LazyLock ──────────┼→ 并发缓存系统
C05 高级并发模式 ────────────┘
```

**推荐项目**: 高性能缓存系统、并发任务调度器

### 学习路线 C: 异步编程方向

```
C04 (泛型基础)
    ↓
C06 (异步基础)
    ↓
Rust 1.96 async Fn ────┐
Rust 1.94 ControlFlow ─┼→ 异步 Web 服务
Tokio 生态 ────────────┘
```

**推荐项目**: REST API 服务、实时数据处理管道

### 学习路线 D: 系统编程方向

```
C01 (所有权)
    ↓
C07 (进程管理)
    ↓
Rust 1.96 spawn_unchecked ───┐
Rust 1.94 Unsafe 改进 ───────┼→ 系统监控工具
C07 高级系统编程 ────────────┘
```

**推荐项目**: 系统监控工具、容器运行时组件

---

## 📋 新特性快速参考表

| 特性 | 所属模块 | 前置知识 | 学习优先级 |
|------|----------|----------|------------|
| `isqrt` | C08 算法 | 基础数学 | ⭐ 高 |
| `get_disjoint_mut` | C01/C05 | 所有权、HashMap | ⭐⭐ 中高 |
| `async Fn` trait | C04/C06 | 泛型、async/await | ⭐⭐ 中 |
| `spawn_unchecked` | C05 | 线程基础、unsafe | ⭐⭐⭐ 低 |
| never_type (!) | C03/C13 | 错误处理 | ⭐⭐ 中 |

---

**状态**: ✅ 可用 (已更新 Rust 1.96 内容)
