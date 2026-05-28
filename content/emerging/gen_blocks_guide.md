# `gen` Blocks 与 `yield` 表达式指南

> **定位**: Rust 原生生成器语法前瞻
> **状态**: Nightly (feature `gen_blocks`)
> **预计稳定**: Rust 1.98+

---

## 📋 目录

- [`gen` Blocks 与 `yield` 表达式指南](#gen-blocks-与-yield-表达式指南)
  - [📋 目录](#-目录)
  - [🎯 什么是生成器](#-什么是生成器)
  - [⚡ 基础语法](#-基础语法)
  - [🔀 与 Iterators 对比](#-与-iterators-对比)
    - [传统 Iterator](#传统-iterator)
    - [生成器版本](#生成器版本)
  - [📊 与 Async 对比](#-与-async-对比)
  - [🔄 实际用例](#-实际用例)
    - [文件行过滤流](#文件行过滤流)
    - [组合生成器](#组合生成器)
  - [⚠️ 当前限制](#️-当前限制)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 什么是生成器

生成器是一种**懒计算**的协程，可以**暂停执行**并**恢复状态**：

```rust
#![feature(gen_blocks, yield_expr)]

// 生成器: 懒计算斐波那契数列
let fib = gen {
    let mut a = 0;
    let mut b = 1;
    loop {
        yield a;
        (a, b) = (b, a + b);
    }
};

// 消费前 10 个值
for (i, n) in fib.take(10).enumerate() {
    println!("fib[{}] = {}", i, n);
}
```

**核心优势**:

- 状态隐式保存（无需手动 struct）
- 懒计算（按需生成）
- 可组合（与 Iterator 适配器链式使用）

---

## ⚡ 基础语法

```rust
#![feature(gen_blocks, yield_expr)]

/// 生成器函数
fn count_to(n: u32) -> impl Iterator<Item = u32> {
    gen move {
        for i in 0..n {
            yield i;
        }
    }
}

/// 树遍历生成器
fn tree_dfs<T>(node: &TreeNode<T>) -> impl Iterator<Item = &T> {
    gen move {
        yield &node.value;
        for child in &node.children {
            for val in tree_dfs(child) {
                yield val;
            }
        }
    }
}
```

**关键区别**:

| | `gen {}` | `async {}` | `iter::from_fn` |
|---|----------|-----------|-----------------|
| 暂停原因 | `yield` | `.await` | `return` |
| 恢复方式 | `next()` | 事件循环 | 下次调用 |
| 状态保存 | 隐式 | 隐式 | 显式闭包捕获 |
| 用途 | 数据流 | 并发 | 迭代器适配 |

---

## 🔀 与 Iterators 对比

### 传统 Iterator

```rust
struct Fibonacci {
    a: u64,
    b: u64,
}

impl Iterator for Fibonacci {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.a;
        (self.a, self.b) = (self.b, self.a + self.b);
        Some(val)
    }
}
```

### 生成器版本

```rust
let fib = gen {
    let mut a = 0;
    let mut b = 1;
    loop {
        yield a;
        (a, b) = (b, a + b);
    }
};
```

**代码量减少 60%+**，状态管理自动化。

---

## 📊 与 Async 对比

```rust
// Async: 等待外部事件
async fn fetch_data() -> Data {
    let response = request().await;  // 等待 I/O
    parse(response).await
}

// Gen: 生产数据流
fn sensor_stream() -> impl Iterator<Item = Reading> {
    gen move {
        let sensor = Sensor::open();
        loop {
            yield sensor.read();  // 产生数据
            std::thread::sleep(Duration::from_millis(100));
        }
    }
}
```

---

## 🔄 实际用例

### 文件行过滤流

```rust
fn grep_lines(file: File, pattern: &str) -> impl Iterator<Item = String> + '_ {
    gen move {
        let reader = BufReader::new(file);
        for line in reader.lines().flatten() {
            if line.contains(pattern) {
                yield line;
            }
        }
    }
}
```

### 组合生成器

```rust
fn flatten_nested<T>(nested: Vec<Vec<T>>) -> impl Iterator<Item = T> {
    gen move {
        for inner in nested {
            for item in inner {
                yield item;
            }
        }
    }
}
```

---

## ⚠️ 当前限制

- **Nightly only**: 需要 `#![feature(gen_blocks, yield_expr)]`
- **生命周期**: `yield` 借用的值需要谨慎管理
- **性能**: 当前实现可能不如手写 Iterator 优化
- **调试**: 生成器状态机调试较复杂

---

## 🔗 参考资源

- [RFC 3513: Gen Blocks](https://github.com/rust-lang/rfcs/pull/3513)
- [项目 C08 算法模块](../../crates/c08_algorithms/)
- [Rust Nightly 文档](https://doc.rust-lang.org/nightly/unstable-book/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
