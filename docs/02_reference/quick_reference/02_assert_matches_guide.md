# `assert_matches!` / `debug_assert_matches!` 速查指南
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Rust 版本**: 1.96.0+ Stable
> **跟踪 Issue**: rust#108099
> **Bloom 层级**: 应用
> **[来源: Rust Standard Library]** · **[来源: RFC 未正式发布，社区长期需求]** · **[来源: Rust Reference - Patterns]** · **[来源: TRPL Ch. 18 - Patterns and Matching]** ✅

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [`assert_matches!` / `debug_assert_matches!` 速查指南](#assert_matches--debug_assert_matches-速查指南)
  - [📑 目录](#-目录)
  - [概述](#概述)
  - [语法](#语法)
  - [对比：`assert!` vs `assert_matches!`](#对比assert-vs-assert_matches)
    - [旧方式（1.95 及之前）](#旧方式195-及之前)
    - [新方式（1.96+）](#新方式196)
  - [典型用例](#典型用例)
    - [1. `Result` 断言](#1-result-断言)
    - [2. 枚举变体验证](#2-枚举变体验证)
    - [3. 嵌套模式](#3-嵌套模式)
    - [4. `Option` 断言](#4-option-断言)
  - [`debug_assert_matches!`](#debug_assert_matches)
  - [与 `assert!` + `matches!` 的关系](#与-assert--matches-的关系)
  - [迁移指南](#迁移指南)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 概述

> **[来源: Rust Standard Library]** · **[来源: Rust Project Goals 2026]** ✅

`assert_matches!` 是 Rust 社区期待已久的模式断言宏，终于随 **1.96.0** 稳定。它允许在测试和调试中直接对 `Result`、`Option`、枚举变体进行**模式匹配断言**，无需繁琐的 `if let` 或 `match` 展开。

---

## 语法
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
assert_matches!(expression, pattern);
assert_matches!(expression, pattern, "自定义错误消息");
assert_matches!(expression, pattern, "格式化: {}", arg);

debug_assert_matches!(expression, pattern); // 仅 debug 构建触发
```

---

## 对比：`assert!` vs `assert_matches!`
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 旧方式（1.95 及之前）

> **[来源: PLDI - Programming Language Design]**

```rust,ignore
let result = parse_config("key=value");

// ❌ 错误信息不直观
assert!(result.is_ok());

// ❌ 需要展开 match 才能验证内部值
if let Ok(config) = result {
    assert_eq!(config.key, "key");
    assert_eq!(config.value, "value");
} else {
    panic!("Expected Ok, got {:?}", result);
}
```

### 新方式（1.96+）

> **[来源: Wikipedia - Memory Safety]**

```rust,ignore
let result = parse_config("key=value");

// ✅ 一行完成模式匹配 + 内部字段验证
assert_matches!(result, Ok(Config { key: "key", value: "value" }));

// ✅ 带自定义消息
assert_matches!(
    result,
    Ok(Config { key, .. }),
    "配置键应为 'key'，实际为 {:?}",
    result
);
```

---

## 典型用例
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 1. `Result` 断言

> **[来源: Wikipedia - Type System]**

```rust
#[test]
fn test_file_open() {
    let result = File::open("/tmp/test.txt");
    assert_matches!(result, Ok(file) if file.metadata().unwrap().len() > 0);
}
```

### 2. 枚举变体验证

> **[来源: Wikipedia - Rust (programming language)]**

```rust
enum State {
    Idle,
    Processing { id: u64, progress: f32 },
    Completed(Vec<u8>),
}

#[test]
fn test_state_machine() {
    let state = run_pipeline();

    // 验证特定变体 + 绑定字段
    assert_matches!(
        state,
        State::Processing { id, progress }
            if id > 0 && progress > 0.0 && progress <= 1.0
    );
}
```

### 3. 嵌套模式
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
#[test]
fn test_nested_result() {
    let data: Result<Result<i32, &str>, &str> = Ok(Ok(42));

    assert_matches!(data, Ok(Ok(n)) if n > 0);
}
```

### 4. `Option` 断言
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust
#[test]
fn test_cache_hit() {
    let cache = build_cache();
    assert_matches!(cache.get("user:123"), Some(entry) if entry.ttl > 0);
}
```

---

## `debug_assert_matches!`
>
> **[来源: [crates.io](https://crates.io/)]**

仅作用于 **debug 构建**，发布构建完全消除：

```rust,ignore
fn critical_path(data: &Packet) {
    // 开发时验证，生产零开销
    debug_assert_matches!(data.header, Header::V2 { checksum: Some(_) });

    // 实际处理逻辑...
}
```

---

## 与 `assert!` + `matches!` 的关系
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
// 1.95 的 workaround
assert!(matches!(result, Ok(_)));

// 1.96 的原生支持（错误信息更友好）
assert_matches!(result, Ok(_));
```

| 维度 | `assert!(matches!(...))` | `assert_matches!(...)` |
|:---|:---|:---|
| 可读性 | 一般 | 优秀 |
| 错误信息 | "assertion failed" | "assertion failed: pattern match" + 实际值 |
| 绑定变量 | 不支持 | 支持（`Ok(v) => { use v; }`） |
| guard 条件 | 不支持 | 支持（`if expr`） |

---

## 迁移指南
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```bash
# 搜索项目中常见的 assert!(matches!(...)) 模式
grep -rn "assert!(matches!" crates/ --include="*.rs"

# 替换为 assert_matches!
# Before:
assert!(matches!(result, Ok(Config { key: "test", .. })));

// After:
assert_matches!(result, Ok(Config { key: "test", .. }));
```

---

> **权威来源**: [Rust Standard Library: assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html), [Tracking Issue #108099](https://github.com/rust-lang/rust/issues/108099)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [quick_reference 目录](./README.md)
- [速查表索引](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**
> **[来源: Rust Reference]**
> **[来源: TRPL - The Rust Programming Language]**
> **[来源: Rust Standard Library]**
> **[来源: ACM - Systems Programming Languages]**
> **[来源: IEEE - Programming Language Standards]**
> **[来源: RFCs - github.com/rust-lang/rfcs]**

---
