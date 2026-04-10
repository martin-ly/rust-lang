# Rust 1.95/1.96 特性速查表

> **版本**: Rust 1.95 - 1.96
> **更新日期**: 2026-04-10
> **适用版本**: stable

---

## 目录

- [Rust 1.95/1.96 特性速查表](#rust-195196-特性速查表)
  - [目录](#目录)
  - [if let guards 语法](#if-let-guards-语法)
    - [基本语法](#基本语法)
    - [链式守卫](#链式守卫)
    - [对比表](#对比表)
    - [代码示例](#代码示例)
  - [Range 类型对比](#range-类型对比)
    - [类型总览](#类型总览)
    - [使用场景速查](#使用场景速查)
    - [Range 方法](#range-方法)
  - [新 Lint 规则](#新-lint-规则)
    - [Rust 1.96 新增 Lints](#rust-196-新增-lints)
    - [配置方式](#配置方式)
    - [命令行使用](#命令行使用)
  - [快速参考示例](#快速参考示例)
    - [if let guards 模板](#if-let-guards-模板)
    - [Range 常用模式](#range-常用模式)
    - [PinCoerceUnsized 快速使用](#pincoerceunsized-快速使用)
    - [元组 Coercion 示例](#元组-coercion-示例)
  - [迁移检查清单](#迁移检查清单)
  - [相关链接](#相关链接)

---

## if let guards 语法

### 基本语法

```rust
match value {
    pattern if let Some(x) = option => { /* use x */ }
    _ => {}
}
```

### 链式守卫

```rust
match event {
    Event::Click(pos)
        if let Some(x) = pos.x
        && let Some(y) = pos.y
        && x > 0 && y > 0 =>
    {
        // 处理有效点击
    }
    _ => {}
}
```

### 对比表

| 场景 | 旧写法 (Rust < 1.95) | 新写法 (Rust 1.95+) |
|------|---------------------|-------------------|
| 简单守卫 | `if let Some(x) = opt { match... }` | `pattern if let Some(x) = opt =>` |
| 嵌套守卫 | 多层 if 嵌套 | 链式 `if let ... && let ...` |
| 组合条件 | `if let Some(x) = opt && x > 0` 不支持 | `pattern if let Some(x) = opt && x > 0 =>` |

### 代码示例

```rust
// ✅ Rust 1.95+ 推荐写法
match message {
    Message::Text(content) if let Some(user) = current_user => {
        println!("{}: {}", user.name, content);
    }
    Message::Text(content) => {
        println!("Anonymous: {}", content);
    }
    _ => {}
}

// ❌ 旧写法（仍可编译，但不推荐）
match message {
    Message::Text(content) => {
        if let Some(user) = current_user {
            println!("{}: {}", user.name, content);
        } else {
            println!("Anonymous: {}", content);
        }
    }
    _ => {}
}
```

---

## Range 类型对比

### 类型总览

| 类型 | 语法 | 包含开始 | 包含结束 | 迭代性 |
|------|------|:--------:|:--------:|:------:|
| `Range` | `a..b` | ✅ | ❌ | ✅ |
| `RangeFrom` | `a..` | ✅ | N/A | ✅ (无限) |
| `RangeTo` | `..b` | N/A | ❌ | ❌ |
| `RangeFull` | `..` | N/A | N/A | ❌ |
| `RangeInclusive` | `a..=b` | ✅ | ✅ | ✅ |
| `RangeToInclusive` | `..=b` | N/A | ✅ | ❌ |

### 使用场景速查

```rust
// 数组/向量切片
let slice = &arr[0..5];        // 索引 0-4
let slice = &arr[0..=5];       // 索引 0-5

// 循环迭代
for i in 0..10 { }             // 0-9
for i in 0..=10 { }            // 0-10

// 模式匹配
match x {
    0..10 => "single digit",   // 0-9
    10..=99 => "two digits",   // 10-99
    _ => "other",
}

// 集合操作
vec.drain(0..5);               // 移除 0-4
vec.get(0..=5);                // 获取 0-5
```

### Range 方法

| 方法 | 适用类型 | 说明 |
|------|----------|------|
| `.contains(&x)` | 所有 Range | 检查值是否在范围内 |
| `.is_empty()` | Range, RangeInclusive | 范围是否为空 |
| `.len()` | Range, RangeInclusive | 范围长度 |
| `.start()` | Range, RangeFrom, RangeInclusive | 获取起始值 |
| `.end()` | Range, RangeTo, RangeInclusive | 获取结束值 |

---

## 新 Lint 规则

### Rust 1.96 新增 Lints

| Lint | 默认级别 | 说明 | 修复建议 |
|------|----------|------|----------|
| `unused_tuple_struct_fields` | Warn | 元组结构体字段未使用 | 删除或添加 `_` 前缀 |
| `redundant_guards` | Warn | 冗余的 match 守卫 | 简化守卫条件 |
| `opaque_hidden_inferred_bound` | Warn | 不透明类型隐藏推断边界 | 显式指定类型边界 |

### 配置方式

```rust
// 在源文件顶部
#![allow(unused_tuple_struct_fields)]
#![warn(redundant_guards)]
#![deny(opaque_hidden_inferred_bound)]
```

```toml
# 在 Cargo.toml
[lints.rust]
unused_tuple_struct_fields = "warn"
redundant_guards = "warn"
opaque_hidden_inferred_bound = "allow"
```

### 命令行使用

```bash
# 启用特定 lint
cargo build -- -W unused_tuple_struct_fields

# 禁用特定 lint
cargo build -- -A redundant_guards

# 将 lint 视为错误
cargo build -- -D unused_tuple_struct_fields
```

---

## 快速参考示例

### if let guards 模板

```rust
// 模板 1: 单一守卫
match value {
    Pattern(x) if let Some(y) = option => { }
    _ => { }
}

// 模板 2: 链式守卫
match value {
    Pattern(x)
        if let Some(a) = opt1
        && let Some(b) = opt2
        && a == b => { }
    _ => { }
}

// 模板 3: 守卫 + 额外条件
match value {
    Pattern(x)
        if let Some(y) = option
        && y > 0
        && y < 100 => { }
    _ => { }
}
```

### Range 常用模式

```rust
// 模式 1: 检查值范围
if (0..100).contains(&value) { }

// 模式 2: 范围交集
let r1 = 0..10;
let r2 = 5..15;
let intersection = r1.start.max(r2.start)..r1.end.min(r2.end);

// 模式 3: 切片操作
let sub = &vec[start..end];
let sub_inclusive = &vec[start..=end];

// 模式 4: 模式匹配范围
match age {
    0..13 => "child",
    13..20 => "teenager",
    20..=65 => "adult",
    _ => "senior",
}
```

### PinCoerceUnsized 快速使用

```rust
use std::pin::Pin;
use std::future::Future;

// 将具体 Future 转为 trait object
fn into_dyn_future<F>(fut: F) -> Pin<Box<dyn Future<Output = F::Output>>>
where
    F: Future + 'static,
{
    Box::pin(fut)
}

// 使用
async fn demo() {
    let fut = into_dyn_future(async { 42 });
    let result = fut.await;
}
```

### 元组 Coercion 示例

```rust
// 类型转换函数
fn widen<T, U>((a, b): (T, U)) -> (i64, i64)
where
    T: Into<i64>,
    U: Into<i64>,
{
    (a.into(), b.into())
}

// 使用
let narrow: (i8, i16) = (1, 2);
let wide: (i64, i64) = widen(narrow);
```

---

## 迁移检查清单

- [ ] 运行 `rustup update` 升级到 1.96
- [ ] 运行 `cargo check` 检查兼容性
- [ ] 运行 `cargo fix` 自动修复问题
- [ ] 检查新的 lint 警告
- [ ] 运行 `cargo test` 确保测试通过
- [ ] 更新 CI/CD 配置中的 Rust 版本
- [ ] 更新项目文档中的版本要求

---

## 相关链接

- [官方 Release Notes](https://blog.rust-lang.org/)
- [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)
- [Cargo Book - Lints](https://doc.rust-lang.org/cargo/reference/manifest.html#the-lints-section)
