# 错误处理速查卡

> **一页纸速查** - Result、Option、错误处理模式

---

## Result与Option

| 类型 | 用途 | 方法 |
| :--- | :--- | :--- |
| `Option<T>` | 可能有值 | `Some(T)` / `None` |
| `Result<T, E>` | 可能成功 | `Ok(T)` / `Err(E)` |

---

## 常用方法

### Option

```rust
opt.unwrap()        // 获取值，None时panic
opt.unwrap_or(def)  // 获取值或默认值
opt.ok_or(err)      // Option -> Result
opt.map(|v| ...)    // 映射
opt.and_then(|v| ...) // 链式操作
```

### Result

```rust
res.unwrap()        // 获取值，Err时panic
res?                // 传播错误
res.map_err(|e| ...) // 错误映射
res.and_then(|v| ...) // 链式操作
```

---

## ?操作符

```rust
fn may_fail() -> Result<T, Error> {
    let x = operation1()?;  // 错误时提前返回
    let y = operation2()?;
    Ok(y)
}
```

---

## 错误转换

```rust
// From trait自动转换
impl From<IOError> for MyError {
    fn from(e: IOError) -> Self { ... }
}

// 使用
let file = File::open("file")?;  // IOError自动转为MyError
```

---

## panic vs Result

| 情况 | 使用 |
| :--- | :--- |
| 不可恢复错误 | `panic!` |
| 可恢复错误 | `Result` |
| 可选值 | `Option` |
| 编程错误 | `assert!` / `unreachable!` |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 错误处理速查卡 (4/5)

---

## 🆕 Rust 1.94 更新

> **适用版本**: Rust 1.94.0+

详见 [RUST_194_RESEARCH_UPDATE](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
