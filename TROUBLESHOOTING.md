# 故障排查指南 (Troubleshooting)

> **最后更新**: 2026-03-08
> **适用版本**: Rust 1.94.0+

---

## 目录

- [故障排查指南 (Troubleshooting)](#故障排查指南-troubleshooting)
  - [目录](#目录)
  - [编译错误](#编译错误)
    - [借用检查错误](#借用检查错误)
    - [生命周期错误](#生命周期错误)
    - [类型不匹配](#类型不匹配)
  - [运行时错误](#运行时错误)
    - [Panic](#panic)
    - [死锁](#死锁)
  - [性能问题](#性能问题)
    - [编译时间过长](#编译时间过长)
    - [运行速度慢](#运行速度慢)
  - [常见问题速查](#常见问题速查)
  - [相关文档](#相关文档)

---

## 编译错误

### 借用检查错误

```rust
error[E0502]: cannot borrow `x` as mutable because it is also borrowed as immutable
```

**解决方案**:

1. 缩小不可变借用的作用域
2. 使用 `clone()` 创建副本
3. 重新设计数据结构，避免同时借用

### 生命周期错误

```rust
error[E0597]: `x` does not live long enough
```

**解决方案**:

1. 确保引用的数据比引用本身存活更久
2. 考虑使用 `String` 代替 `&str` 拥有数据
3. 使用智能指针如 `Rc` 或 `Arc`

### 类型不匹配

```rust
error[E0308]: mismatched types
```

**解决方案**:

1. 使用 `.into()` 或 `as` 进行类型转换
2. 检查泛型参数是否正确
3. 使用 turbofish 语法明确指定类型：`::<Type>`

---

## 运行时错误

### Panic

```rust
thread 'main' panicked at 'explicit panic', src/main.rs:2:5
```

**调试步骤**:

1. 设置 `RUST_BACKTRACE=1` 查看调用栈
2. 使用 `unwrap()` 和 `expect()` 的替代方案
3. 添加日志输出定位问题

### 死锁

**症状**: 程序卡住不继续执行

**解决方案**:

1. 确保锁的获取顺序一致
2. 使用 `try_lock()` 替代 `lock()`
3. 缩小临界区范围

---

## 性能问题

### 编译时间过长

**优化建议**:

1. 使用 `cargo build --release` 的增量编译
2. 分割大 crate 为多个小 crate
3. 使用 `sccache` 缓存编译结果

### 运行速度慢

**分析工具**:

```bash
# 使用 cargo flamegraph 生成火焰图
cargo flamegraph

# 使用 cargo prof 进行性能分析
cargo prof --release
```

---

## 常见问题速查

| 问题 | 快速解决 |
|------|----------|
| `cargo build` 太慢 | 使用 `cargo check` 快速检查 |
| 找不到模块 | 检查 `mod` 声明和文件路径 |
| 测试失败 | 运行 `cargo test -- --nocapture` 查看输出 |
| 依赖冲突 | 使用 `cargo tree` 分析依赖树 |

---

## 相关文档

- [README.md](./README.md)
- [CONTRIBUTING.md](./CONTRIBUTING.md)
- [PROJECT_STRUCTURE.md](./PROJECT_STRUCTURE.md)
