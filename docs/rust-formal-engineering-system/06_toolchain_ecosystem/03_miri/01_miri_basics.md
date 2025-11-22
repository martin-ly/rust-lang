# Miri 基础（Miri Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [Miri 基础](#miri-基础miri-basics)
  - [概述](#概述)
  - [安装和配置](#安装和配置)
  - [基本使用](#基本使用)
  - [检测未定义行为](#检测未定义行为)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Miri 是 Rust 的 MIR 解释器，可以在编译时检测未定义行为（Undefined Behavior）。它通过解释 MIR（Mid-level Intermediate Representation）来执行 Rust 代码，并检测各种内存安全问题。

## 安装和配置

### 安装 Miri

```bash
# 使用 rustup 安装
rustup component add miri

# 更新 Miri
rustup component update miri
```

### 配置 Cargo

在 `Cargo.toml` 中添加：

```toml
[dev-dependencies]
# Miri 会自动处理，通常不需要显式添加依赖
```

## 基本使用

### 运行测试

```bash
# 使用 Miri 运行测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 运行示例
cargo miri run --example example_name
```

### 运行二进制文件

```bash
# 使用 Miri 运行二进制文件
cargo miri run

# 运行特定二进制
cargo miri run --bin binary_name
```

## 检测未定义行为

### 内存安全问题

Miri 可以检测以下问题：

1. **使用未初始化的内存**
2. **内存泄漏**
3. **数据竞争**
4. **悬垂指针**
5. **越界访问**
6. **对齐问题**

### 示例：检测未初始化内存

```rust
// ❌ 错误示例：使用未初始化的内存
fn uninitialized_memory() {
    let x: i32;
    println!("{}", x);  // Miri 会检测到未初始化内存的使用
}

// ✅ 正确示例
fn initialized_memory() {
    let x: i32 = 0;
    println!("{}", x);
}
```

### 示例：检测悬垂指针

```rust
// ❌ 错误示例：悬垂指针
fn dangling_pointer() -> &i32 {
    let x = 5;
    &x  // Miri 会检测到悬垂指针
}

// ✅ 正确示例
fn valid_pointer() -> i32 {
    let x = 5;
    x
}
```

### 示例：检测越界访问

```rust
// ❌ 错误示例：越界访问
fn out_of_bounds() {
    let arr = [1, 2, 3];
    println!("{}", arr[5]);  // Miri 会检测到越界访问
}

// ✅ 正确示例
fn safe_access() {
    let arr = [1, 2, 3];
    if let Some(value) = arr.get(1) {
        println!("{}", value);
    }
}
```

## 实践示例

### 示例 1：检测内存泄漏

```rust
use std::rc::Rc;

#[test]
fn test_memory_leak() {
    // Miri 可以检测到循环引用导致的内存泄漏
    let a = Rc::new(5);
    let b = Rc::clone(&a);
    // 如果形成循环引用，Miri 会报告
}
```

### 示例 2：检测数据竞争

```rust
use std::sync::Arc;
use std::thread;

#[test]
fn test_data_race() {
    let data = Arc::new(5);
    let data1 = Arc::clone(&data);
    let data2 = Arc::clone(&data);

    // Miri 可以检测到潜在的数据竞争
    let handle1 = thread::spawn(move || {
        // 如果这里尝试修改 data1，Miri 会检测到问题
        println!("{}", data1);
    });

    let handle2 = thread::spawn(move || {
        println!("{}", data2);
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

### 示例 3：检测对齐问题

```rust
use std::mem;

#[test]
fn test_alignment() {
    // Miri 可以检测到对齐问题
    let data: [u8; 8] = [0; 8];

    // 如果尝试以错误的对齐方式读取，Miri 会检测到
    unsafe {
        let ptr = data.as_ptr() as *const i32;
        // 如果对齐不正确，Miri 会报告
        let _value = *ptr;
    }
}
```

### 示例 4：检测未定义行为

```rust
#[test]
fn test_undefined_behavior() {
    // Miri 可以检测到各种未定义行为
    let mut x = 5;
    let y = &mut x;
    let z = &x;  // Miri 会检测到同时存在可变和不可变借用

    println!("{}", z);
    *y = 10;
}
```

## 最佳实践

### 1. 在 CI/CD 中集成 Miri

```yaml
# .github/workflows/miri.yml
name: Miri

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          components: miri
      - name: Run Miri
        run: cargo miri test
```

### 2. 使用 Miri 检查 unsafe 代码

```rust
// 对于包含 unsafe 代码的模块，使用 Miri 进行额外检查
#[cfg(miri)]
mod miri_tests {
    use super::*;

    #[test]
    fn test_unsafe_code() {
        // 使用 Miri 测试 unsafe 代码
        unsafe {
            // 测试 unsafe 代码的正确性
        }
    }
}
```

### 3. 配置 Miri 选项

```bash
# 设置堆栈大小
MIRI_STACK_SIZE=1000000 cargo miri test

# 设置内存限制
MIRI_MEMORY_LIMIT=1000000 cargo miri test

# 启用更多检查
MIRI_FLAGS="-- -Zmiri-disable-isolation" cargo miri test
```

### 4. 与 Clippy 结合使用

```bash
# 先运行 Clippy，再运行 Miri
cargo clippy -- -D warnings
cargo miri test
```

## 常见问题

### 问题 1：Miri 运行缓慢

**解决方案**：
- 只对关键测试使用 Miri
- 使用 `#[cfg(miri)]` 条件编译
- 减少测试数据量

### 问题 2：误报

**解决方案**：
- 检查代码逻辑
- 使用 `#[allow(unsafe_op_in_unsafe_fn)]` 等属性
- 查看 Miri 的详细输出

### 问题 3：某些库不兼容

**解决方案**：
- 使用 `#[cfg(not(miri))]` 跳过不兼容的测试
- 寻找替代库
- 报告问题给库维护者

## 参考资料

- [Miri 索引](./00_index.md)
- [Miri 官方文档](https://github.com/rust-lang/miri)
- [Rust 未定义行为](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回工具链生态: [`../00_index.md`](../00_index.md)
