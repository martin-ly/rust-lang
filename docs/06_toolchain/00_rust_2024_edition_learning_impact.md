# Rust 2024 Edition 学习影响

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录 {#-目录}

- [Rust 2024 Edition 学习影响](#rust-2024-edition-学习影响)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [一、Rust 2024 Edition 概览](#一rust-2024-edition-概览)
  - [二、对学习路径的主要影响](#二对学习路径的主要影响)
    - [2.1 所有权与借用（C01）](#21-所有权与借用c01)
    - [2.2 类型系统（C02）](#22-类型系统c02)
    - [2.3 控制流（C03）](#23-控制流c03)
    - [2.4 宏系统（C11）](#24-宏系统c11)
    - [2.5 其他](#25-其他)
  - [三、学习建议](#三学习建议)
  - [四、代码示例](#四代码示例)
    - [4.1 2024 Edition 迁移示例](#41-2024-edition-迁移示例)
    - [4.2 `unsafe_op_in_unsafe_fn` 示例](#42-unsafe_op_in_unsafe_fn-示例)
    - [4.3 `static mut` 替代方案](#43-static-mut-替代方案)
    - [4.4 RPIT 生命周期捕获](#44-rpit-生命周期捕获)
    - [4.5 `if let` 临时作用域](#45-if-let-临时作用域)
    - [4.6 宏片段说明符更新](#46-宏片段说明符更新)
    - [4.7 `unsafe` 属性](#47-unsafe-属性)
    - [4.8 Unsafe `extern` 块](#48-unsafe-extern-块)
  - [五、迁移指南与兼容性检查](#五迁移指南与兼容性检查)
    - [5.1 迁移检查清单](#51-迁移检查清单)
    - [5.2 兼容性检查代码](#52-兼容性检查代码)
    - [5.3 条件编译处理版本差异](#53-条件编译处理版本差异)
  - [六、相关文档与形式化链接](#六相关文档与形式化链接)
    - [官方文档](#官方文档)
    - [形式化参考](#形式化参考)
    - [项目内部文档](#项目内部文档)

## 一、Rust 2024 Edition 概览

Rust 2024 Edition 是 Rust 迄今为止**最大的 Edition 更新**，于 2025 年 2 月 20 日随 Rust 1.85.0 稳定发布。本项目已全面采用 `edition = "2024"`（根 Cargo.toml 及 12 个 crate）。

---

## 二、对学习路径的主要影响

### 2.1 所有权与借用（C01）

| 变更 | 影响 | 学习建议 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **禁止 `static mut` 引用** | 旧代码中 `&static mut` 将报错 | 使用 `Sync` 类型或 `UnsafeCell` 替代 |

### 2.2 类型系统（C02）

| 变更 | 影响 | 学习建议 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Never 类型 (`!`) fallback 变更** | `!` 在类型推断中的行为更一致 | 关注 `panic!`、`loop` 等表达式的类型 |

### 2.3 控制流（C03）

| 变更 | 影响 | 学习建议 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Match ergonomics 保留** | 部分 match 模式匹配行为调整 | 参考 [Edition Guide](https://doc.rust-lang.org/edition-guide/) |

### 2.4 宏系统（C11）

| 变更 | 影响 | 学习建议 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`unsafe` 属性** | `unsafe` 可作为属性使用 | 与 `unsafe fn` 配合理解 |

### 2.5 其他

| 变更 | 影响 |
| :--- | :--- | :--- | :--- | :--- |
| **`cfg` 谓词关键词** | 使用关键词作为 `cfg` 谓词将报错 |

---

## 三、学习建议

1. **初学者**：按 C01→C02→C03 顺序学习，2024 变更对基础语法影响较小。
2. **进阶者**：重点理解 RPIT 生命周期、`unsafe_op_in_unsafe_fn`、`if let` 临时作用域。
3. **迁移者**：若从 2021 Edition 迁移，参考 [Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/)。

---

## 四、代码示例

### 4.1 2024 Edition 迁移示例

**从 2021 Edition 迁移到 2024 Edition**:

```toml
# Cargo.toml - 更新 edition
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"  # 从 "2021" 更新
rust-version = "1.85"
```

```bash
# 使用 cargo fix 自动修复迁移问题
cargo fix --edition
cargo fix --edition-idioms
```

### 4.2 `unsafe_op_in_unsafe_fn` 示例

```rust
// Rust 2021 - unsafe fn 内不需要显式标记 unsafe 块
#[edition = "2021"]
unsafe fn old_style() {
    // 隐式 unsafe 块
    let ptr = std::ptr::null::<i32>();
    *ptr; // 危险操作但没有显式标记
}

// Rust 2024 - 必须在 unsafe fn 内显式使用 unsafe 块
#[edition = "2024"]
unsafe fn new_style() {
    // ✅ 正确：显式标记 unsafe 块
    unsafe {
        let ptr = std::ptr::null::<i32>();
        // *ptr; // 危险操作在 unsafe 块内
    }
}
```

### 4.3 `static mut` 替代方案

```rust
// ❌ Rust 2024 禁止：&static mut 引用
// static mut COUNTER: i32 = 0;
// let _ = unsafe { &mut COUNTER };

// ✅ 正确做法 1：使用 Sync 类型
use std::sync::atomic::{AtomicI32, Ordering};
static COUNTER: AtomicI32 = AtomicI32::new(0);

fn increment() {
    COUNTER.fetch_add(1, Ordering::Relaxed);
}

// ✅ 正确做法 2：使用 UnsafeCell（需要 unsafe）
use std::cell::UnsafeCell;
static DATA: UnsafeCell<i32> = UnsafeCell::new(0);

unsafe fn modify_data() {
    *DATA.get() = 42;
}

// ✅ 正确做法 3：使用 thread_local
thread_local! {
    static LOCAL_COUNTER: Cell<i32> = Cell::new(0);
}
```

### 4.4 RPIT 生命周期捕获

```rust
// Rust 2024 - 返回 impl Trait 的生命周期捕获
use std::future::Future;

// 在 2024 Edition 中，async fn 的生命周期捕获更清晰
async fn process_data(data: &str) -> impl Future<Output = String> + '_ {
    // 显式捕获 'data' 的生命周期
    async move {
        format!("Processed: {}", data)
    }
}

// RPIT (Return Position Impl Trait) 生命周期规则
fn get_iterator<'a>(data: &'a [i32]) -> impl Iterator<Item = i32> + 'a {
    // 2024 Edition 更精确地捕获生命周期
    data.iter().copied()
}
```

### 4.5 `if let` 临时作用域

```rust
use std::sync::Mutex;

// Rust 2024 - if let 临时值作用域变更
fn process_mutex() {
    let data = Mutex::new(vec![1, 2, 3]);

    // 在 2024 Edition 中，临时值的存活期更清晰
    if let Some(item) = data.lock().unwrap().first() {
        // temp value 在 if let 条件结束后立即释放
        println!("First item: {}", item);
    } // lock 在这里释放

    // 因此这里可以再次获取 lock
    if let Some(item) = data.lock().unwrap().last() {
        println!("Last item: {}", item);
    }
}
```

### 4.6 宏片段说明符更新

```rust
// Rust 2024 - 宏片段说明符增强
macro_rules! create_fn {
    // 新的片段说明符支持
    ($name:ident $(, $arg:ident: $ty:ty)*) -> $ret:ty $body:block) => {
        fn $name($($arg: $ty),*) -> $ret $body
    };
}

create_fn!(add, a: i32, b: i32) -> i32 {
    a + b
}
```

### 4.7 `unsafe` 属性

```rust
// Rust 2024 - unsafe 可以作为属性使用
#[unsafe(no_mangle)]
pub extern "C" fn my_c_function() {
    // 函数实现
}

// 与 unsafe fn 配合
#[unsafe(link_section = ".custom_section")]
static DATA: [u8; 4] = [0x01, 0x02, 0x03, 0x04];
```

### 4.8 Unsafe `extern` 块

```rust
// Rust 2024 - extern 块可以标记为 unsafe
unsafe extern "C" {
    // 整个 extern 块内的函数都是 unsafe 的
    fn dangerous_function() -> i32;
    fn another_dangerous_function(ptr: *const u8) -> *const u8;
}

fn use_ffi() {
    // 必须在 unsafe 块中调用
    unsafe {
        let result = dangerous_function();
        println!("Result: {}", result);
    }
}
```

---

## 五、迁移指南与兼容性检查

### 5.1 迁移检查清单

```bash
# 1. 检查当前 Rust 版本
rustc --version  # 需要 1.85+

# 2. 运行 cargo fix 进行自动迁移
cargo fix --edition
cargo fix --edition-idioms

# 3. 检查未修复的手动迁移项
cargo check --all-targets --all-features

# 4. 运行测试确保功能正常
cargo test --all

# 5. 检查 Clippy lints
cargo clippy --all-targets --all-features
```

### 5.2 兼容性检查代码

```rust
// 在 build.rs 或 CI 中检查 Edition 兼容性
#[cfg(not(edition = "2024"))]
compile_error!("This crate requires Rust 2024 Edition");

// 检查 Rust 版本
const REQUIRED_VERSION: &str = "1.85.0";

fn check_rust_version() {
    let version = env!("RUSTC_VERSION");
    println!("cargo:rustc-check-cfg=cfg(edition2024)");
}
```

### 5.3 条件编译处理版本差异

```rust
// 根据 Edition 条件编译不同代码
#[cfg(edition = "2024")]
mod edition2024 {
    pub unsafe fn safe_unsafe_op() {
        unsafe {
            // 2024 Edition 风格
        }
    }
}

#[cfg(not(edition = "2024"))]
mod edition2021 {
    pub unsafe fn safe_unsafe_op() {
        // 2021 Edition 风格
    }
}
```

---

## 六、相关文档与形式化链接

### 官方文档

- [Rust Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/)
- [Rust Reference - Editions](https://doc.rust-lang.org/reference/items/extern-crates.html)
- [Unsafe Rust Guide](https://doc.rust-lang.org/nomicon/)

### 形式化参考

- [类型系统形式化规范](https://doc.rust-lang.org/reference/type-system.html)
- [生命周期与借用检查](https://doc.rust-lang.org/reference/lifetime-elision.html)
- [所有权系统形式化](https://doc.rust-lang.org/reference/ownership.html)
- [Rust 形式化语义 (Ferrocene)](https://spec.ferrocene.dev/)

### 项目内部文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性深度解析](./09_rust_1.93_compatibility_deep_dive.md)
- [Unsafe Rust 指南](../05_guides/UNSAFE_RUST_GUIDE.md)

---

**最后对照 releases.rs**: 2026-02-14
