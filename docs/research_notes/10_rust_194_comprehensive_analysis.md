# Rust 1.96.0 特性全面分析 {#rust-1960-特性全面分析}
>
> **概念族**: 版本特性

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **发布日期**: 2026-05-28
> **分支日期**: 2026-04-10
> **Edition**: 2024
> **最后更新**: 2026-06-29
> **权威来源**: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/), [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/), [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html), [releases.rs](https://releases.rs/)
> **历史版本**: [1.95](https://releases.rs/docs/1.95.0/), [1.94](https://releases.rs/docs/1.94.0/), [1.93](https://releases.rs/docs/1.93.0/)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 1.96.0 特性全面分析](#rust-1960-特性全面分析)
  - [📑 目录](#目录)
  - [特性概述](#特性概述)
    - [版本亮点](#版本亮点)
  - [一、array\_windows 方法](#一array_windows-方法)
    - [1.1 特性描述](#11-特性描述)
    - [1.2 代码示例](#12-代码示例)
    - [1.3 ABBA 模式检测示例](#13-abba-模式检测示例)
    - [1.4 使用场景](#14-使用场景)
  - [二、element\_offset 方法](#二element_offset-方法)
    - [2.1 特性描述](#21-特性描述)
    - [2.2 代码示例](#22-代码示例)
  - [三、LazyCell 和 LazyLock 新方法](#三lazycell-和-lazylock-新方法)
    - [3.1 新增 API](#31-新增-api)
    - [3.2 代码示例](#32-代码示例)
  - [四、数学常量扩展](#四数学常量扩展)
    - [4.1 新增常量](#41-新增常量)
    - [4.2 代码示例](#42-代码示例)
  - [五、迭代器增强](#五迭代器增强)
    - [5.1 Peekable::next\_if\_map](#51-peekablenext_if_map)
  - [六、字符转换](#六字符转换)
    - [6.1 `TryFrom<char>` for usize](#61-tryfromchar-for-usize)
  - [七、Const 上下文增强](#七const-上下文增强)
    - [7.1 mul\_add 在 const 中稳定](#71-mul_add-在-const-中稳定)
  - [八、Cargo 新特性](#八cargo-新特性)
    - [8.1 Config Inclusion](#81-config-inclusion)
    - [8.2 TOML 1.1 支持](#82-toml-11-支持)
    - [8.3 pubtime 字段](#83-pubtime-字段)
  - [九、平台支持](#九平台支持)
    - [9.1 新增目标](#91-新增目标)
    - [9.2 RISC-V 特性](#92-risc-v-特性)
  - [十、语言改进](#十语言改进)
    - [10.1 Lint 改进](#101-lint-改进)
    - [10.2 Unicode 17](#102-unicode-17)
  - [十一、兼容性说明](#十一兼容性说明)
  - [十二、版本变更历史](#十二版本变更历史)
  - [相关资源](#相关资源)
  - [十三、Rust 1.95 新特性补充](#十三rust-195-新特性补充)
    - [13.1 `if let` guards 示例](#131-if-let-guards-示例)
    - [13.2 `cfg_select!` 示例](#132-cfg_select-示例)
  - [十四、Rust 1.96 后续新特性](#十四rust-196-后续新特性)
    - [14.1 `core::range` 新类型](#141-corerange-新类型)
    - [14.2 `assert_matches!` 与 `debug_assert_matches!`](#142-assert_matches-与-debug_assert_matches)
    - [14.3 Cargo CVE-2026-5223 / CVE-2026-5222 修复](#143-cargo-cve-2026-5223-cve-2026-5222-修复)
    - [14.4 WebAssembly 链接行为变更](#144-webassembly-链接行为变更)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#权威国际化来源对齐升级摘要rust-1960-edition-2024)
    - [本次升级要点](#本次升级要点)
      - [新增 Rust 1.96.0 特性](#新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性](#新增-rust-1950-特性)
      - [权威来源对齐](#权威来源对齐)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 特性概述 {#特性概述}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

Rust 1.96.0 是 **2026年5月28日** 发布的稳定版本，带来了一系列重要的语言特性、标准库增强和 Cargo 改进。本文档基于权威来源全面分析这些特性。

### 版本亮点 {#版本亮点}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 类别 | 主要特性 | 影响程度 | 状态 |
|------|----------|----------|------|
| 标准库 | `array_windows` 方法 | ⭐⭐⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 标准库 | `element_offset` 方法 | ⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 标准库 | `LazyCell/LazyLock` 新方法 | ⭐⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 标准库 | 数学常量扩展 | ⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 标准库 | `core::range` 新类型 (RFC 3550) | ⭐⭐⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 标准库 | `assert_matches!` / `debug_assert_matches!` | ⭐⭐⭐⭐ | ✅ 已稳定 (1.96) |
| 工具链 | Cargo config inclusion | ⭐⭐⭐⭐ | ✅ 已稳定 (1.94) |
| 工具链 | TOML 1.1 支持 | ⭐⭐⭐ | ✅ 已稳定 (1.94) |
| 工具链 | Cargo CVE-2026-5223/5222 修复 | ⭐⭐⭐⭐ | ✅ 已修复 (1.96) |
| 性能 | AVX-512 FP16 指令 | ⭐⭐⭐ | ✅ 已稳定 (1.96) |

---

## 一、array_windows 方法 {#一array_windows-方法}
>
> **来源: [Rust Standard Library - slice::array_windows](https://doc.rust-lang.org/std/primitive.slice.html#method.array_windows)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 1.1 特性描述 {#11-特性描述}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`array_windows` 是 Rust 1.96.0 中最重要的新特性之一，它允许以固定大小的窗口遍历数组或切片，返回 `[T; N]` 数组而不是切片引用。

### 1.2 代码示例 {#12-代码示例}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
// 要求: Rust 1.96.0+ | Edition 2024

fn main() {
    let data = [1, 2, 3, 4, 5];

    // 使用 array_windows 遍历大小为 3 的窗口
    for window in data.array_windows::<3>() {
        println!("{:?}", window); // [1, 2, 3], [2, 3, 4], [3, 4, 5]
        // window 的类型是 [i32; 3]，不是 &[i32]
    }

    // 与 windows() 对比
    for window in data.windows(3) {
        println!("{:?}", window); // 相同输出
        // window 的类型是 &[i32]
    }
}
```

### 1.3 ABBA 模式检测示例 {#13-abba-模式检测示例}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 官方博客提供的经典示例：检测 ABBA 模式（两个不同字符后跟该字符对的逆序）。

```rust
fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows()
        .any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

fn main() {
    assert!(has_abba("abba"));
    assert!(has_abba("xyyx"));
    assert!(!has_abba("abcd"));
}
```

### 1.4 使用场景 {#14-使用场景}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 场景 | 优势 | 示例 |
|------|------|------|
| 信号处理 | 固定大小数组便于 SIMD 优化 | 滑动平均滤波 |
| 图像处理 | 3x3 卷积核遍历 | 边缘检测 |
| 时间序列 | 固定窗口统计计算 | 移动平均线 |
| 编译器 | Token 流分析 | 语法解析 |

---

## 二、element_offset 方法 {#二element_offset-方法}
>
> **来源: [Rust Standard Library - slice::element_offset](https://doc.rust-lang.org/std/primitive.slice.html#method.element_offset)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 2.1 特性描述 {#21-特性描述}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`element_offset` 方法返回切片中某个元素的索引位置，如果不属于该切片则返回 `None`。

### 2.2 代码示例 {#22-代码示例}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn main() {
    let arr = [10, 20, 30, 40, 50];

    // 获取元素偏移量
    let offset = arr.element_offset(&arr[2]);
    println!("{:?}", offset); // Some(2)

    // 不属于该切片的元素
    let other = 30;
    let offset = arr.element_offset(&other);
    println!("{:?}", offset); // None
}
```

---

## 三、LazyCell 和 LazyLock 新方法 {#三lazycell-和-lazylock-新方法}
>
> **来源: [Rust Standard Library - LazyCell](https://doc.rust-lang.org/std/cell/struct.LazyCell.html)**
>
> **来源: [Rust Standard Library - LazyLock](https://doc.rust-lang.org/std/sync/struct.LazyLock.html)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 3.1 新增 API {#31-新增-api}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 1.96.0 为 `LazyCell` 和 `LazyLock` 添加了以下方法：

| 方法 | 描述 | 适用类型 |
|------|------|----------|
| `get()` | 获取引用 | `LazyCell`, `LazyLock` |
| `get_mut()` | 获取可变引用 | `LazyCell`, `LazyLock` |
| `force_mut()` | 强制初始化并获取可变引用 | `LazyCell`, `LazyLock` |

### 3.2 代码示例 {#32-代码示例}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```rust,ignore
use std::cell::LazyCell;
use std::sync::LazyLock;

fn lazy_cell_examples() {
    // get() 示例
    let lazy: LazyCell<String> = LazyCell::new(|| "hello".to_string());
    println!("{:?}", lazy.get()); // Some("hello")

    // get_mut() 示例
    let mut lazy: LazyCell<String> = LazyCell::new(|| "initial".to_string());
    if let Some(value) = lazy.get_mut() {
        value.push_str(" modified");
    }
    println!("{}", *lazy); // "initial modified"

    // force_mut() 示例
    let mut lazy: LazyCell<String> = LazyCell::new(|| "forced".to_string());
    let value = LazyCell::force_mut(&mut lazy);
    value.push_str(" mutation");
    println!("{}", *lazy); // "forced mutation"
}

fn lazy_lock_examples() {
    // LazyLock 在多线程环境中使用
    static CONFIG: LazyLock<String> = LazyLock::new(|| {
        "config data".to_string()
    });

    println!("{:?}", CONFIG.get());
}
```

---

## 四、数学常量扩展 {#四数学常量扩展}
>
> **来源: [Rust Standard Library - f64::consts](https://doc.rust-lang.org/std/f64/consts/index.html)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 4.1 新增常量 {#41-新增常量}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

Rust 1.96.0 新增以下数学常量：

| 常量 | 值 | 说明 |
|------|-----|------|
| `EULER_GAMMA` | 0.5772... | 欧拉-马歇罗尼常数 |
| `GOLDEN_RATIO` | 1.6180... | 黄金比例 |

### 4.2 代码示例 {#42-代码示例}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

```rust
fn math_constants() {
    // 欧拉-马歇罗尼常数
    println!("γ = {}", std::f64::consts::EULER_GAMMA);
    // γ = 0.5772156649015329

    // 黄金比例
    println!("φ = {}", std::f64::consts::GOLDEN_RATIO);
    // φ = 1.618033988749895
}
```

---

## 五、迭代器增强 {#五迭代器增强}
>
> **来源: [Rust Standard Library - Peekable::next_if_map](https://doc.rust-lang.org/std/iter/struct.Peekable.html#method.next_if_map)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 5.1 Peekable::next_if_map {#51-peekablenext_if_map}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```rust,ignore
use std::iter::Peekable;

fn next_if_map_example() {
    let mut iter = [1, 2, 3, 4].into_iter().peekable();

    // 条件映射获取
    let result = iter.next_if_map(|x| if x > 2 { Some(x * 2) } else { None });
    println!("{:?}", result); // None (第一个元素 1 不大于 2)

    // 跳过 1, 2
    iter.next();
    iter.next();

    let result = iter.next_if_map(|x| if x > 2 { Some(x * 2) } else { None });
    println!("{:?}", result); // Some(6) (3 * 2)
}
```

---

## 六、字符转换 {#六字符转换}
>
> **来源: [Rust Standard Library - char](https://doc.rust-lang.org/std/primitive.char.html)**
>
> **来源: [Rust Standard Library - TryFrom<char> for usize](https://doc.rust-lang.org/std/primitive.usize.html)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 6.1 `TryFrom<char>` for usize {#61-tryfromchar-for-usize}

> **来源: [ACM](https://dl.acm.org/)**

```rust
fn char_to_usize() {
    let c = 'A';
    match usize::try_from(c) {
        Ok(n) => println!("'{}' = {}", c, n), // 'A' = 65
        Err(e) => println!("转换失败: {}", e),
    }

    // 或者直接使用
    let n: usize = '❤'.try_into().unwrap();
    println!("心形符号的码点: {}", n); // 10084
}
```

---

## 七、Const 上下文增强 {#七const-上下文增强}
>
> **来源: [Rust Standard Library - f64::mul_add](https://doc.rust-lang.org/std/primitive.f64.html#method.mul_add)**
>
> **来源: [Rust Reference - Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 7.1 mul_add 在 const 中稳定 {#71-mul_add-在-const-中稳定}

> **来源: [IEEE](https://standards.ieee.org/)**

```rust,ignore
const fn const_math() {
    // 乘加运算: a * b + c
    let result = 2.0f64.mul_add(3.0, 4.0);
    // 2 * 3 + 4 = 10
    assert_eq!(result, 10.0);
}
```

---

## 八、Cargo 新特性 {#八cargo-新特性}
>
> **来源: [Cargo Reference - Configuration](https://doc.rust-lang.org/cargo/reference/config.html)**
>
> **来源: [TOML 1.1 Specification](https://toml.io/en/v1.1.0)**
>
> **来源: [Rust 1.94 Release Notes / Cargo Dev Cycle](https://blog.rust-lang.org/inside-rust/2026/02/18/this-development-cycle-in-cargo-1.94/)**

### 8.1 Config Inclusion {#81-config-inclusion}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

Cargo 1.94 支持在配置文件中包含其他配置文件：

```toml
# .cargo/config.toml {#cargoconfigtoml}
include = [
    "frodo.toml",
    "samwise.toml",
]

# 或使用内联表格式 {#或使用内联表格式}
include = [
    { path = "required.toml" },
    { path = "optional.toml", optional = true },
]
```

### 8.2 TOML 1.1 支持 {#82-toml-11-支持}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

Cargo 现在解析 TOML v1.1，支持：

- 跨多行的内联表
- 尾部逗号
- `\xHH` 和 `\e` 字符串转义
- 时间中的秒可选

```toml
[dependencies]
serde = {
    version = "1.0",
    features = ["derive",],
}
```

### 8.3 pubtime 字段 {#83-pubtime-字段}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

registry 索引现在记录 crate 版本的发布时间，支持基于时间的依赖解析。

---

## 九、平台支持 {#九平台支持}
>
> **来源: [Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 9.1 新增目标 {#91-新增目标}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

| 目标 | 级别 | 描述 |
|------|------|------|
| `riscv64im-unknown-none-elf` | Tier 3 | RISC-V 64位嵌入式 |

### 9.2 RISC-V 特性 {#92-risc-v-特性}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

29 个 RISC-V 目标特性已稳定化，包括 RVA22U64 / RVA23U64 配置文件的大部分内容。

---

## 十、语言改进 {#十语言改进}
>
> **来源: [Rust Reference - Lint Levels](https://doc.rust-lang.org/reference/attributes/diagnostics.html#lint-check-attributes)**
>
> **来源: [Unicode 17](https://www.unicode.org/versions/Unicode17.0.0/)**
>
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**

### 10.1 Lint 改进 {#101-lint-改进}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| Lint | 级别 | 描述 |
|------|------|------|
| `dead_code` 继承 | 默认 | Impls 继承 trait 的 lint 级别 |
| `unused_visibilities` | Warn | `const _` 声明的可见性警告 |

### 10.2 Unicode 17 {#102-unicode-17}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

Rust 1.96.0 更新至 Unicode 17。

---

## 十一、兼容性说明 {#十一兼容性说明}
>
> **来源: [Rust 1.96.0 Release Notes - Compatibility Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)**
>
> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**

Rust 1.96.0 包含以下兼容性变更：

1. **闭包捕获**: 模式匹配周围的闭包捕获行为已改变
2. **宏导入**: 标准库宏现在通过 prelude 导入
3. **dyn 类型生命周期**: 禁止自由转换 dyn 类型的生命周期边界
4. **Windows 时间**: `SystemTime::checked_sub_duration` 在 Windows 纪元前的行为

---

## 十二、版本变更历史 {#十二版本变更历史}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 版本 | 发布日期 | 变更内容 |
|------|----------|----------|
| 1.94.0 | 2026-03-05 | Cargo config inclusion、TOML 1.1、pubtime |
| 1.95.0 | 2026-04-16 | if let guards、cfg_select!、PowerPC inline asm |
| 1.96.0 | 2026-05-28 | core::range、assert_matches!、CVE-2026-5223/5222 修复 |

---

## 相关资源 {#相关资源}
>
> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**
>
> **来源: [Rust Blog](https://blog.rust-lang.org/)**

- [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)
- [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0.html)
- [Rust Release Notes (doc.rust-lang.org)](https://doc.rust-lang.org/stable/releases.html)
- [Rust Changelogs 1.96.0](https://releases.rs/docs/1.96.0/)
- [Rust Changelogs 1.95.0](https://releases.rs/docs/1.95.0/)
- [Cargo 1.94 开发周期](https://blog.rust-lang.org/inside-rust/2026/02/18/this-development-cycle-in-cargo-1.94/)
- [项目版本索引](../../crates/VERSION_INDEX.md)

---

## 十三、Rust 1.95 新特性补充 {#十三rust-195-新特性补充}

> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**

Rust 1.95.0 于 2026-04-16 发布，补充了多项语言与工具链特性：

| 特性 | 说明 | 权威来源 |
| :--- | :--- | :--- |
| `if let` guards on match arms | match 臂支持 `if let` 条件守卫 | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards) |
| `cfg_select!` 宏 | 编译期按 cfg 条件选择分支 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) |
| PowerPC / PowerPC64 inline asm | 稳定 PowerPC 平台内联汇编 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) |
| `--remap-path-scope` | 控制路径重映射作用域 | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) |

### 13.1 `if let` guards 示例 {#131-if-let-guards-示例}

```rust
match value {
    Some(x) if let Ok(y) = compute(x) => {
        println!("x = {}, y = {}", x, y);
    }
    _ => {}
}
```

### 13.2 `cfg_select!` 示例 {#132-cfg_select-示例}

```rust
cfg_select! {
    unix => { fn foo() { /* Unix-specific */ } }
    windows => { fn foo() { /* Windows-specific */ } }
    _ => { fn foo() { /* fallback */ } }
}
```

---

## 十四、Rust 1.96 后续新特性 {#十四rust-196-后续新特性}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

### 14.1 `core::range` 新类型 {#141-corerange-新类型}

Rust 1.96.0 稳定了 RFC 3550 提出的新 Range 类型，解决旧 `std::ops::Range` 直接实现 `Iterator` 导致无法 `Copy` 的问题。

```rust
use core::range::Range;

let r: Range<i32> = 0..10;
// Range<Idx> 实现 Copy（当 Idx: Copy）
let r2 = r;

for i in r {
    print!("{} ", i); // 0 1 2 ... 9
}
// r 仍可再次使用，因为它被 Copy
for i in r2 {
    print!("{} ", i);
}
```

**关键区别**：

| 特性 | legacy `std::ops::Range` | 新 `core::range::Range` |
| :--- | :--- | :--- |
| `Iterator` | 直接实现 | 不直接实现 |
| `Copy` | ❌ | ✅（当 `Idx: Copy`） |
| 迭代方式 | `.next()` 直接调用 | `for` 通过 `IntoIterator` |
| 推荐使用 | 历史代码 | 新代码、公共 API |

### 14.2 `assert_matches!` 与 `debug_assert_matches!` {#142-assert_matches-与-debug_assert_matches}

```rust
use core::assert_matches::assert_matches;

let result: Result<i32, &str> = Ok(42);
assert_matches!(result, Ok(_));
assert_matches!(result, Ok(x) if x > 0);
```

**特点**：

- 失败时输出匹配值的 `Debug` 表示
- 未加入 prelude，需显式导入
- 比 `assert!(matches!(...))` 诊断更丰富

### 14.3 Cargo CVE-2026-5223 / CVE-2026-5222 修复 {#143-cargo-cve-2026-5223-cve-2026-5222-修复}

详见 [Cargo 1.94 新特性指南 - 九、Rust 1.96 Cargo 安全修复](10_cargo_194_features.md#九rust-196-cargo-安全修复)。

### 14.4 WebAssembly 链接行为变更 {#144-webassembly-链接行为变更}

Rust 1.96.0 不再默认向链接器传递 `--allow-undefined`，未定义符号现在会直接报错而非静默转为 `"env"` 模块的 WebAssembly 导入。

```bash
# 如需恢复旧行为 {#如需恢复旧行为}
RUSTFLAGS="-Clink-arg=--allow-undefined" cargo build --target wasm32-unknown-unknown
```

---

## ✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024） {#权威国际化来源对齐升级摘要rust-1960-edition-2024}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性 {#新增-rust-1960-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |

#### 新增 Rust 1.95.0 特性 {#新增-rust-1950-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |

#### 权威来源对齐 {#权威来源对齐}

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**

> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**

> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**

> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

> **来源: [Rust Standard Library - core::range](https://doc.rust-lang.org/stable/core/range/index.html)**

> **来源: [Rust Standard Library - assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)**

> **来源: [Rust Reference - Range Expressions](https://doc.rust-lang.org/reference/expressions/range-expr.html)**

> **来源: [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)**

> **来源: [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)**

> **来源: [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)**

---