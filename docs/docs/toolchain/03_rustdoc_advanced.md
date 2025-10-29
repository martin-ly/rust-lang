# Rustdoc 高级功能与文档生成

> **文档版本**: Rust 1.90+ | **更新日期**: 2025-10-22  
> **文档类型**: 📘 工具链参考 | **适用对象**: 中级到高级开发者

---

## 📊 目录

- [Rustdoc 高级功能与文档生成](#rustdoc-高级功能与文档生成)
  - [📊 目录](#-目录)
  - [🎯 文档说明](#-文档说明)
  - [📋 目录](#-目录-1)
  - [1. Rustdoc 概览](#1-rustdoc-概览)
    - [1.1 基础用法](#11-基础用法)
    - [1.2 文档结构](#12-文档结构)
  - [2. 文档注释语法](#2-文档注释语法)
    - [2.1 基础注释](#21-基础注释)
    - [2.2 Markdown 支持](#22-markdown-支持)
    - [2.3 代码块](#23-代码块)
  - [3. 文档测试 (Doc Tests)](#3-文档测试-doc-tests)
    - [3.1 基础测试](#31-基础测试)
    - [3.2 高级测试选项](#32-高级测试选项)
    - [3.3 测试属性](#33-测试属性)
  - [4. 文档链接](#4-文档链接)
    - [4.1 Intra-doc Links](#41-intra-doc-links)
    - [4.2 链接语法](#42-链接语法)
    - [4.3 链接到外部文档](#43-链接到外部文档)
  - [5. 文档组织](#5-文档组织)
    - [5.1 模块级文档](#51-模块级文档)
    - [5.2 crate 级文档](#52-crate-级文档)
    - [5.3 文档章节](#53-文档章节)
  - [6. JSON 输出 (Rust 1.54+)](#6-json-输出-rust-154)
    - [6.1 生成 JSON](#61-生成-json)
    - [6.2 JSON 格式](#62-json-格式)
    - [6.3 应用场景](#63-应用场景)
  - [7. 主题与定制](#7-主题与定制)
    - [7.1 自定义 CSS](#71-自定义-css)
    - [7.2 自定义 HTML](#72-自定义-html)
    - [7.3 Logo 和 Favicon](#73-logo-和-favicon)
  - [8. 文档属性](#8-文档属性)
    - [8.1 `#[doc]` 属性](#81-doc-属性)
    - [8.2 条件文档](#82-条件文档)
  - [9. 私有项文档](#9-私有项文档)
    - [9.1 文档化私有项](#91-文档化私有项)
    - [9.2 内部文档](#92-内部文档)
  - [10. 搜索与索引](#10-搜索与索引)
    - [10.1 搜索功能](#101-搜索功能)
    - [10.2 搜索别名](#102-搜索别名)
  - [11. CI/CD 集成](#11-cicd-集成)
    - [11.1 自动化文档生成](#111-自动化文档生成)
    - [11.2 文档部署](#112-文档部署)
  - [12. 最佳实践](#12-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [⚠️ 避免](#️-避免)
  - [13. 实战案例](#13-实战案例)
  - [14. 故障排查](#14-故障排查)
    - [常见问题](#常见问题)
  - [15. 相关资源](#15-相关资源)
    - [📚 官方文档](#-官方文档)
    - [🔗 相关文档](#-相关文档)
    - [📦 推荐工具](#-推荐工具)

## 🎯 文档说明

本文档深入介绍 Rustdoc 的高级功能、文档生成技术、以及最新改进，帮助开发者创建高质量的 API 文档。

**覆盖内容**: 文档注释、文档测试、主题定制、JSON 输出、文档链接、最佳实践

---

## 📋 目录

- [Rustdoc 高级功能与文档生成](#rustdoc-高级功能与文档生成)
  - [📊 目录](#-目录)
  - [🎯 文档说明](#-文档说明)
  - [📋 目录](#-目录-1)
  - [1. Rustdoc 概览](#1-rustdoc-概览)
    - [1.1 基础用法](#11-基础用法)
    - [1.2 文档结构](#12-文档结构)
  - [2. 文档注释语法](#2-文档注释语法)
    - [2.1 基础注释](#21-基础注释)
    - [2.2 Markdown 支持](#22-markdown-支持)
    - [2.3 代码块](#23-代码块)
  - [3. 文档测试 (Doc Tests)](#3-文档测试-doc-tests)
    - [3.1 基础测试](#31-基础测试)
    - [3.2 高级测试选项](#32-高级测试选项)
    - [3.3 测试属性](#33-测试属性)
  - [4. 文档链接](#4-文档链接)
    - [4.1 Intra-doc Links](#41-intra-doc-links)
    - [4.2 链接语法](#42-链接语法)
    - [4.3 链接到外部文档](#43-链接到外部文档)
  - [5. 文档组织](#5-文档组织)
    - [5.1 模块级文档](#51-模块级文档)
    - [5.2 crate 级文档](#52-crate-级文档)
    - [5.3 文档章节](#53-文档章节)
  - [6. JSON 输出 (Rust 1.54+)](#6-json-输出-rust-154)
    - [6.1 生成 JSON](#61-生成-json)
    - [6.2 JSON 格式](#62-json-格式)
    - [6.3 应用场景](#63-应用场景)
  - [7. 主题与定制](#7-主题与定制)
    - [7.1 自定义 CSS](#71-自定义-css)
    - [7.2 自定义 HTML](#72-自定义-html)
    - [7.3 Logo 和 Favicon](#73-logo-和-favicon)
  - [8. 文档属性](#8-文档属性)
    - [8.1 `#[doc]` 属性](#81-doc-属性)
    - [8.2 条件文档](#82-条件文档)
  - [9. 私有项文档](#9-私有项文档)
    - [9.1 文档化私有项](#91-文档化私有项)
    - [9.2 内部文档](#92-内部文档)
  - [10. 搜索与索引](#10-搜索与索引)
    - [10.1 搜索功能](#101-搜索功能)
    - [10.2 搜索别名](#102-搜索别名)
  - [11. CI/CD 集成](#11-cicd-集成)
    - [11.1 自动化文档生成](#111-自动化文档生成)
    - [11.2 文档部署](#112-文档部署)
  - [12. 最佳实践](#12-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [⚠️ 避免](#️-避免)
  - [13. 实战案例](#13-实战案例)
  - [14. 故障排查](#14-故障排查)
    - [常见问题](#常见问题)
  - [15. 相关资源](#15-相关资源)
    - [📚 官方文档](#-官方文档)
    - [🔗 相关文档](#-相关文档)
    - [📦 推荐工具](#-推荐工具)

---

## 1. Rustdoc 概览

### 1.1 基础用法

**生成文档**:

```bash
# 生成当前 crate 的文档
cargo doc

# 生成并打开文档
cargo doc --open

# 生成所有依赖的文档
cargo doc --no-deps

# 生成私有项的文档
cargo doc --document-private-items
```

---

### 1.2 文档结构

**输出目录**:

```text
target/doc/
├── index.html                # 主索引页
├── my_crate/
│   ├── index.html           # crate 主页
│   ├── struct.MyStruct.html # 结构体文档
│   ├── fn.my_function.html  # 函数文档
│   └── ...
├── search-index.js          # 搜索索引
├── settings.html            # 设置页
└── help.html               # 帮助页
```

---

## 2. 文档注释语法

### 2.1 基础注释

**外部文档注释** (`///`):

```rust
/// 这是一个公开函数的文档
///
/// # Examples
///
/// ```
/// use my_crate::add;
/// assert_eq!(add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

**内部文档注释** (`//!`):

```rust
//! 这是模块的文档
//!
//! 这个模块提供了数学运算功能。

pub fn multiply(a: i32, b: i32) -> i32 {
    a * b
}
```

**块文档注释**:

```rust
/** 外部块文档注释
 *
 * 支持多行
 */
pub fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

/*! 内部块文档注释
 *
 * 用于模块级文档
 */
```

---

### 2.2 Markdown 支持

**完整 Markdown 语法**:

```rust
/// # 标题 1
/// ## 标题 2
/// ### 标题 3
///
/// **粗体** 和 *斜体*
///
/// - 列表项 1
/// - 列表项 2
///   - 嵌套列表
///
/// 1. 有序列表 1
/// 2. 有序列表 2
///
/// [链接文本](https://example.com)
///
/// ![图片描述](https://example.com/image.png)
///
/// `行内代码`
///
/// > 引用文本
///
/// ---
///
/// | 表头 1 | 表头 2 |
/// |--------|--------|
/// | 单元格 | 单元格 |
pub fn demo() {}
```

---

### 2.3 代码块

**基础代码块**:

````rust
/// ```
/// let x = 42;
/// assert_eq!(x, 42);
/// ```
pub fn example() {}
````

**指定语言**:

````rust
/// ```rust
/// // Rust 代码
/// ```
///
/// ```python
/// # Python 代码 (不会被测试)
/// print("Hello")
/// ```
///
/// ```text
/// 纯文本
/// ```
pub fn multi_lang() {}
````

**编译失败的示例**:

````rust
/// ```compile_fail
/// // 这段代码应该编译失败
/// let x: i32 = "string";
/// ```
pub fn error_demo() {}
````

---

## 3. 文档测试 (Doc Tests)

### 3.1 基础测试

**自动测试**:

````rust
/// 加法函数
///
/// # Examples
///
/// ```
/// use my_crate::add;
/// assert_eq!(add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
````

**运行文档测试**:

```bash
cargo test --doc
```

---

### 3.2 高级测试选项

**隐藏部分代码**:

````rust
/// ```
/// # use my_crate::setup;
/// # let ctx = setup();
/// // 用户只看到这一行
/// ctx.run();
/// ```
pub fn demo() {}
````

**`no_run`**: 编译但不运行

````rust
/// ```no_run
/// // 这段代码会编译，但不会运行
/// std::process::exit(0);
/// ```
pub fn exit_demo() {}
````

**`ignore`**: 忽略测试

````rust
/// ```ignore
/// // 这段代码被忽略
/// ```
pub fn ignored() {}
````

**`should_panic`**: 应该 panic

````rust
/// ```should_panic
/// panic!("This should panic");
/// ```
pub fn panic_demo() {}
````

---

### 3.3 测试属性

````rust
/// ```
/// use my_crate::MyType;
/// let x = MyType::new();
/// # // 隐藏的测试代码
/// # assert!(x.is_valid());
/// ```
///
/// ```no_run
/// // 编译但不运行
/// loop {}
/// ```
///
/// ```compile_fail
/// // 应该编译失败
/// let x: i32 = "string";
/// ```
pub struct MyType;
````

---

## 4. 文档链接

### 4.1 Intra-doc Links

**链接到其他项**:

```rust
/// 使用 [`add`] 函数进行加法运算
///
/// 也可以链接到 [`MyStruct`]
///
/// 或者使用完整路径 [`crate::module::function`]
pub fn demo() {}

/// 加法函数
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 示例结构体
pub struct MyStruct;
```

---

### 4.2 链接语法

**不同的链接方式**:

```rust
/// - [`function`]: 自动推断
/// - [`function()`]: 明确指定是函数
/// - [`Struct`]: 结构体
/// - [`Struct::method`]: 方法
/// - [`Struct::method()`]: 方法 (显式)
/// - [`module::Type`]: 带模块路径
/// - [custom text][`Type`]: 自定义显示文本
pub fn link_examples() {}
```

**链接到特定项类型**:

```rust
/// - [struct@MyType]: 结构体
/// - [enum@MyType]: 枚举
/// - [trait@MyType]: trait
/// - [type@MyType]: 类型别名
/// - [fn@my_function]: 函数
/// - [macro@my_macro]: 宏
pub fn explicit_links() {}
```

---

### 4.3 链接到外部文档

```rust
/// 使用 [tokio](https://docs.rs/tokio) 进行异步编程
///
/// 参考 [Rust Book](https://doc.rust-lang.org/book/)
pub fn external_links() {}
```

---

## 5. 文档组织

### 5.1 模块级文档

```rust
//! # 模块名称
//!
//! 模块描述
//!
//! ## Examples
//!
//! ```
//! use my_crate::my_module;
//! my_module::function();
//! ```

pub fn function() {}
```

---

### 5.2 crate 级文档

**`src/lib.rs`**:

```rust
//! # My Crate
//!
//! 这是 crate 的主文档
//!
//! ## Quick Start
//!
//! ```
//! use my_crate::MyType;
//! let instance = MyType::new();
//! ```
//!
//! ## Features
//!
//! - Feature 1
//! - Feature 2

#![doc(html_logo_url = "https://example.com/logo.png")]
#![doc(html_favicon_url = "https://example.com/favicon.ico")]
```

---

### 5.3 文档章节

**标准章节**:

```rust
/// # Examples
///
/// ```
/// // 示例代码
/// ```
///
/// # Errors
///
/// 此函数可能返回以下错误:
/// - `ErrorType1`: 错误描述
/// - `ErrorType2`: 错误描述
///
/// # Panics
///
/// 此函数在以下情况下会 panic:
/// - 条件 1
/// - 条件 2
///
/// # Safety
///
/// 此函数是 unsafe 的，因为...
///
/// 调用者必须确保:
/// - 条件 1
/// - 条件 2
///
/// # Performance
///
/// 时间复杂度: O(n)
/// 空间复杂度: O(1)
pub fn documented_function() {}
```

---

## 6. JSON 输出 (Rust 1.54+)

### 6.1 生成 JSON

**命令**:

```bash
# 生成 JSON 格式的文档
cargo +nightly rustdoc -- -Z unstable-options --output-format json

# 或使用 rustdoc 直接生成
rustdoc src/lib.rs -Z unstable-options --output-format json
```

---

### 6.2 JSON 格式

**输出示例**:

```json
{
  "format_version": 28,
  "crate_name": "my_crate",
  "crate_version": "0.1.0",
  "paths": {
    "0": {
      "kind": "function",
      "name": "add",
      "source": "src/lib.rs:10:1"
    }
  },
  "index": {
    "0": {
      "docs": "加法函数",
      "sig": "pub fn add(a: i32, b: i32) -> i32",
      "kind": "function"
    }
  }
}
```

---

### 6.3 应用场景

- **文档工具**: 构建自定义文档生成器
- **API 索引**: 生成 API 目录
- **文档搜索**: 构建高级搜索功能
- **文档分析**: 分析 API 覆盖率

---

## 7. 主题与定制

### 7.1 自定义 CSS

**添加自定义样式**:

```rust
#![doc(html_root_url = "https://docs.example.com/my-crate/")]
#![doc(html_playground_url = "https://play.rust-lang.org/")]
```

**Cargo.toml 配置**:

```toml
[package.metadata.docs.rs]
rustdoc-args = ["--html-in-header", "header.html"]
```

**`header.html`**:

```html
<style>
    :root {
        --main-background-color: #1e1e1e;
        --main-color: #ddd;
    }
</style>
```

---

### 7.2 自定义 HTML

**添加自定义 HTML**:

```rust
#![doc(
    html_favicon_url = "https://example.com/favicon.ico",
    html_logo_url = "https://example.com/logo.svg",
    html_playground_url = "https://play.rust-lang.org/"
)]
```

---

### 7.3 Logo 和 Favicon

```rust
#![doc(html_logo_url = "https://example.com/logo.png")]
#![doc(html_favicon_url = "https://example.com/favicon.ico")]
#![doc(html_root_url = "https://docs.rs/my-crate/")]
```

---

## 8. 文档属性

### 8.1 `#[doc]` 属性

**基础用法**:

```rust
#[doc = "这是文档字符串"]
pub fn func1() {}

#[doc = include_str!("../README.md")]
pub fn func2() {}

#[doc(hidden)]
pub fn internal_func() {}  // 不在文档中显示

#[doc(alias = "addition")]
pub fn add(a: i32, b: i32) -> i32 {  // 搜索别名
    a + b
}
```

---

### 8.2 条件文档

```rust
#[cfg_attr(feature = "docs", doc = "Extended documentation")]
pub fn conditional_doc() {}

#[doc(cfg(feature = "async"))]
pub async fn async_function() {}  // 显示需要的 feature
```

---

## 9. 私有项文档

### 9.1 文档化私有项

```bash
# 生成包含私有项的文档
cargo doc --document-private-items
```

```rust
/// 私有函数也可以有文档
fn private_helper() {
    // ...
}
```

---

### 9.2 内部文档

```rust
#[doc(hidden)]
pub fn internal_api() {}  // 公开但隐藏的 API

/// 仅在内部使用
#[doc = "Internal use only"]
pub(crate) fn crate_internal() {}
```

---

## 10. 搜索与索引

### 10.1 搜索功能

**搜索索引自动生成**: `search-index.js`

**搜索语法**:

- `MyStruct`: 搜索类型名
- `my_function`: 搜索函数名
- `path::to::item`: 搜索路径

---

### 10.2 搜索别名

```rust
#[doc(alias = "addition")]
#[doc(alias = "sum")]
#[doc(alias = "plus")]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
// 可以通过 "addition", "sum", "plus" 搜索到此函数
```

---

## 11. CI/CD 集成

### 11.1 自动化文档生成

**GitHub Actions 示例**:

```yaml
name: Documentation

on:
  push:
    branches: [main]

jobs:
  docs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
      - name: Build documentation
        run: cargo doc --no-deps --all-features
      - name: Deploy to GitHub Pages
        uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./target/doc
```

---

### 11.2 文档部署

**docs.rs 自动部署**:

```toml
[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

**自定义域名**:

创建 `CNAME` 文件:

```text
docs.example.com
```

---

## 12. 最佳实践

### ✅ 推荐做法

1. **示例代码**: 为每个公开 API 提供示例
2. **文档测试**: 确保示例代码可编译运行
3. **错误文档**: 说明可能的错误和 panic 情况
4. **性能说明**: 对性能敏感的 API 说明复杂度
5. **Safety**: unsafe 代码必须详细说明安全要求
6. **使用 Intra-doc Links**: 链接到相关项

### ⚠️ 避免

1. **重复代码签名**: Rustdoc 会自动显示签名
2. **过时的文档**: 定期更新文档
3. **缺少示例**: 没有示例的 API 难以使用
4. **不可运行的示例**: 确保示例可以编译

---

## 13. 实战案例

**完整示例**:

```rust
//! # My Awesome Crate
//!
//! 这个 crate 提供了高性能的数据处理功能。
//!
//! ## Features
//!
//! - **Fast**: 使用 SIMD 加速
//! - **Safe**: 100% 安全 Rust
//! - **Flexible**: 支持多种数据格式
//!
//! ## Quick Start
//!
//! ```
//! use my_crate::Processor;
//!
//! let processor = Processor::new();
//! let result = processor.process(&[1, 2, 3, 4, 5]);
//! assert_eq!(result, vec![2, 4, 6, 8, 10]);
//! ```

#![doc(html_logo_url = "https://example.com/logo.svg")]
#![doc(html_favicon_url = "https://example.com/favicon.ico")]
#![doc(html_root_url = "https://docs.rs/my-crate/")]
#![warn(missing_docs)]

/// 数据处理器
///
/// 这个结构体提供了高效的数据处理能力。
///
/// # Examples
///
/// ```
/// use my_crate::Processor;
///
/// let processor = Processor::new();
/// assert!(processor.is_ready());
/// ```
///
/// # Performance
///
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
///
/// # Thread Safety
///
/// 这个类型实现了 `Send` 和 `Sync`，可以安全地在线程间共享。
pub struct Processor {
    config: Config,
}

impl Processor {
    /// 创建新的处理器实例
    ///
    /// # Examples
    ///
    /// ```
    /// use my_crate::Processor;
    ///
    /// let processor = Processor::new();
    /// ```
    pub fn new() -> Self {
        Self {
            config: Config::default(),
        }
    }

    /// 处理数据
    ///
    /// # Arguments
    ///
    /// * `data` - 输入数据切片
    ///
    /// # Returns
    ///
    /// 返回处理后的数据向量
    ///
    /// # Examples
    ///
    /// ```
    /// use my_crate::Processor;
    ///
    /// let processor = Processor::new();
    /// let result = processor.process(&[1, 2, 3]);
    /// assert_eq!(result, vec![2, 4, 6]);
    /// ```
    ///
    /// # Errors
    ///
    /// 当输入数据为空时返回错误
    ///
    /// # Panics
    ///
    /// 当配置无效时会 panic
    pub fn process(&self, data: &[i32]) -> Vec<i32> {
        data.iter().map(|x| x * 2).collect()
    }

    /// 检查处理器是否就绪
    ///
    /// # Examples
    ///
    /// ```
    /// use my_crate::Processor;
    ///
    /// let processor = Processor::new();
    /// assert!(processor.is_ready());
    /// ```
    pub fn is_ready(&self) -> bool {
        true
    }
}

#[derive(Default)]
struct Config;
```

---

## 14. 故障排查

### 常见问题

**1. 文档链接失效**:

```bash
# 检查断开的链接
cargo rustdoc -- -D rustdoc::broken-intra-doc-links
```

**2. 文档测试失败**:

```bash
# 运行文档测试并显示详细输出
cargo test --doc -- --nocapture
```

**3. JSON 输出错误**:

```bash
# 确保使用 nightly 工具链
rustup override set nightly
cargo +nightly rustdoc -- -Z unstable-options --output-format json
```

---

## 15. 相关资源

### 📚 官方文档

- [Rustdoc Book](https://doc.rust-lang.org/rustdoc/)
- [Doc Comments](https://doc.rust-lang.org/reference/comments.html#doc-comments)
- [The Rust Book - Documentation](https://doc.rust-lang.org/book/ch14-02-publishing-to-crates-io.html)

### 🔗 相关文档

- [01_compiler_features.md](./01_compiler_features.md)
- [02_cargo_workspace_guide.md](./02_cargo_workspace_guide.md)

### 📦 推荐工具

- **mdBook**: 创建书籍格式的文档
- **cargo-readme**: 从文档生成 README
- **cargo-deadlinks**: 检查文档中的死链接
- **cargo-watch**: 自动重新生成文档

---

**文档维护**: Documentation Team  
**最后更新**: 2025-10-22  
**下次审查**: 2026-01-22
