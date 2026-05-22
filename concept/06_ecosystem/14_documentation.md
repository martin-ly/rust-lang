# 文档生态：rustdoc、文档测试与 API 文档规范

> **Bloom 层级**: 应用 → 分析
> **定位**: 覆盖 Rust **文档生态**的核心工具与实践——从 rustdoc 的渲染机制、文档测试（doctest）、到 API 文档规范（RFC 1574）和 mdBook 静态站点生成，分析 Rust 文档文化如何成为语言生态的竞争优势。
> **前置概念**: [Macros](../03_advanced/04_macros.md) · [Module System](../02_intermediate/10_module_system.md)
> **后置概念**: [Cargo Toolchain](./01_toolchain.md) · [WebAssembly](./11_webassembly.md)

---

> **来源**: [rustdoc Documentation](https://doc.rust-lang.org/rustdoc/) · [RFC 1574 — API Documentation](https://github.com/rust-lang/rfcs/pull/1574) · [mdBook Guide](https://rust-lang.github.io/mdBook/) · [RFC 1946 — Intra-rustdoc links](https://github.com/rust-lang/rfcs/pull/1946) · [docs.rs](https://docs.rs/about)

## 📑 目录

- [文档生态：rustdoc、文档测试与 API 文档规范](#文档生态rustdoc文档测试与-api-文档规范)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 rustdoc：编译器集成的文档生成器](#11-rustdoc编译器集成的文档生成器)
    - [1.2 文档测试（Doc Tests）](#12-文档测试doc-tests)
    - [1.3 文档作为类型系统的一部分](#13-文档作为类型系统的一部分)
  - [二、技术细节](#二技术细节)
    - [2.1 文档注释语法](#21-文档注释语法)
    - [2.2 Intra-doc Links](#22-intra-doc-links)
    - [2.3 mdBook 与知识体系站点](#23-mdbook-与知识体系站点)
  - [三、最佳实践](#三最佳实践)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念

### 1.1 rustdoc：编译器集成的文档生成器

```mermaid
graph LR
    subgraph Source["源代码"]
        RS["*.rs 文件"]
        DOC["/// 文档注释"]
        EXAMPLE["```rust 代码示例"]
    end

    subgraph Rustdoc["rustdoc 处理"]
        PARSE["解析 AST"]
        EXTRACT["提取文档注释"]
        COMPILE["编译 doctests"]
        RENDER["渲染 HTML"]
    end

    subgraph Output["输出"]
        HTML["静态 HTML 站点"]
        SEARCH["搜索索引"]
        TEST["测试结果"]
    end

    RS --> PARSE
    DOC --> EXTRACT
    EXAMPLE --> COMPILE
    PARSE --> EXTRACT --> RENDER --> HTML
    COMPILE --> TEST
    EXTRACT --> SEARCH
```

> **认知功能**: 此图展示 rustdoc 的**工作流**——它不仅是文档渲染器，还是**文档测试运行器**。这是 Rust 文档生态区别于其他语言的关键特性。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: 将 rustdoc 视为 CI 的一部分——`cargo test --doc` 应在每次提交时运行。
> **关键洞察**: rustdoc 与**编译器共享 AST**——它直接读取编译器的解析结果，确保文档与代码始终同步。
> [来源: [rustdoc Documentation](https://doc.rust-lang.org/rustdoc/)]

---

### 1.2 文档测试（Doc Tests）

```text
文档测试: 将示例代码作为测试运行

  基本语法:
  /// ```
  /// let x = add(2, 3);
  /// assert_eq!(x, 5);
  /// ```
  pub fn add(a: i32, b: i32) -> i32 { a + b }

  运行方式:
  ├── cargo test --doc        // 仅运行文档测试
  ├── cargo test              // 运行所有测试（包括 doctest）
  └── rustdoc --test src/lib.rs  // 直接使用 rustdoc

  属性控制:
  ├── ```ignore    // 不编译（展示不可运行代码）
  ├── ```no_run    // 编译但不运行（如 panic 示例）
  ├── ```should_panic  // 期望 panic
  ├── ```edition2021   // 指定 edition
  ├── ```compile_fail  // 期望编译失败（演示错误）
  └── ```text      // 纯文本，不编译

  隐藏代码:
  /// ```
  /// # use my_crate::setup;  // # 前缀的代码被隐藏
  /// # setup();
  /// let result = my_function();
  /// ```
```

> **Doctest 洞察**: Rust 的**文档测试**是生态的独特优势——示例代码不会过时，因为 CI 会验证它们是否能编译和运行。这解决了技术文档的**示例腐烂**（bit rot）问题。
> [来源: [TRPL — Documentation Comments](https://doc.rust-lang.org/book/ch14-02-publishing-to-crates-io.html#documentation-comments)]

---

### 1.3 文档作为类型系统的一部分

```text
Rust 文档文化的独特性:

  1. 文档即契约
  ├── Safety 注释: /// # Safety 段落说明 unsafe 前置条件
  ├── Panic 注释: /// # Panics 段落说明 panic 条件
  └── Errors 注释: /// # Errors 段落说明错误情况

  2. 文档即示例
  ├── 每个公共 API 都有可运行的示例
  ├── 示例覆盖典型用例和边界情况
  └── doctest 确保示例始终有效

  3. 文档即规范
  ├── RFC 1574 定义标准文档结构
  ├── docs.rs 自动生成所有 crate 的文档
  └── cargo doc 在本地生成文档

  4. 与其他语言的对比:
  ┌───────────┬─────────────────┬─────────────────┬─────────────────┐
  │ 特性      │ Rust            │ Python          │ JavaScript      │
  ├───────────┼─────────────────┼─────────────────┼─────────────────┤
  │ 文档测试  │ 内置            │ 需 doctest 库   │ 无原生支持      │
  │ 生成工具  │ rustdoc（集成） │ Sphinx/ pydoc   │ JSDoc/ TSDoc    │
  │ 托管平台  │ docs.rs（自动） │ ReadTheDocs     │ 无统一平台      │
  │ 类型链接  │ intra-doc links │ 无              │ 无              │
  └───────────┴─────────────────┴─────────────────┴─────────────────┘
```

> **文档文化洞察**: Rust 的文档生态不是**事后补充**，而是**开发流程的组成部分**——从 RFC 1574 的标准化到 docs.rs 的自动托管，文档质量被提升到与代码质量同等重要的地位。
> [来源: [RFC 1574 — API Documentation](https://github.com/rust-lang/rfcs/pull/1574)]

---

## 二、技术细节

### 2.1 文档注释语法

```rust,ignore
/// 单行文档注释（推荐用于函数/结构体）
pub fn example() {}

/** 块文档注释（推荐用于长文档）
 * # 概述
 *
 * 这是一个示例函数，展示了块文档注释的用法。
 *
 * # 示例
 *
 * ```
 * use my_crate::example;
 * example();
 * ```
 *
 * # 安全性
 *
 * 此函数是安全的，不需要 unsafe 块。
 */
pub fn documented() {}

// 模块级文档（放在文件开头或 //!）
//! # My Crate
//!
//! 这是 crate 级别的文档，使用 `//!` 前缀。
//!
//! ## 功能
//!
//! - 功能 A
//! - 功能 B
```

> **注释规范**: `///` 用于项文档，`//!` 用于容器（模块/crate）文档。RFC 1574 建议使用 Markdown 格式和特定章节结构（Examples、Panics、Errors、Safety）。
> [来源: [RFC 1574 — Documentation Conventions](https://rust-lang.github.io/rfcs/1574-more-api-documentation-conventions.html)]

---

### 2.2 Intra-doc Links

```rust,ignore
/// 使用 [`MyStruct`] 进行演示。
///
/// 也可以使用 [完整路径](crate::module::MyStruct)。
///
/// 引用 Trait 方法: [`Trait::method`](Trait::method)
///
/// 引用标准库: [`Vec::push`] 或 [`std::vec::Vec`]
///
/// 引用外部 crate: [`serde::Serialize`]
pub fn demo() {}

// Intra-doc links 的优势:
// - 编译期验证链接目标存在
// - 重命名时自动更新（重构安全）
// - 生成可点击的 HTML 链接
// - 支持路径解析（包括 use 别名）
```

> **Intra-doc Links**: intra-doc links 是 Rust 文档的**杀手级特性**——它们在编译期验证链接有效性，解决了技术文档中最常见的**链接腐烂**问题。
> [来源: [RFC 1946 — Intra-rustdoc links](https://github.com/rust-lang/rfcs/pull/1946)]

---

### 2.3 mdBook 与知识体系站点

```text
mdBook: Rust 生态的静态站点生成器

  设计目标:
  ├── 为 Rust 官方文档（The Book、Reference、Nomicon）提供支持
  ├── Markdown 源文件 → 静态 HTML
  ├── 支持数学公式（MathJax/KaTeX）
  ├── 支持代码高亮和可编辑代码块
  └── 插件系统（预处理器/后处理器）

  本知识体系的 mdBook 配置:
  ├── book.toml: 站点配置（标题、作者、输出设置）
  ├── SUMMARY.md: 目录结构（自动生成）
  ├── src/: Markdown 源文件
  └── 主题: 自定义 CSS + Mermaid 支持

  Mermaid 集成:
  ├── mdBook 原生不支持 Mermaid
  ├── 通过 custom head（header.hbs）注入 Mermaid.js
  └── 实现: 页面加载时自动渲染 ```mermaid 代码块

  部署流程:
  1. 运行 generate_summary.py 生成 SUMMARY.md
  2. mdbook build 生成静态站点
  3. 部署到 GitHub Pages / Netlify / 自有服务器
```

> **mdBook 洞察**: mdBook 的设计哲学与 Rust 一致——**简单、可扩展、以内容为中心**。它不试图成为全能 CMS，而是专注于将 Markdown 转换为漂亮的文档站点。
> [来源: [mdBook Documentation](https://rust-lang.github.io/mdBook/)]

---

## 三、最佳实践

```text
API 文档规范（RFC 1574 推荐）:

  公共 API 文档结构:
  /// 简短描述（一句话）
  ///
  /// 详细描述（多段，说明功能、设计意图）
  ///
  /// # 示例
  ///
  /// ```
  /// use my_crate::my_function;
  /// let result = my_function(42);
  /// assert_eq!(result, 42);
  /// ```
  ///
  /// # Panics
  ///
  /// 说明什么情况下会 panic。
  ///
  /// # Errors
  ///
  /// 如果返回 Result，说明可能的错误情况。
  ///
  /// # Safety
  ///
  /// 如果是 unsafe 函数，说明调用者需要保证的前置条件。
  ///
  /// # 另见
  ///
  /// - [`related_function`]
  /// - [模块文档](crate::module)

  Crate 级别文档（lib.rs 开头）:
  //! # Crate 名称
  //!
  //! 简短描述 crate 的功能和用途。
  //!
  //! ## 快速开始
  //!
  //! ```
  //! use my_crate::Client;
  //! let client = Client::new();
  //! ```
  //!
  //! ## 功能特性
  //!
  //! - 特性 A
  //! - 特性 B
  //!
  //! ## 最低支持 Rust 版本（MSRV）
  //!
  //! 本 crate 的 MSRV 是 1.70.0。

  文档质量检查清单:
  ├── 所有 pub 项都有文档注释
  ├── 所有示例代码都能通过 doctest
  ├── 所有 intra-doc links 有效
  ├── Safety 注释完整（unsafe API）
  └── CHANGELOG.md 记录重大变更
```

> **最佳实践**: Rust 的文档规范不是**可选的**——`cargo doc` 会对未文档化的公共项发出警告（`#[warn(missing_docs)]`）， crates.io 上的高质量 crate 都有完整的文档。
> [来源: [Rust API Guidelines — Documentation](https://rust-lang.github.io/api-guidelines/documentation.html)]

---

## 四、反命题与边界分析

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: 所有代码示例都应使用 doctest"]
    ROOT --> Q1{"是否需要编译验证?"}
    Q1 -->|是| Q2{"是否是可运行代码?"}
    Q1 -->|否| TEXT["✅ 使用 ```text 或 ```ignore"]
    Q2 -->|是| TRUE["✅ 使用 ```rust（默认 doctest）"]
    Q2 -->|否| IGNORE["✅ 使用 ```ignore 或 ```no_run"]

    style TRUE fill:#c8e6c9
    style TEXT fill:#c8e6c9
    style IGNORE fill:#c8e6c9
```

> **认知功能**: 此决策树帮助选择正确的代码块属性。核心原则是**默认使用 doctest**，只有在确实不需要验证时才使用 ignore/text。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> **使用建议**: doctest 会增加编译时间，但对于公共 API 的示例来说是值得的。
> [来源: [rustdoc — Documentation tests](https://doc.rust-lang.org/rustdoc/write-documentation/documentation-tests.html)]

---

### 4.2 边界极限

```text
边界 1: doctest 的编译时间
├── doctest 需要编译和运行，增加 CI 时间
├── 复杂示例可能依赖外部资源（数据库、网络）
├── 解决方案: 使用 #[cfg(doctest)] 条件编译
└── 或使用 ```no_run 编译但不运行

边界 2: 文档与实现的同步
├── 重构时文档可能过时（即使 doctest 通过）
├── 语义变更可能不影响示例代码的编译
├── 解决方案: 代码审查时强制检查文档更新
└── 使用 intra-doc links 减少手动维护

边界 3: 私有 API 的文档
├── rustdoc 默认不渲染私有项文档
├── 但可以通过 --document-private-items 生成
├── 内部文档需求与公开文档的冲突
└── 解决方案: CI 生成两套文档（公开 + 内部）

边界 4: mdBook 的 Mermaid 支持
├── mdBook 原生不支持 Mermaid
├── 需要自定义 head 模板注入 JS
├── 大页面可能有性能问题
└── 替代方案: 预渲染 Mermaid 为 SVG（mdbook-mermaid 插件）

边界 5: docs.rs 资源限制
├── docs.rs 对 crate 构建有时间限制
├── 非常大的 crate 可能构建失败
├── 自定义构建脚本可能被限制
└── 解决方案: 使用 docs.rs metadata 配置构建设项
```

> **边界要点**: 文档生态的边界主要与**编译时间**、**同步维护**、**工具限制**和**托管平台约束**相关。
> [来源: [docs.rs Build Limits](https://docs.rs/about/builds)]

---

## 五、常见陷阱

```text
陷阱 1: 忘记 doctest 会失败
  ❌ ```rust
     let x = std::fs::read_to_string("file.txt").unwrap();
     // doctest 运行时文件可能不存在！

  ✅ ```no_run
     // 或提供 mock 数据
     let x = "mock data".to_string();

陷阱 2: 文档注释中的代码不合法
  ❌ /// let x = 1 + ;  // 语法错误

  ✅ 运行 cargo test --doc 确保所有示例通过

陷阱 3: intra-doc links 指向私有项
  ❌ /// 参见 [`private_helper`]
     // private_helper 是私有的，链接无效

  ✅ 只链接公共 API，或使用 [文本](path) 格式

陷阱 4: 文档与实现不同步
  ❌ 函数签名变更后忘记更新文档中的示例

  ✅ 将 cargo test --doc 加入 CI
     // doctest 失败会阻止合并

陷阱 5: 过度文档化
  ❌ 为每个私有函数写长文档
  // 维护成本高，收益低

  ✅ 优先文档化公共 API
  // 私有函数用简洁注释说明意图即可
```

> **陷阱总结**: 文档生态的陷阱主要与**doctest 可靠性**、**链接有效性**、**同步维护**和**文档优先级**相关。
> [来源: [Rust RFC 1574 — Common Mistakes](https://rust-lang.github.io/rfcs/1574-more-api-documentation-conventions.html)]

---

## 六、来源与延伸阅读

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [rustdoc Documentation](https://doc.rust-lang.org/rustdoc/) | ✅ 一级 | 官方文档工具 |
| [RFC 1574 — API Documentation](https://github.com/rust-lang/rfcs/pull/1574) | ✅ 一级 | 文档规范 RFC |
| [mdBook Guide](https://rust-lang.github.io/mdBook/) | ✅ 一级 | 静态站点生成器 |
| [RFC 1946 — Intra-doc Links](https://github.com/rust-lang/rfcs/pull/1946) | ✅ 一级 | 内部链接 RFC |
| [docs.rs](https://docs.rs/about) | ✅ 一级 | crate 文档托管 |
| [Rust API Guidelines — Documentation](https://rust-lang.github.io/api-guidelines/documentation.html) | ✅ 一级 | API 文档指南 |

---

## 相关概念文件

- [Cargo Toolchain](./01_toolchain.md) — Cargo 与 rustdoc 集成
- [Macros](../03_advanced/04_macros.md) — 文档宏（doc comments）
- [Module System](../02_intermediate/10_module_system.md) — 模块级文档

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成
