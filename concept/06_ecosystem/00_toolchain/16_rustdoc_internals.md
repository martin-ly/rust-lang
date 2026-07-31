# Rustdoc 内部实现

> **EN**: Rustdoc Internals
> **Summary**: Deep dive into rustdoc's implementation inside `rustc`: partial compilation to HIR, the `clean` AST, passes (intra-doc links, coverage, strips, lints), HTML/JSON rendering with Askama, doctest extraction, and local testing workflows.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **F+S** — Formal / Structure
> **双维定位**: F×Inf — 编译器文档工具内部实现
> **定位**: 揭示 `rustdoc` 作为 `rustc` 子系统的完整数据流，从源码经 `clean` AST、多轮 pass，到 HTML/JSON 渲染与 doctest 提取，服务于需要调试、扩展或贡献 rustdoc 的 toolchain 内部开发者。
> **前置概念**: [Toolchain](01_toolchain.md) · [Documentation](../09_testing_and_quality/02_documentation.md) · [rustc Query System](../../04_formal/05_rustc_internals/01_rustc_query_system.md) · [Name Resolution and HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md)
> **后置概念**: [Rustdoc 1.96–1.97 变更](07_rustdoc_196_changes.md) · [Compiler Internals](04_compiler_internals.md)

---

> **来源**: [Rustc Dev Guide — Rustdoc](https://rustc-dev-guide.rust-lang.org/rustdoc.html) ·
> [Rustc Dev Guide — Rustdoc Internals](https://rustc-dev-guide.rust-lang.org/rustdoc-internals.html) ·
> [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) ·
> [RFC 1946 — Intra-rustdoc links](https://github.com/rust-lang/rfcs/pull/1946) ·
> [RFC 2963 — Rustdoc JSON](https://rust-lang.github.io/rfcs/2963-rustdoc-json.html) ·
> [rustdoc source tree — `src/librustdoc`](https://github.com/rust-lang/rust/tree/master/src/librustdoc) ·
> [Askama crate docs](https://docs.rs/askama/)

---

## 📑 目录

- [Rustdoc 内部实现](#rustdoc-内部实现)
  - [📑 目录](#-目录)
  - [一、核心概念与架构](#一核心概念与架构)
    - [1.1 rustdoc 在 rustc 中的位置](#11-rustdoc-在-rustc-中的位置)
    - [1.2 从 crate 到文档的数据流](#12-从-crate-到文档的数据流)
    - [1.3 `DocContext` 与 `run_global_ctxt`](#13-doccontext-与-run_global_ctxt)
  - [二、从 Crate 到 Clean AST](#二从-crate-到-clean-ast)
    - [2.1 `clean/mod.rs` 与 Clean 类型](#21-cleanmodrs-与-clean-类型)
    - [2.2 `visit_ast::RustdocVisitor`](#22-visit_astrustdocvisitor)
    - [2.3 `#[doc(inline)]` / `#[doc(no_inline)]`](#23-docinline--docno_inline)
    - [2.4 跨 crate inlining](#24-跨-crate-inlining)
  - [三、Clean AST 上的 Passes](#三clean-ast-上的-passes)
    - [3.1 文档覆盖率（Doc Coverage）](#31-文档覆盖率doc-coverage)
    - [3.2 Intra-doc Links](#32-intra-doc-links)
    - [3.3 Trait Impl 收集](#33-trait-impl-收集)
    - [3.4 `doc(cfg(...))` 传播](#34-doccfg-传播)
    - [3.5 rustdoc Lints](#35-rustdoc-lints)
    - [3.6 Strip Passes](#36-strip-passes)
  - [四、从 Clean 到 HTML / JSON](#四从-clean-到-html--json)
    - [4.1 `formats::renderer::run_format`](#41-formatsrendererrun_format)
    - [4.2 `Context` / `SharedContext`](#42-context--sharedcontext)
    - [4.3 Askama 模板](#43-askama-模板)
    - [4.4 `html/render/print_item.rs`](#44-htmlrenderprint_itemrs)
    - [4.5 `html/markdown.rs` 与语法高亮](#45-htmlmarkdownrs-与语法高亮)
    - [4.6 搜索索引](#46-搜索索引)
    - [4.7 `src/` 源码页](#47-src-源码页)
    - [4.8 JSON 输出模式](#48-json-输出模式)
  - [五、Doctest 与独立 Markdown 模式](#五doctest-与独立-markdown-模式)
    - [5.1 Doctest 提取：`test.rs` / `make_test` / `find_testable_code`](#51-doctest-提取testrs--make_test--find_testable_code)
    - [5.2 独立 Markdown 渲染](#52-独立-markdown-渲染)
  - [六、本地测试与调试](#六本地测试与调试)
    - [6.1 用 `./x doc library` 构建](#61-用-x-doc-library-构建)
    - [6.2 本地 HTTP 服务器](#62-本地-http-服务器)
  - [七、来源与延伸阅读](#七来源与延伸阅读)
  - [⚠️ 反命题 / 边界分析 / 常见陷阱](#️-反命题--边界分析--常见陷阱)
    - [反命题 1：“rustdoc 只是 Markdown 处理器”](#反命题-1rustdoc-只是-markdown-处理器)
    - [反命题 2：“`cargo doc` 会完整编译整个 crate”](#反命题-2cargo-doc-会完整编译整个-crate)
    - [边界：intra-doc link 解析路径与 reexport 内联](#边界intra-doc-link-解析路径与-reexport-内联)
    - [边界：跨 crate 文档与本地文档的差异](#边界跨-crate-文档与本地文档的差异)
    - [常见陷阱：`compile_fail` doctest 的 error code 漂移](#常见陷阱compile_fail-doctest-的-error-code-漂移)
    - [常见陷阱：CSS / JS 静态资源缓存](#常见陷阱css--js-静态资源缓存)
    - [反例：intra-doc link 在 reexport 后失效](#反例intra-doc-link-在-reexport-后失效)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)
  - [相关概念链接](#相关概念链接)
  - [补充国际权威来源（P1/P2 覆盖）](#补充国际权威来源p1p2-覆盖)

---

## 一、核心概念与架构

rustdoc 并非独立的 Markdown 处理器，而是 `rustc` 源码树中复用编译器前端的文档生成子系统。理解它的位置、数据流与核心数据结构，是调试、扩展或贡献 rustdoc 的基础。

### 1.1 rustdoc 在 rustc 中的位置

`rustdoc` 不是独立工具，而是 `rustc` 源码树中 `src/librustdoc` 目录下的一个 crate。它复用编译器前端直到 **HIR（High-level Intermediate Representation）** 的解析与类型信息，然后跳过后端代码生成，直接生成文档产物。这意味着 rustdoc 必须理解 name resolution、macro expansion、`cfg` 条件编译和 trait resolution，但不会运行 borrow checker 或 LLVM 后端。

> **关键洞察**：rustdoc 的“部分编译”模型决定了它必须维护一个自己的 `TyCtxt` 视图，并在 HIR 层提取文档注释，而不是在源码文本层做字符串分析。文档中 `# Safety` 段落的渲染本身也构成 Rust [Safety Boundaries](../../05_comparative/03_domain_comparisons/01_safety_boundaries.md) 知识的一部分。
> [来源：Rustc Dev Guide — Rustdoc](https://rustc-dev-guide.rust-lang.org/rustdoc.html)

### 1.2 从 crate 到文档的数据流

rustdoc 的数据流可分为四个阶段：

```text
.rs 源码
   │
   ▼
rustc 前端（parse → expand → resolve → HIR）
   │
   ▼
librustdoc::clean  （HIR → Clean AST）
   │
   ▼
librustdoc::passes  （多轮变换与检查）
   │
   ▼
librustdoc::formats  （HTML / JSON / doctest）
```

1. **前端**：调用 `rustc_interface` 将源码解析到 HIR，获取 `TyCtxt`。
2. **Clean**：把 HIR 节点转换为 rustdoc 自有的 `clean::Item` 树，屏蔽 HIR 的复杂度。
3. **Passes**：在 Clean AST 上运行文档覆盖率、intra-doc link 解析、strip 等变换。
4. **Formats**：渲染 HTML（默认）、JSON（ nightly / unstable），或提取 doctest。

> **L5 延伸**：从这一数据流出发，可进一步在 [Performance Optimization](../10_performance/01_performance_optimization.md) 中分析 rustdoc 的编译时间、内存占用与增量文档构建策略。

### 1.3 `DocContext` 与 `run_global_ctxt`

入口函数 `librustdoc::core::run_global_ctxt` 接收编译器运行完毕后的 `global_ctxt`，构造出 rustdoc 的 `DocContext`：

```rust,ignore
// src/librustdoc/core.rs
pub struct DocContext<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    /// 当前 crate 的 `clean::Crate`（经过初步转换）
    pub module: Item,
    /// 已内联的外部项缓存
    pub inlined: FxHashSet<DefId>,
    /// 已收集的 trait 实现
    pub collected_trait_impls: bool,
    /// 渲染器配置（输出格式、主题等）
    pub render_options: RenderOptions,
    /// ...
}
```

`DocContext` 是 rustdoc 后续所有 pass 与渲染步骤的共享状态容器。它把 `TyCtxt` 的查询能力与 rustdoc 自有的文档语义（如 inlining、strip、cfg）粘合在一起。

```rust,ignore
// 概念性入口伪代码（非真实源码）
pub fn run_global_ctxt(
    krate: rustc_hir::Crate,
    render_options: RenderOptions,
    output_format: OutputFormat,
) -> Result<()> {
    let mut ctxt = DocContext::new(tcx, render_options);
    let mut clean_crate = clean::krate(&mut ctxt, krate);
    clean_crate = run_passes(clean_crate, &ctxt);
    run_format(clean_crate, ctxt, output_format)
}
```

> **注意**：`run_global_ctxt` 在 `rustc` 完成 HIR 构建后才被回调调用；rustdoc 不会触发完整的 MIR / codegen 查询，因此比正常编译快得多，但仍需解析所有依赖的元数据。

---

## 二、从 Crate 到 Clean AST

rustdoc 首先调用 rustc 前端获得 HIR 与 `TyCtxt`，然后通过 `clean` 模块把 HIR 节点转换为更精简、更文档化的 `clean::Item` 树。本节解释 Clean AST 的设计动机、关键类型和跨 crate inlining 的语义影响。

### 2.1 `clean/mod.rs` 与 Clean 类型

`src/librustdoc/clean/mod.rs` 实现 HIR → `clean::Item` 的转换。`clean` 模块定义了一套简化的 AST 表示，只保留文档生成关心的字段：可见性、泛型、trait bound、doc 属性、源码位置等。

```rust,ignore
// src/librustdoc/clean/mod.rs（概念片段）
pub fn krate(cx: &mut DocContext<'_>, krate: rustc_hir::Crate) -> Crate {
    let module = visit_ast::RustdocVisitor::new(cx).visit(krate);
    Crate {
        module,
        external_traits: cx.external_traits.clone(),
        // ...
    }
}
```

`clean::utils::krate` 是实际触发转换的辅助函数。Clean 的核心价值是**隔离**：HIR 随编译器快速演进，而 rustdoc 的渲染逻辑基于稳定的 `clean` 抽象，减少前端重构对文档生成的影响。

### 2.2 `visit_ast::RustdocVisitor`

`src/librustdoc/visit_ast.rs` 中的 `RustdocVisitor` 负责遍历 HIR，决定哪些项进入 Clean AST。它会：

- 跳过 `#[doc(hidden)]` 的项（除非启用 `--document-hidden-items`）。
- 处理 `extern crate`、`use` 声明与 reexport。
- 把模块层级展平为 rustdoc 的模块树。
- 为每个项附加 `Attributes`（解析出的 doc 注释与属性）。

```rust,ignore
// src/librustdoc/visit_ast.rs（概念片段）
struct RustdocVisitor<'a, 'tcx> {
    cx: &'a mut DocContext<'tcx>,
    view_item_stack: Vec<DefId>,
    inlining: bool,
}

impl RustdocVisitor<'_, '_> {
    fn visit_item(&mut self, item: &hir::Item<'_>) -> Option<Item> {
        // 1. 解析属性，判断是否显示
        // 2. 处理 use / extern crate / reexport
        // 3. 递归进入子模块
        // 4. 构造 clean::Item
    }
}
```

### 2.3 `#[doc(inline)]` / `#[doc(no_inline)]`

rustdoc 对 `pub use` reexport 有两种处理策略：

| 属性 | 行为 | 典型场景 |
| :--- | :--- | :--- |
| 默认 | 在父模块列出 reexport 链接，目标仍显示在原始位置 | 常规 reexport |
| `#[doc(inline)]` | 把被 reexport 项的文档“内联”到当前模块，仿佛它定义在这里 | facade 模式（如 `futures`） |
| `#[doc(no_inline)]` | 强制只显示链接，不展开内容 | 避免文档重复 |

```rust,ignore
// 默认行为：显示在 reexport 列表中
pub use inner::Foo;

// 内联：Foo 的完整文档页出现在 facade 模块下
#[doc(inline)]
pub use inner::Bar;

// 强制不内联
#[doc(no_inline)]
pub use inner::Baz;
```

判定依据：内联会改变文档的“逻辑位置”，进而影响 intra-doc link 的解析路径；贡献 rustdoc 时处理 inlining 必须同时更新 `inlined` 集合，防止同一 `DefId` 被重复处理。

### 2.4 跨 crate inlining

当文档依赖外部 crate 的 public item 时，rustdoc 需要从 `.rmeta` 元数据中把外部项“拉进来”并内联到当前文档。这由 `clean::inline` 模块处理：

- `try_inline`：根据 `DefId` 判断能否内联。
- `load_attrs`：从外部 crate 加载 doc 属性。
- `record_extern_fqn`：记录外部项的完全限定名，用于生成链接。

跨 crate inlining 的难点在于：**外部 crate 的 HIR 不可用**，只能依赖 `metadata` 中的摘要信息。如果外部项的文档属性缺失或解析失败，rustdoc 会回退到只显示类型签名。

> **常见陷阱**：修改 `rustc_metadata` 中存储的字段时，必须同步检查 rustdoc 的 cross-crate inlining 路径，否则 docs.rs 上大量 crate 的文档会出现空白页或断链。

---

## 三、Clean AST 上的 Passes

Passes 是 rustdoc 的中间变换层，位于 `src/librustdoc/passes/`。它们在 Clean AST 上运行多轮，每轮完成单一职责。

### 3.1 文档覆盖率（Doc Coverage）

`collect_intra_doc_links` 之外的 `calculate_doc_coverage` pass 统计公开 API 的文档覆盖情况：

- 有文档注释的 public item 比例。
- 有代码示例的 public item 比例。
- 输出到 `target/doc/{crate}/coverage/index.html`（HTML）或 stderr（`--show-coverage`）。

```bash
# 查看文档覆盖率
rustdoc --show-coverage src/lib.rs
```

### 3.2 Intra-doc Links

`collect_intra_doc_links` 是 rustdoc 最著名的 pass 之一。它解析 Markdown 中的 ``[`path::to::Item`]`` 语法，将其转换为指向文档页面的锚点链接。

解析过程：

1. 用 Markdown 解析器定位所有 ``[`...`]`` 与 `[text](...)``。
2. 对 ``[`path`]`` 形式，调用 name resolution 在 `TyCtxt` 中解析路径。
3. 根据解析到的 `DefId` 生成目标 URL 与 anchor。
4. 无法解析时发出 `rustdoc::broken_intra_doc_links` lint。

```rust,ignore
/// 使用 [`Vec::push`] 添加元素。
/// 等价于 [`std::vec::Vec::push`].
pub fn demo(v: &mut Vec<i32>) {
    v.push(1);
}
```

> **关键洞察**：intra-doc link 是 rustdoc 把“文档”与“类型系统”连接的关键机制；它的解析依赖 rustc name resolution，因此必须等待 HIR 构建完成后才能运行。
> [来源：Rustc Dev Guide — Intra-doc links](https://rustc-dev-guide.rust-lang.org/rustdoc-internals.html#intra-doc-links)

### 3.3 Trait Impl 收集

`collect_trait_impls` pass 把当前 crate 及已内联外部 crate 中所有满足条件的 trait implementation 收集起来，挂到对应类型与 trait 的文档页。这是文档中“Implementations”与“Auto trait implementation”列表的来源。

### 3.4 `doc(cfg(...))` 传播

`propagate_doc_cfg` pass 把 `#[cfg(...)]` 条件转换为 `#[doc(cfg(...))]` 显示信息，让 docs.rs 等托管站点能标注“此 API 仅在特定平台/特性下可用”。

```rust,ignore
#[cfg(unix)]
#[doc(cfg(unix))]  // 显式声明，rustdoc 会渲染平台标签
pub fn unix_only() {}
```

### 3.5 rustdoc Lints

rustdoc 注册了一组专用 lint，部分在 pass 中执行：

| Lint | 触发场景 | 默认级别 |
| :--- | :--- | :--- |
| `rustdoc::broken_intra_doc_links` | intra-doc link 无法解析 | warn |
| `rustdoc::bare_urls` | Markdown 中出现裸 URL 未用尖括号包裹 | warn |
| `rustdoc::invalid_html_tags` | 文档注释中存在无效 HTML 标签 | warn |
| `rustdoc::invalid_rust_codeblocks` | 代码块语言标记无法识别 | warn |
| `rustdoc::missing_doc_code_examples` | 公共 API 缺少示例 | allow |

```bash
# CI 中提升为错误
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
```

### 3.6 Strip Passes

Strip passes 根据可见性过滤 Clean AST 中的项：

| Pass | 行为 | 对应标志 |
| :--- | :--- | :--- |
| `strip-hidden` | 移除 `#[doc(hidden)]` 项 | 默认 |
| `strip-private` | 移除私有项 | `--document-private-items` 关闭时 |
| `strip-priv-imports` | 移除私有 `use` 声明 | 默认 |

这些 passes 的顺序很重要：通常先 strip-hidden，再 strip-private，确保不会先移除再被其他 pass 引用。

---

## 四、从 Clean 到 HTML / JSON

Clean AST 经过 passes 后被传递给渲染器。本节跟踪 HTML（默认）与 JSON（nightly/unstable）两种输出格式的生成路径，包括模板渲染、搜索索引和源码页。

### 4.1 `formats::renderer::run_format`

`src/librustdoc/formats/renderer.rs` 中的 `run_format` 是渲染阶段的统一入口。它根据 `OutputFormat` 分发到 HTML 渲染器或 JSON 渲染器：

```rust,ignore
// src/librustdoc/formats/renderer.rs（概念片段）
pub fn run_format<'tcx, T: FormatRenderer<'tcx>>(
    krate: clean::Crate,
    context: Context<'tcx>,
) -> Result<(), Error> {
    let mut renderer = T::init(krate, context)?;
    // 渲染 crate 根、模块、item 页
    renderer.render()?
}
```

### 4.2 `Context` / `SharedContext`

HTML 渲染器维护两层上下文：

- **`Context`**：当前正在渲染的页面上下文，包含当前路径、父模块、item 信息等。
- **`SharedContext`**：全局共享状态，包含 crate 名、资源路径、搜索索引数据、主题设置等。

```rust,ignore
// src/librustdoc/html/render/context.rs（概念片段）
pub struct Context<'a, 'tcx> {
    pub shared: &'a SharedContext<'a>,
    /// 当前文件相对根目录的路径前缀
    pub path: Vec<String>,
    /// 当前所在模块
    pub current: Item,
    /// ...
}

pub struct SharedContext<'a> {
    pub src_root: PathBuf,
    pub crate_name: String,
    pub issue_tracker_base_url: Option<String>,
    pub resource_suffix: String,
    pub search_index: Vec<IndexItem>,
    /// ...
}
```

### 4.3 Askama 模板

rustdoc 的 HTML 使用 [Askama](https://docs.rs/askama/)（Jinja-like 模板引擎）生成。模板位于 `src/librustdoc/html/templates/`。主要模板包括：

- `page.html`：整页骨架（head、sidebar、footer）。
- `print_item.html`：单个 item（fn/struct/trait 等）的详情页。
- `type_layout.html`：类型布局可视化。
- `source.html`：源码页。

模板与 Rust 代码通过 `#[derive(Template)]` 绑定，编译期检查模板变量名。

### 4.4 `html/render/print_item.rs`

`src/librustdoc/html/render/print_item.rs` 负责把单个 `clean::Item` 渲染为 HTML 主体。它为每种 item kind（`ItemType::Struct`、`ItemType::Trait`、`ItemType::Function` 等）实现对应的签名、实现列表、文档注释布局。

### 4.5 `html/markdown.rs` 与语法高亮

`src/librustdoc/html/markdown.rs` 处理 Markdown 到 HTML 的转换，并集成 rustdoc 特有的扩展：

- **Heading anchor 自动生成**。
- **Rust 代码块语法高亮**：调用 `html/highlight.rs` 对 `rustc_lexer` 分词结果上色。
- **Intra-doc link 替换**（pass 已解析，渲染时直接输出 `<a>`）。
- **`#[doc = include_str!(...)]` 展开后的 Markdown 处理**。

```rust,ignore
/// ```rust
/// let x = 1;
/// ```
pub fn foo() {}
```

上述注释经 `markdown.rs` 后会生成带 `language-rust` 类名和语法高亮的 `<pre>` 块。

### 4.6 搜索索引

rustdoc 在渲染阶段同步构建搜索索引（`search-index.js`）。索引项包含：

- 名称、类型（function/trait/struct 等）、路径、描述摘要。
- 泛型参数、parent module、disambiguator。

前端搜索通过 `static.files/search.js` 在浏览器端加载 `search-index.js` 并执行模糊匹配。

### 4.7 `src/` 源码页

`--generate-source-tarball` 与源码页功能把 crate 源码渲染为带语法高亮的 HTML。实现位于 `src/librustdoc/html/sources.rs`，它复用与 item 页相同的高亮逻辑，但不对源码做 Clean AST 转换。

### 4.8 JSON 输出模式

JSON 输出（`rustdoc --output-format json`）是 unstable 功能，通过 `--enable-index-page` 等配套选项控制。它把 Clean AST 序列化为结构化的 JSON 文档，供外部工具（如 rustdoc JSON 的 IDE、绑定生成器、文档分析工具）消费。

```bash
# nightly / unstable 用法示例
rustdoc +nightly -Z unstable-options --output-format json src/lib.rs
```

JSON 模式与 HTML 模式共享 Clean AST 和大部分 pass，但跳过 Askama 渲染，直接输出 `index.json` 与按 item 分片的 JSON 文件。

> **注意**：截至 Rust 1.97，JSON 输出仍标记为 unstable；稳定 crate 不应在 CI 中依赖其 schema。

---

## 五、Doctest 与独立 Markdown 模式

`cargo test --doc` 的实际执行者是 rustdoc 而非 rustc。本节解释 doctest 如何从 doc 注释中提取、包装成独立 crate 并运行，以及独立 Markdown 文件的渲染路径。

### 5.1 Doctest 提取：`test.rs` / `make_test` / `find_testable_code`

`cargo test --doc` 的实际执行者是 rustdoc 的 `test.rs` 模块。其流程为：

1. **提取**：`find_testable_code` 扫描所有 doc 注释中的 Markdown 代码块。
2. **生成测试**：`make_test` 把每个 ```rust` 块包装成可编译的 crate，包括：
   - 注入 `#![allow(...)]` 与 `extern crate`。
   - 把隐藏行（`# ...`）移到实际代码中但不在文档中显示。
   - 为 `compile_fail`、`no_run`、`should_panic`、`edition2021` 等属性生成对应测试类型。
3. **运行**：调用 `rustc` 编译并执行生成的测试文件。

```rust,ignore
// src/librustdoc/test.rs（概念片段）
pub fn make_test(
    code: &str,
    crate_name: Option<&str>,
    dont_insert_main: bool,
    opts: &TestOptions,
    edition: Edition,
) -> (String, usize, bool) {
    // 1. 处理 # 隐藏行
    // 2. 决定是否插入 fn main()
    // 3. 注入 crate 属性与 extern crate
}
```

| 属性 | 含义 |
| :--- | :--- |
| `ignore` | 不编译、不运行 |
| `no_run` | 编译，但不运行 |
| `should_panic` | 运行，期望 panic |
| `compile_fail` | 期望编译失败 |
| `edition2021` / `edition2024` | 指定 edition |

> **关键洞察**：doctest 的“隐藏行”机制是文档可读性与测试完整性的平衡——`#` 前缀的代码在文档中不可见，但在测试生成时会被保留，常用于 `use` 语句和初始化。

### 5.2 独立 Markdown 渲染

rustdoc 也能直接渲染独立的 Markdown 文件：

```bash
rustdoc README.md
```

此时 rustdoc 把它当作一个“没有 crate 上下文”的页面，只做 Markdown → HTML 转换，不执行 intra-doc link 解析、不生成搜索索引。该模式常用于把项目 README 渲染为 HTML 预览。

---

## 六、本地测试与调试

为 rustc/rustdoc 贡献代码时，需要掌握 rustc 源码树中的本地构建与调试命令。本节覆盖 `./x doc`、`rustdoc` 本地 HTTP 服务器等常用工作流。

### 6.1 用 `./x doc library` 构建

在 rustc 源码树中，最常用的本地 rustdoc 测试命令是：

```bash
# 构建并生成 std 文档
./x.py doc library/std

# 或简称
./x doc library

# 仅构建 rustdoc 本身
./x.py build src/tools/rustdoc
```

`./x.py` 是 rustc 的 bootstrap 脚本。`doc library` 会：

1. 编译 stage0 的 rustdoc。
2. 用 stage0 rustdoc 生成标准库文档。
3. 输出到 `build/<host>/doc`。

### 6.2 本地 HTTP 服务器

生成后可用任意静态服务器预览：

```bash
# Python
python -m http.server 8080 --directory build/<host>/doc

# Rust ecosystem
cargo install miniserve
miniserve build/<host>/doc --index index.html
```

> **调试建议**：修改 rustdoc 源码后，应先 `./x.py build src/tools/rustdoc` 再 `./x.py doc library/std --stage 1`，确保改动实际生效；stage0  rustdoc 是预编译二进制，不会反映你的修改。

---

## 七、来源与延伸阅读

| 资源 | 说明 |
| :--- | :--- |
| [Rustc Dev Guide — Rustdoc](https://rustc-dev-guide.rust-lang.org/rustdoc.html) | rustdoc 总览 |
| [Rustc Dev Guide — Rustdoc Internals](https://rustc-dev-guide.rust-lang.org/rustdoc-internals.html) | 内部实现细节 |
| [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) | 用户-facing 文档 |
| [RFC 1946 — Intra-rustdoc links](https://github.com/rust-lang/rfcs/pull/1946) | intra-doc link 设计 |
| [RFC 2963 — Rustdoc JSON](https://rust-lang.github.io/rfcs/2963-rustdoc-json.html) | JSON 输出格式 |

---

## ⚠️ 反命题 / 边界分析 / 常见陷阱

rustdoc 的“部分编译”模型带来了许多与直觉不符的边界。本节澄清常见误解，并给出 intra-doc link、doc test error code 和缓存等具体陷阱。

### 反命题 1：“rustdoc 只是 Markdown 处理器”

**错误**。rustdoc 深度依赖 `rustc` 的 name resolution 与类型信息。如果只在文本层处理 Markdown，就无法实现 intra-doc link、跨 crate inlining、`doc(cfg(...))` 平台标签等功能。

### 反命题 2：“`cargo doc` 会完整编译整个 crate”

**错误**。rustdoc 只运行到 HIR，不会生成 MIR 或 LLVM IR。因此 borrow-check 错误不会阻止 `cargo doc`（除非错误发生在 name resolution / macro expansion 阶段）。

### 边界：intra-doc link 解析路径与 reexport 内联

`#[doc(inline)]` 会改变项在文档树中的“逻辑父模块”，因此同一 intra-doc link 在“内联前”和“内联后”可能解析到不同页面。贡献 rustdoc 时，link resolution pass 必须在 inlining pass 之后运行。

### 边界：跨 crate 文档与本地文档的差异

docs.rs 使用 nightly rustdoc 并启用 `--cfg docsrs` 等标志，可能与本地 stable `cargo doc` 行为不同。例如 `doc(cfg(...))` 标签在 docs.rs 上更完整，因为 docs.rs 会为多个 target 构建文档。

### 常见陷阱：`compile_fail` doctest 的 error code 漂移

```rust,ignore
/// ```compile_fail,E0308
/// let x: u32 = "not a number";
/// ```
```

rustc 错误码可能随版本重编号或合并，导致原本标注 `E0308` 的 `compile_fail` 测试在新版本 rustc 上失败。CI 应把 doctest 与特定 Rust 版本绑定，或避免精确 error code 断言。

### 常见陷阱：CSS / JS 静态资源缓存

rustdoc 输出的 `static.files/` 包含哈希化文件名以便长期缓存，但 `index.html` 与模块页引用这些资源时使用相对路径。
如果 CDN 或静态服务器配置错误，可能出现页面样式丢失。
解决方式是确保 `static.files` 目录与 HTML 页面保持相对位置不变。

### 反例：intra-doc link 在 reexport 后失效

```rust,ignore
// crate_a/src/lib.rs
pub mod inner {
    /// See [Foo]
    pub struct Bar;
    pub struct Foo;
}

// crate_b/src/lib.rs
pub use crate_a::inner::*; // 扁平 reexport
```

在上例中，`crate_a::inner::Bar` 的 doc 注释使用相对路径 `[Foo]`。当 `crate_b` 通过 `pub use crate_a::inner::*` 扁平 reexport 后，`Bar` 在文档树中的逻辑父模块从 `crate_a::inner` 变为 `crate_b`。此时 `[Foo]` 在 `crate_b` 的文档中可能解析失败，因为 `crate_b` 下并不存在 `Foo`。这说明了 link resolution 必须在 inlining pass 之后、针对最终文档树进行的原因。

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((Rustdoc 内部实现))
    前端
      Parse
      Expand
      Resolve
      HIR
    Clean AST
      clean/mod.rs
      visit_ast
      #[doc(inline)]
      跨 crate inlining
    Passes
      文档覆盖率
      intra-doc links
      trait impl 收集
      doc(cfg) 传播
      lints
      strip passes
    渲染
      HTML
        Context / SharedContext
        Askama 模板
        print_item.rs
        markdown.rs
        搜索索引
        src/ 源码页
      JSON
        unstable
    Doctest
      test.rs
      make_test
      find_testable_code
    本地测试
      ./x doc library
      HTTP 服务器
```

> **认知功能**：本 mindmap 把 rustdoc 的四个主要阶段（前端 / Clean / Passes / 输出）与两个特殊模式（HTML/JSON、Doctest）可视化，帮助内部开发者快速定位源码目录与数据流。

---

## 相关概念链接

- [Rustdoc 1.96–1.97 变更](07_rustdoc_196_changes.md) — 近期 rustdoc 稳定特性与渲染改进
- [Toolchain](01_toolchain.md) — 工具链总览
- [Documentation](../09_testing_and_quality/02_documentation.md) — 文档生态与实践
- [rustc Query System](../../04_formal/05_rustc_internals/01_rustc_query_system.md) — rustdoc 复用的查询基础设施
- [Name Resolution and HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) — rustdoc 输入的编译器表示
- [Compiler Internals](04_compiler_internals.md) — rustc 内部机制总览

## 补充国际权威来源（P1/P2 覆盖）

- [RustBelt project](https://plv.mpi-sws.org/rustbelt/)
- [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982)
