> **Canonical 说明**: 本文件专注 **Askama 编译期 Jinja-like 模板引擎的派生宏（Macro）架构**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [Web 框架生态](../../../../concept/06_ecosystem/04_web_and_networking/27_web_frameworks.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / askama
>
> **层级**: L3-L5

---

# Askama Crate 架构解构 {#askama-crate-架构解构}

> **EN**: Askama Architecture
> **Summary**: Askama Crate 架构解构 Askama Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5
>
> **知识领域**: 模板引擎、HTML 渲染、类型安全、编译期代码生成
>
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 1. 引言：Askama 在 Rust 模板生态中的定位 {#1-引言askama-在-rust-模板生态中的定位}

> **[来源: [askama crates.io](https://crates.io/crates/askama)]**

`Askama` 是 Rust 生态中**类型安全、编译期渲染**的模板引擎，采用 Jinja-like 语法。它的核心设计是将模板文件或内联模板在编译期转换为 Rust 代码，从而把运行时（Runtime）语法错误和字段名错误转变为编译错误。

> [来源: [askama docs.rs](https://docs.rs/askama/latest/askama/index.html#integrations)]

与动态模板引擎（如 Handlebars、Tera）相比，Askama 的取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **渲染时机** | 编译期生成渲染代码 | 运行时无解析开销，错误前置 |
| **类型安全** | 模板字段与 Rust struct 绑定 | 字段缺失/类型不匹配在编译期报错 |
| **语法** | Jinja-like（`{{ }}`、`{% %}`） | 前端/模板工程师迁移成本低 |
| **文件组织** | 默认 `templates/` 目录或 `source` 内联 | 支持传统 MVC 目录结构 |
| **框架集成** | 提供 axum / actix-web / salvo / warp 集成 feature | 可直接作为 `IntoResponse` |

> [来源: [askama GitHub Repository](https://github.com/djc/askama)]

```rust,ignore
use askama::Template;

#[derive(Template)]
#[template(source = "<h1>Hello, {{ name }}!</h1>", ext = "html")]
struct HelloTemplate<'a> {
    name: &'a str,
}

fn main() {
    println!("{}", HelloTemplate { name: "Askama" }.render().unwrap());
}
```

> [来源: [askama book](https://djc.github.io/askama/)]

---

## 2. 核心 API 架构 {#2-核心-api-架构}

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 派生宏 `#[derive(Template)]` {#21-派生宏-derivetemplate}

Askama 的入口是派生宏。编译期根据 `#[template(...)]` 属性定位模板源，并生成一个 `render()` 方法：

```rust,ignore
#[derive(Template)]
#[template(path = "hello.html")]  // 默认查找 templates/hello.html
struct HelloTemplate<'a> {
    name: &'a str,
}
```

> [来源: [askama::Template trait](https://docs.rs/askama/latest/askama/index.html#integrations)]

宏展开后，结构体字段成为模板上下文。模板中引用（Reference）的变量必须在 struct 中定义，否则编译报错。

### 2.2 模板语法与控制结构 {#22-模板语法与控制结构}

Askama 支持 Jinja 风格的过滤器、循环、条件、继承和包含：

```jinja2
{% extends "base.html" %}
{% block content %}
  <h1>{{ title|escape }}</h1>
  <ul>
  {% for item in items %}
    <li>{{ item }}</li>
  {% endfor %}
  </ul>
{% endblock %}
```

> [来源: [askama 模板语法](https://askama.readthedocs.io/en/stable/template_syntax.html)]

### 2.3 渲染流程 {#23-渲染流程}

```mermaid
graph LR
    STRUCT[Context Struct] --> DERIVE[#[derive(Template)]]
    TEMPLATE[.html Template] --> DERIVE
    DERIVE --> RENDER[render() -> String]
    RENDER --> RESPONSE[IntoResponse / HttpResponse]
```

渲染在运行时是纯字符串拼接，无模板解析步骤。由于代码在编译期生成，LLVM 可以内联小型模板，性能接近手写 `format!`。

### 2.4 Web 框架集成 {#24-web-框架集成}

通过启用相应 feature，Askama 模板可直接作为 Web 框架响应：

```toml
askama = { version = "0.16.0", features = ["with-axum"] }
```

```rust,ignore
use askama::Template;
use axum::{response::IntoResponse, routing::get, Router};

#[derive(Template)]
#[template(path = "page.html")]
struct PageTemplate { title: String }

async fn page() -> impl IntoResponse {
    PageTemplate { title: "Askama + Axum".into() }
}
```

> [来源: [askama axum integration](https://docs.rs/askama/latest/askama/index.html#integrations)]

---

## 3. 与 axum / actix-web 及同类模板引擎对比 {#3-与-axum-actix-web-及同类模板引擎对比}

> **[来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]**

| 维度 | Askama | Maud | Tera | Axum/Actix-web 原生 |
|:--|:--|:--|:--|:--|
| **语法风格** | Jinja-like | Rust DSL (`html!` 宏) | Jinja-like | 无（直接返回字符串/JSON） |
| **渲染时机** | 编译期 | 编译期 | 运行时解析 | 运行时（Runtime） |
| **类型安全** | 强（字段编译期检查） | 极强（Rust 表达式） | 弱（动态上下文） | 强（返回类型） |
| **模板文件** | 支持 `.html` 文件 | 通常内联 | 支持 `.html` 文件 | 不适用 |
| **与 axum 集成** | `with-axum` feature | `axum` feature | 手动渲染后返回 | 原生支持 |
| **与 actix-web 集成** | `with-actix-web` feature | `actix-web` feature | 手动渲染后返回 | 原生支持 |
| **学习曲线** | 低（熟悉 Jinja） | 中（需适应宏语法） | 低 | 低 |

> [来源: [maud docs.rs](https://docs.rs/maud/latest/maud/)] · [tera docs.rs](https://docs.rs/tera/latest/tera/)]

**关键差异**：

- **Askama vs Maud**：Askama 使用 Jinja 模板文件，适合设计师与开发者协作；Maud 使用 Rust 宏内联 HTML，适合纯 Rust 团队，模板与逻辑共用类型系统（Type System）。
- **Askama vs Tera**：Tera 是运行时解析的动态模板引擎，上下文是 `HashMap<String, Value>`，更灵活但失去编译期检查；Askama 牺牲部分灵活性换取类型安全与性能。
- **Askama vs 原生返回**：在 Axum/Actix-web 中直接返回 `String`/`Json` 最简单，但无法利用模板继承和 HTML 专用语法；Askama 在保持类型安全的同时提供完整模板能力。

---

## 4. 反例边界 {#4-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 模板文件路径错误 | 编译错误：无法找到模板文件 | 确保 `templates/<name>.html` 存在，或使用 `source` 内联 |
| 模板中引用未定义字段 | 编译错误：未找到字段 | 在 struct 中定义所有模板使用的字段 |
| 字段类型与过滤器不匹配 | 编译错误：类型不满足过滤器要求 | 使用 `|safe` / `|escape` 等过滤器前确认类型 |
| 在循环中使用错误变量名 | 编译错误 | 与 `{% for item in items %}` 中声明的变量名一致 |
| 忽略 HTML 转义导致 XSS | 安全漏洞 | 默认使用 `|escape`，仅对可信内容使用`|safe` |
| 模板热重载困难 | 开发体验差 | 使用 `askama` 的 `reload` feature 或在 dev 环境使用动态引擎 |

> [来源: [askama 模板语法 - 过滤器](https://askama.readthedocs.io/en/stable/template_syntax.html#filters)]

---

## 5. 代码示例锚点 {#5-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| Askama 模板渲染 | [`crates/c06_async/examples/askama_template_rendering.rs`](../../../../crates/c06_async/examples/askama_template_rendering.rs) | `#[derive(Template)]`、内联模板、循环渲染 |

> [来源: [c06_async Crate](../../../../../crates/c06_async)]

---

## 6. 相关概念 {#6-相关概念}

- [00_crate_architecture_master_index.md](00_crate_architecture_master_index.md) — Rust 工业级 Crate 架构总索引
- [39_salvo_architecture.md](39_salvo_architecture.md) — Salvo Web 框架架构
- [40_ntex_architecture.md](40_ntex_architecture.md) — ntex Web 框架架构
- [42_maud_architecture.md](42_maud_architecture.md) — Maud 模板宏架构
- [07_axum_architecture.md](07_axum_architecture.md) — Axum Web 框架架构
- [12_actix_web_architecture.md](12_actix_web_architecture.md) — Actix-web 框架架构
- [concept L6: Web 框架与中间件](../../../../06_ecosystem)

---

> **权威来源**: [askama docs.rs](https://docs.rs/askama/latest/askama/index.html#integrations) · [askama crates.io](https://crates.io/crates/askama) · [askama book](https://djc.github.io/askama/) · [askama GitHub](https://github.com/djc/askama)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-06-29
> **状态**: ✅ 已完成

---

## 权威来源参考 {#权威来源参考}

### P0 — 核心官方文档 {#p0-核心官方文档}

> - [来源: [askama docs.rs](https://docs.rs/askama/latest/askama/index.html#integrations)]
> - [来源: [askama book](https://djc.github.io/askama/)]
> - [来源: [askama crates.io](https://crates.io/crates/askama)]

### P1 — 标准与生态文档 {#p1-标准与生态文档}

> - [来源: [Jinja Documentation](https://jinja.palletsprojects.com/)]
> - [来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]
> - [来源: [OWASP XSS Prevention](https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html)]

### P2 — 仓库与社区文章 {#p2-仓库与社区文章}

> - [来源: [askama GitHub Repository](https://github.com/djc/askama)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]
> - [[Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->](https://rustcc.cn/)

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneasverif.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
