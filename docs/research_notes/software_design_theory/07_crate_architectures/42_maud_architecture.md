> **Canonical 说明**: 本文件专注 **Maud 编译期 HTML DSL 宏（Macro）与 Render trait 架构**。
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
> **概念族**: Crate 架构 / maud
>
> **层级**: L3-L5

---

# Maud Crate 架构解构 {#maud-crate-架构解构}

> **EN**: Maud Architecture
> **Summary**: Maud Crate 架构解构 Maud Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5
>
> **知识领域**: 模板引擎、HTML DSL、过程宏（Procedural Macro）、编译期代码生成、Web 框架集成
>
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 1. 引言：Maud 在 Rust 模板生态中的定位 {#1-引言maud-在-rust-模板生态中的定位}

> **[来源: [maud crates.io](https://crates.io/crates/maud)]**

`Maud` 是 Rust 生态中独特的**编译期 HTML 模板宏**。与其他模板引擎不同，它不解析外部模板文件，而是提供一个 `html!` 过程宏（Procedural Macro），让开发者直接在 Rust 代码中编写类型安全的 HTML。

> [来源: [maud docs.rs](https://docs.rs/maud/latest/maud/)]

Maud 的核心设计取舍：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **DSL 形态** | Rust 过程宏 `html! { ... }` | 模板即 Rust 代码，共享类型与作用域 |
| **渲染时机** | 编译期展开为 `fmt::Write` 调用 | 运行时（Runtime）零解析、零分配临时 AST |
| **类型安全** | 模板中直接嵌入 Rust 表达式 | 字段/类型错误在编译期捕获 |
| **HTML 语义** | 宏语法强制标签配对与属性结构 | 减少手写 HTML 时的结构错误 |
| **框架集成** | axum / actix-web / rocket / warp feature | 可直接作为响应体 |

> [来源: [maud GitHub Repository](https://github.com/lambda-fairy/maud)]

```rust,ignore
use maud::html;

fn main() {
    let name = "Maud";
    let markup = html! {
        h1 { "Hello, " (name) "!" }
    };
    println!("{}", markup.into_string());
}
```

> [来源: [maud book](https://maud.lambda.xyz/)]

---

## 2. 核心 API 架构 {#2-核心-api-架构}

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 `html!` 过程宏 {#21-html-过程宏}

`html!` 是 Maud 的唯一核心入口。它将花括号内的 DSL 在编译期转换为 `Markup` 值：

```rust,ignore
use maud::{html, Markup};

fn page(title: &str, items: &[&str]) -> Markup {
    html! {
        html {
            head { title { (title) } }
            body {
                h1 { "Items" }
                ul {
                    @for item in items {
                        li { (item) }
                    }
                }
            }
        }
    }
}
```

> [来源: [maud::html macro](https://docs.rs/maud/latest/maud/macro.html.html)]

DSL 规则：

- 字面量字符串直接输出并自动转义。
- `(expression)` 嵌入 Rust 表达式，结果需实现 `Render` trait。
- `@for`、`@if`、`@match` 提供控制流。
- 属性使用 `key="value"` 或 `key=(expr)` 形式。

### 2.2 `Markup` 与 `Render` trait {#22-markup-与-render-trait}

`html!` 返回 `Markup` 类型，可通过 `into_string()` 转为 `String`，也可直接作为 HTTP 响应：

```rust,ignore
use maud::{html, Markup, Render};

struct User { name: String }
impl Render for User {
    fn render_to(&self, buffer: &mut String) {
        html! { span.user { (self.name) } }.render_to(buffer);
    }
}
```

> [来源: [maud::Render trait](https://docs.rs/maud/latest/maud/trait.Render.html)]

`Render` trait 允许自定义类型直接参与模板拼接，实现类型级别的组件化。

### 2.3 渲染流程 {#23-渲染流程}

```mermaid
graph LR
    MACRO[html! macro] --> EXPAND[编译期过程宏展开]
    RUST[Rust 表达式/变量] --> EXPAND
    EXPAND --> MARKUP[Markup 值]
    MARKUP --> STRING[into_string()]
    MARKUP --> RESPONSE[IntoResponse]
```

由于宏在编译期完成所有工作，运行期只有字符串写入操作，无 AST 遍历或模板缓存。

### 2.4 Web 框架集成 {#24-web-框架集成}

启用对应 feature 后，`Markup` 可直接作为响应：

```toml
maud = { version = "0.27.0", features = ["axum"] }
```

```rust,ignore
use axum::{routing::get, Router};
use maud::html;

async fn hello() -> impl axum::response::IntoResponse {
    html! { h1 { "Hello from Maud + Axum" } }
}
```

> [来源: [maud framework support](https://maud.lambda.xyz/)]

---

## 3. 与 axum / actix-web 及同类模板引擎对比 {#3-与-axum-actix-web-及同类模板引擎对比}

> **[来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]**

| 维度 | Maud | Askama | Tera | Axum/Actix-web 原生 |
|:--|:--|:--|:--|:--|
| **语法风格** | Rust DSL (`html!` 宏) | Jinja-like | Jinja-like | 无 |
| **渲染时机** | 编译期 | 编译期 | 运行时（Runtime） | 运行时 |
| **模板位置** | 内联 Rust | 外部 `.html` 文件 | 外部 `.html` 文件 | 不适用 |
| **类型安全** | 极强（Rust 表达式） | 强（字段绑定） | 弱 | 强 |
| **与 axum 集成** | `axum` feature | `with-axum` feature | 手动 | 原生 |
| **与 actix-web 集成** | `actix-web` feature | `with-actix-web` feature | 手动 | 原生 |
| **协作设计** | 纯 Rust 团队友好 | 设计师可编辑模板 | 设计师可编辑模板 | 不适用 |

> [来源: [askama docs.rs](https://docs.rs/askama/latest/askama/)] · [tera docs.rs](https://docs.rs/tera/latest/tera/)]

**关键差异**：

- **Maud vs Askama**：Maud 将 HTML 完全融入 Rust 语法，没有模板文件，重构和类型检查体验最好；Askama 保留 Jinja 文件，更适合需要设计师参与的项目。
- **Maud vs Tera**：Tera 是运行时引擎，支持模板热加载和动态上下文；Maud 是编译期引擎，性能更高但模板必须在编译时确定。
- **Maud vs 原生返回**：相比直接返回 `String`，Maud 提供结构化 HTML DSL、自动转义和组件复用，同时不牺牲类型安全。

---

## 4. 反例边界 {#4-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 标签未闭合 | 宏编译错误 | 保证每个 `{` 有对应的 `}` |
| 在 DSL 中写裸 Rust 语法 | 宏解析错误 | 使用 `@let`、`@if`、`@for` 等 DSL 控制流 |
| 忘记转义用户输入 | XSS 安全漏洞 | Maud 默认转义，仅在可信内容上使用 `PreEscaped` |
| 表达式返回非 `Render` 类型 | 编译错误 | 为自定义类型实现 `Render`，或返回字符串 |
| 在宏中捕获过长生命周期（Lifetimes） | 编译错误 | 确保借用（Borrowing）数据在 `Markup` 使用前有效 |
| 试图运行时动态选择模板 | 不可行 | Maud 模板在编译期固定，动态场景改用 Askama/Tera |

> [来源: [maud syntax reference](https://maud.lambda.xyz/)]

---

## 5. 代码示例锚点 {#5-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| Maud 模板渲染 | [`crates/c06_async/examples/maud_template_rendering.rs`](../../../../crates/c06_async/examples/maud_template_rendering.rs) | `html!` 宏、循环、函数组件 |

> [来源: [c06_async Crate](../../../../../crates/c06_async)]

---

## 6. 相关概念 {#6-相关概念}

- [00_crate_architecture_master_index.md](00_crate_architecture_master_index.md) — Rust 工业级 Crate 架构总索引
- [39_salvo_architecture.md](39_salvo_architecture.md) — Salvo Web 框架架构
- [40_ntex_architecture.md](40_ntex_architecture.md) — ntex Web 框架架构
- [41_askama_architecture.md](41_askama_architecture.md) — Askama 模板引擎架构
- [07_axum_architecture.md](07_axum_architecture.md) — Axum Web 框架架构
- [12_actix_web_architecture.md](12_actix_web_architecture.md) — Actix-web 框架架构
- [concept L6: Web 框架与中间件](../../../../06_ecosystem)

---

> **权威来源**: [maud docs.rs](https://docs.rs/maud/latest/maud/) · [maud crates.io](https://crates.io/crates/maud) · [maud book](https://maud.lambda.xyz/) · [maud GitHub](https://github.com/lambda-fairy/maud)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-06-29
> **状态**: ✅ 已完成

---

## 权威来源参考 {#权威来源参考}

### P0 — 核心官方文档 {#p0-核心官方文档}

> - [来源: [maud docs.rs](https://docs.rs/maud/latest/maud/)]
> - [来源: [maud book](https://maud.lambda.xyz/)]
> - [来源: [maud crates.io](https://crates.io/crates/maud)]

### P1 — 标准与生态文档 {#p1-标准与生态文档}

> - [来源: [Rust Reference - Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)]
> - [来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]
> - [来源: [OWASP XSS Prevention](https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html)]

### P2 — 仓库与社区文章 {#p2-仓库与社区文章}

> - [来源: [maud GitHub Repository](https://github.com/lambda-fairy/maud)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]
> - [[Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->](https://rustcc.cn/)

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneasverif.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
