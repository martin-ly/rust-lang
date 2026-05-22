# DSL [来源: [DSL Wikipedia](https://en.wikipedia.org/wiki/Domain-specific_language)] 与嵌入 [来源: [Rust Embedded Book](https://docs.rust-embedded.org/book/)]式设计：Rust 中的领域特定语言

> **Bloom 层级**: 应用 → 分析
> **定位**: 分析 Rust 中 **DSL（领域特定语言）**的构建方法——从宏驱动的内嵌 DSL（如 html!、sql!）、到外部 DSL 的解析器 [来源: [Parsing in Rust](https://rust-lang.github.io/rustc-dev-guide/grammar.html)]组合子（parser combinators），再到 Rust 作为宿主语言的嵌入策略，揭示类型安全 DSL 的设计模式。
> **前置概念**: [Macros](../03_advanced/04_macro [来源: [Rust Macros](https://doc.rust-lang.org/reference/macros.html)]s.md) · [Proc Macro](../03_advanced/07_proc_macro [来源: [Rust Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)].md) · [Trait](./01_traits.md)
> **后置概念**: [Serde Patterns](./09_serde_patterns.md) · [WebAssembly](../06_ecosystem/11_webassembly.md)

---

> **来源**: [TRPL — Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) · [nom Parser Combinators](https://docs.rs/nom/latest/nom/) · [serde DSL Design](https://serde.rs/) · [Rust API Guidelines — DSLs](https://rust-lang.github.io/api-guidelines/predictability.html) · [Wikipedia — Domain-specific language](https://en.wikipedia.org/wiki/Domain-specific_language)

## 📑 目录
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [DSL \[来源: DSL Wikipedia\] 与嵌入 \[来源: Rust Embedded Book\]式设计：Rust 中的领域特定语言](#dsl-来源-dsl-wikipedia-与嵌入-来源-rust-embedded-book式设计rust-中的领域特定语言)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 内嵌 DSL vs 外部 DSL](#11-内嵌-dsl-vs-外部-dsl)
    - [1.2 宏驱动的内嵌 DSL](#12-宏驱动的内嵌-dsl)
    - [1.3 Builder 模式作为 DSL](#13-builder-模式作为-dsl)
  - [二、技术细节](#二技术细节)
    - [2.1 Parser Combinators](#21-parser-combinators)
    - [2.2 类型安全的 DSL](#22-类型安全的-dsl)
    - [2.3 编译期验证的 DSL](#23-编译期验证的-dsl)
  - [三、设计模式矩阵](#三设计模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 内嵌 DSL vs 外部 DSL

```text
DSL 的两种形态:

  内嵌 DSL（Embedded DSL）:
  ├── 宿主语言（Rust）的语法子集
  ├── 利用 Rust 的类型系统和工具链
  ├── 运行时性能接近手写代码
  └── 示例: html! 宏、format! 宏

  外部 DSL（External DSL）:
  ├── 独立的语法和语义
  ├── 需要解析器（parser）和编译器/解释器
  ├── 更灵活的语法设计
  └── 示例: SQL、正则表达式、配置文件格式

  Rust 中的 DSL 实现方式:
  ┌─────────────────┬─────────────────┬─────────────────┐
  │ 方式            │ 类型            │ 示例            │
  ├─────────────────┼─────────────────┼─────────────────┤
  │ 宏              │ 内嵌            │ html!, sql!     │
  │ Builder 模式    │ 内嵌            │ Request::new()  │
  │ Parser Combinator│ 外部           │ nom, pest       │
  │ 过程宏          │ 内嵌            │ serde, derive   │
  │ 嵌入解释器      │ 外部            │ Lua/Rhai 嵌入   │
  └─────────────────┴─────────────────┴─────────────────┘
```

> **认知功能**: DSL 的**核心权衡**是**表达能力 vs 工具链支持**——内嵌 DSL 免费获得 Rust 的类型检查和 IDE 支持，外部 DSL 需要自建工具链。
> [来源: [Fowler — Domain-Specific Languages](https://martinfowler.com/books/dsl.html)]

---

### 1.2 宏驱动的内嵌 DSL

```rust,ignore
// 示例 1: HTML DSL（类似 yew/html!）
let doc = html! {
    <div class="container">
        <h1>{"Hello, DSL!"}</h1>
        <ul>
            {items.iter().map(|item| html! {
                <li>{item}</li>
            })}
        </ul>
    </div>
};

// 示例 2: SQL DSL（概念示例）
let query = sql! {
    SELECT id, name FROM users
    WHERE age > {min_age} AND active = true
};

// 示例 3: 路由 DSL（类似 axum）
let app = Router::new()
    .route("/", get(home))
    .route("/users", post(create_user))
    .layer(TraceLayer::new_for_http());

// 宏 DSL 的优势:
// - 编译期语法检查
// - 编译期优化（如 SQL 预编译）
// - IDE 支持（如果宏生成良好）
```

> **宏 DSL 洞察**: Rust 的**过程宏**使 DSL 可以在编译期进行**任意复杂的验证和转换**——这是其他语言难以实现的能力。
> [来源: [yew — html! macro](https://yew.rs/docs/concepts/html)]

---

### 1.3 Builder 模式作为 DSL

```rust,ignore
// 类型安全的 Builder DSL

// 未完成的 Request（缺少 method 和 uri）
let builder = Request::builder();

// 链式调用构建
let request = Request::builder()
    .method(Method::POST)
    .uri("https://api.example.com/users")
    .header("content-type", "application/json")
    .body(json_body)?;

// 类型状态模式（Typestate）
struct RequestBuilder<State> {
    method: Option<Method>,
    uri: Option<Uri>,
    _state: PhantomData<State>,
}

struct Incomplete;
struct Ready;

impl RequestBuilder<Incomplete> {
    fn method(self, m: Method) -> RequestBuilder<Incomplete> { ... }
    fn uri(self, u: Uri) -> RequestBuilder<Ready> { ... }
}

impl RequestBuilder<Ready> {
    fn body(self, b: Body) -> Result<Request> { ... }
}

// RequestBuilder<Incomplete> 不能调用 body()
// 编译器在类型层面强制执行构建顺序
```

> **Builder DSL 洞察**: **Typestate 模式**将运行时检查转化为编译期类型检查——这是 Rust 类型系统的强大应用。
> [来源: [Rust API Guidelines — Builders](https://rust-lang.github.io/api-guidelines/type-safety.html#builders-enable-construction-of-complex-values-c-builder)]

---

## 二、技术细节
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 Parser Combinators

```rust,ignore
// 使用 nom 解析外部 DSL

use nom::{
    IResult,
    sequence::tuple,
    character::complete::{char, digit1},
    combinator::map,
};

// 解析简单表达式: "1 + 2"
fn expression(input: &str) -> IResult<&str, Expr> {
    map(
        tuple((digit1, char(' '), char('+'), char(' '), digit1)),
        |(left, _, _, _, right)| Expr::Add(
            left.parse().unwrap(),
            right.parse().unwrap(),
        ),
    )(input)
}

// Parser Combinator 的优势:
// - 组合子（combinator）是类型安全的构建块
// - 无需外部工具（如 yacc/lex）
// - 错误处理与 Rust 的 Result 集成
// - 可增量解析（streaming）

// 与其他解析方式的对比:
// ┌──────────────┬─────────────┬─────────────┬─────────────┐
// │ 方式         │ 类型安全    │ 性能        │ 错误信息    │
// ├──────────────┼─────────────┼─────────────┼─────────────┤
// │ nom          │ 是          │ 高          │ 良好        │
// │ pest (PEG)   │ 是          │ 高          │ 良好        │
// │ hand-written │ 是          │ 最高        │ 自定义      │
// │ lalrpop      │ 是          │ 高          │ 良好        │
// └──────────────┴─────────────┴─────────────┴─────────────┘
```

> **Parser Combinator 洞察**: nom 等库将**解析器作为一等值**——解析器可以组合、映射、选择，与函数式编程的抽象能力结合。
> [来源: [nom Documentation](https://docs.rs/nom/latest/nom/)]

---

### 2.2 类型安全的 DSL

```rust,ignore
// 使用 Rust 类型系统保证 DSL 安全

// 安全的 SQL 参数化（防止 SQL 注入）
struct Query<'a> {
    sql: &'a str,
    params: Vec<Param>,
}

enum Param {
    Int(i64),
    Text(String),
    Bool(bool),
}

// 只能通过安全的 API 构造 Query
impl<'a> Query<'a> {
    fn new(sql: &'a str) -> Self { ... }

    fn bind_int(mut self, val: i64) -> Self {
        self.params.push(Param::Int(val));
        self
    }

    fn bind_text(mut self, val: &str) -> Self {
        self.params.push(Param::Text(val.to_string()));
        self
    }
}

// 使用
let query = Query::new("SELECT * FROM users WHERE id = ?")
    .bind_int(42);

// 编译器保证:
// - 参数数量与占位符匹配（运行时检查）
// - 参数类型与列类型兼容（数据库检查）
// - 无字符串拼接导致的注入风险
```

> **类型安全洞察**: Rust 的**强类型系统**使 DSL 可以在编译期排除大量错误——从 SQL 注入到格式字符串漏洞。
> [source: [Rust API Guidelines — Type Safety](https://rust-lang.github.io/api-guidelines/type-safety.html)]

---

### 2.3 编译期验证的 DSL

```rust,ignore
// 编译期验证的格式字符串（类似 println!）

// Rust 的 format! 宏在编译期解析格式字符串
let s = format!("Hello, {}! You have {} messages.", name, count);
// 编译器检查:
// - 占位符数量与参数匹配
// - 参数类型实现 Display trait
// - 编译错误而非运行时 panic

// 自定义编译期验证 DSL
#[derive(Debug)]
struct Email(String);

impl Email {
    // 编译期无法验证邮箱格式
    // 但可以在构造时验证
    fn new(s: &str) -> Result<Self, EmailError> {
        if s.contains('@') {
            Ok(Email(s.to_string()))
        } else {
            Err(EmailError::Invalid)
        }
    }
}

// 更高级的编译期验证（使用 const fn 或宏）
const fn validate_email_prefix(s: &str) -> bool {
    // const fn 中的验证在编译期执行
    // 但能力有限（无法分配内存、无法使用正则）
    // 复杂验证仍需运行时
}
```

> **编译期验证洞察**: Rust 的**宏 + const fn** 提供了有限的编译期计算能力——对于复杂验证，通常采用"**解析，不验证**"（parse, don't validate）策略，使用强类型替代运行时检查。
> [source: [Parse Don't Validate](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/)]

---

## 三、设计模式矩阵
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
场景 → DSL 类型 → 实现方式 → 关键 crate

HTML/XML 生成:
  → 内嵌 DSL
  → 过程宏
  → yew, maud, markup

SQL 查询:
  → 内嵌 DSL
  → Builder 或宏
  → sqlx, sea-query

配置解析:
  → 外部 DSL
  → Parser Combinator
  → serde, toml, nom

路由定义:
  → 内嵌 DSL
  → Builder 或宏
  → axum, actix-web

序列化格式:
  → 内嵌 DSL（derive）
  → 过程宏
  → serde

测试断言:
  → 内嵌 DSL
  → 宏
  → pretty_assertions, insta

状态机:
  → 内嵌 DSL
  → Typestate
  → 手动实现或 state_machine_future
```

> **模式矩阵**: Rust 的 DSL 生态充分利用了**宏系统 [来源: [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros-by-example.html)]**和**类型系统**——两者结合使 DSL 既表达力强又类型安全。
> [source: [Awesome Rust — DSL](https://github.com/rust-unofficial/awesome-rust)]

---

## 四、反命题与边界分析
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: 所有配置都应使用 Rust DSL"]
    ROOT --> Q1{"是否需要非程序员编辑?"}
    Q1 -->|是| EXTERNAL["❌ 使用 JSON/YAML/TOML 等通用格式"]
    Q1 -->|否| Q2{"是否需要编译期验证?"}
    Q2 -->|是| DSL["✅ Rust DSL 最优"]
    Q2 -->|否| SIMPLE["✅ 简单结构体即可"]

    style EXTERNAL fill:#fff3e0
    style DSL fill:#c8e6c9
    style SIMPLE fill:#c8e6c9
```

> **认知功能**: 此决策树展示 DSL 的**适用边界**。核心原则是：**需要编译期验证时用 Rust DSL，需要通用可编辑性时用标准格式**。
> [来源: [TRPL](https://doc.rust-lang.org/book/)]
> [source: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]

---

### 4.2 边界极限

```text
边界 1: 宏的编译时间
├── 复杂宏 DSL 增加编译时间
├── syn [来源: [syn crate](https://docs.rs/syn/latest/syn/)] 解析是 CPU 密集型
├── 每个使用宏的 crate 都需要重新解析
└── 缓解: 优化宏实现、使用 proc-macro2

边界 2: 错误信息质量
├── 宏生成的代码错误指向生成位置
├── 用户难以理解宏内部的错误
├── 需要 careful 的 Span 设置
└── 缓解: 使用 syn::Error、提供有意义的错误信息

边界 3: IDE 支持
├── 宏 DSL 在 IDE 中可能无法正确补全/跳转
├── rust-analyzer 支持有限
├── 复杂的嵌套宏更难分析
└── 缓解: 生成辅助的 trait impl、使用 rust-analyzer 的 expand macro

边界 4: 语法限制
├── 内嵌 DSL 受 Rust 语法约束
├── 不能自由设计语法（如中缀运算符）
├── 某些 DSL 更适合外部实现
└── 缓解: 使用 postfix 宏、接受语法限制

边界 5: 学习曲线
├── 自定义 DSL 需要学习新的"子语言"
├── 团队内的 DSL 增加认知负担
├── 与标准 Rust 的交互可能不直观
└── 缓解: 遵循 Rust 惯例、提供良好文档
```

> **边界要点**: DSL 的边界主要与**编译时间**、**错误信息**、**IDE 支持**、**语法限制**和**学习曲线**相关。
> [source: [Rust Proc Macro Workshop](https://github.com/dtolnay/proc-macro-workshop)]

---

## 五、常见陷阱
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

```text
陷阱 1: 过度工程化 DSL
  ❌ 为简单配置创建复杂的宏 DSL
     // 维护成本高，收益低

  ✅ 简单的 Builder 或结构体足够时不要用宏

陷阱 2: 忽略错误信息
  ❌ 宏失败时产生晦涩的编译错误
     // 用户体验差

  ✅ 使用 syn::Error 在精确位置报告错误
     // 提供清晰的错误消息和修复建议

陷阱 3: DSL 与 Rust 语法冲突
  ❌ html! { <div class="main"> } 中 class 是 Rust 关键字
     // 需要 workaround

  ✅ 使用 r#class 或避免关键字作为标识符
     // 或接受语法限制

陷阱 4: 运行时性能假设
  ❌ 假设宏 DSL 生成的代码总是最优
     // 宏只保证语法正确，不保证性能

  ✅ 测量生成的代码性能
     // 使用 cargo asm 检查

陷阱 5: 版本兼容性
  ❌ DSL 的 breaking change 影响所有用户
     // 没有类型系统的保护

  ✅ 使用语义化版本控制
     // 提供迁移指南
```

> **陷阱总结**: DSL 的陷阱主要与**过度工程**、**错误信息**、**语法冲突**、**性能假设**和**版本兼容**相关。
> [source: [Rust Macro Best Practices](https://doc.rust-lang.org/reference/macros.html)]

---

## 六、来源与延伸阅读
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | ✅ 一级 | 标准库参考 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | ✅ 一级 | 交互式教程 |
| [This Week in Rust](https://this-week-in-rust.org/) | ✅ 二级 | 社区动态 |

| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 语言参考 |
|:---|:---:|:---|
| [TRPL — Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) | ✅ 一级 | 宏系统入门 |
| [nom Parser Combinators](https://docs.rs/nom/latest/nom/) | ✅ 一级 | 解析器组合子 |
| [serde](https://serde.rs/) | ✅ 一级 | 序列化 DSL |
| [Fowler — DSLs](https://martinfowler.com/books/dsl.html) | ✅ 二级 | DSL 设计经典 |
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | ✅ 一级 | API 设计指南 |

---

## 相关概念文件
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Macros](../03_advanced/04_macros.md) — 声明式宏
- [Proc Macro](../03_advanced/07_proc_macro.md) — 过程宏
- [Trait](./01_traits.md) — Trait 系统
- [Serde Patterns](./09_serde_patterns.md) — Serde 序列化

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成
