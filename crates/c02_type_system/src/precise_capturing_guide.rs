//! `use<..>` Precise Capturing 深度指南
//!
//! > **Rust 版本**: 2024 Edition (部分稳定)  
//! > **RFC**: [RFC 3617 - Precise Capturing](https://rust-lang.github.io/rfcs/3617-precise-capturing.html)  
//! > **最后更新**: 2026-05-08
//!
//! # 概念定义
//!
//! `use<..>` 是 Rust 2024 Edition 引入的语法，用于**精确控制 `impl Trait`
//! 返回类型中捕获的生命周期和类型参数**。
//!
//! ## 问题背景
//!
//! 在 Rust 2021 Edition 中，`impl Trait` 返回类型会自动捕获所有输入生命周期：
//!
//! ```rust,ignore
//! // 2021 Edition: 自动捕获所有生命周期
//! fn get_str(s: &str) -> impl Iterator<Item = &str> {
//!     s.split(',')
//! }
//! // 返回的 Iterator 捕获了 s 的生命周期，这是正确的
//! ```
//!
//! 但有时这种自动捕获**过于宽泛**，导致不必要的约束：
//!
//! ```rust,ignore
//! // 问题：返回的 Future 自动捕获了 'a
//! fn process<'a>(data: &'a str) -> impl Future<Output = String> + 'a {
//!     async move {
//!         // 实际上不使用 data，但 Future 仍被约束为 'a
//!         "result".to_string()
//!     }
//! }
//! ```
//!
//! ## 解决方案：`use<..>`
//!
//! `use<T, 'a>` 语法允许你**显式声明** `impl Trait` 捕获哪些类型参数和生命周期：
//!
//! ```rust,edition2024
//! // 2024 Edition: 精确捕获
//! fn process<'a>(data: &'a str) -> impl Future<Output = String> + use<> {
//!     async move {
//!         // use<> 表示不捕获任何外部生命周期
//!         "result".to_string()
//!     }
//! }
//! ```

/// # 语法详解
///
/// ## 基本形式
///
/// ```ignore
/// impl Trait + use<'a, T>
/// //              ^^^^^^^^^
/// //              只捕获 'a 和 T
/// ```
///
/// ## 常见模式
///
/// | 模式 | 含义 | 场景 |
/// |------|------|------|
/// | `use<>` | 不捕获任何参数 | 返回类型完全独立 |
/// | `use<'a>` | 只捕获生命周期 'a | 返回类型依赖特定引用 |
/// | `use<T>` | 只捕获类型参数 T | 泛型函数，返回与 T 相关 |
/// | `use<'a, T>` | 捕获 'a 和 T | 同时依赖生命周期和类型 |
///
/// # 与 2021 Edition 的对比
///
/// ```mermaid
/// graph LR
///     E21["2021 Edition<br/>自动捕获所有"] -->|过于宽泛| P1["不必要的生命周期约束"]
///     E21 -->|隐藏细节| P2["难以推断实际依赖"]
///     E24["2024 Edition<br/>use&lt;..&gt; 精确捕获"] -->|显式控制| S1["更灵活的 API 设计"]
///     E24 -->|自文档化| S2["代码意图更清晰"]
/// ```
pub struct PreciseCapturingGuide;

impl PreciseCapturingGuide {
    /// ## 示例 1：排除不必要的生命周期捕获
    ///
    /// 在 2021 Edition 中，异步函数自动捕获所有输入生命周期。
    /// 使用 `use<>` 可以创建一个 'static Future：
    pub fn static_future_example() -> &'static str {
        r#"
// 2024 Edition
fn spawn_independent_task() -> impl Future<Output = i32> + use<> + Send {
    async move {
        // 这个 Future 是 'static 的，因为它 use<> 不捕获任何生命周期
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }
}

// 使用：可以直接 spawn，因为 Future 是 'static
let handle = tokio::spawn(spawn_independent_task());
"#
    }

    /// ## 示例 2：选择性捕获特定生命周期
    ///
    /// 只捕获需要的生命周期，排除其他：
    pub fn selective_capture_example() -> &'static str {
        r#"
// 只捕获 'data 生命周期，不捕获 'config
fn process<'data, 'config>(
    data: &'data str,
    _config: &'config Config,
) -> impl Iterator<Item = &'data str> + use<'data> {
    // 返回的 Iterator 只与 'data 绑定
    // 'config 不会被捕获，因此 config 可以在 Iterator 使用前被释放
    data.split_whitespace()
}
"#
    }

    /// ## 示例 3：在 Trait 中使用
    ///
    /// `use<..>` 在 trait 定义和实现中同样有效：
    pub fn trait_example() -> &'static str {
        r#"
trait Parser {
    fn parse<'a>(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a>;
}

struct CommaParser;

impl Parser for CommaParser {
    fn parse<'a>(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a> {
        input.split(',')
    }
}
"#
    }

    /// ## 示例 4：迁移策略
    ///
    /// 从 2021 Edition 迁移到 2024 Edition 时：
    pub fn migration_guide() -> &'static str {
        r#"
// 2021 Edition（旧代码）
fn old_style<'a>(s: &'a str) -> impl Iterator<Item = &'a str> + 'a {
    s.split(',')
}

// 2024 Edition（等价的精确捕获）
fn new_style<'a>(s: &'a str) -> impl Iterator<Item = &'a str> + use<'a> {
    s.split(',')
}

// 2024 Edition（优化：如果不需要捕获）
fn optimized() -> impl Iterator<Item = String> + use<> {
    ["a", "b", "c"].iter().map(|s| s.to_string())
}
"#
    }

    /// ## 反例 / 常见错误
    pub fn common_mistakes() -> &'static str {
        r#"
// ❌ 错误：use<> 但返回类型实际依赖外部生命周期
fn bad<'a>(s: &'a str) -> impl Iterator<Item = &'a str> + use<> {
    s.split(',')
    // 编译错误：返回类型需要 'a，但 use<> 排除了它
}

// ✅ 正确：显式捕获需要的生命周期
fn good<'a>(s: &'a str) -> impl Iterator<Item = &'a str> + use<'a> {
    s.split(',')
}
"#
    }
}

/// # 决策树：何时使用 use<..>
///
/// ```text
/// 使用 2024 Edition 的 impl Trait?
/// ├── 返回类型完全不依赖输入参数？ → use<>
/// ├── 只依赖特定生命周期？ → use<'a>
/// ├── 依赖多个生命周期？ → use<'a, 'b>
/// ├── 依赖类型参数？ → use<T>
/// └── 不确定？ → 省略 use<..>，使用默认捕获（与 2021 Edition 行为一致）
/// ```
pub struct PreciseCapturingDecisionTree;

impl PreciseCapturingDecisionTree {
    pub fn explain() -> &'static str {
        r#"
use<..> Precise Capturing 决策树:

1. 返回值是否包含引用？
   ├── 否 → use<> (返回 'static 类型)
   └── 是 → 继续 2

2. 引用来自哪个参数？
   ├── 来自参数 A → use<'lifetime_of_A>
   ├── 来自参数 B → use<'lifetime_of_B>
   └── 来自多个 → use<'a, 'b, ...>

3. 是否涉及泛型类型参数？
   ├── 是 → 在 use<> 中包含类型参数
   └── 否 → 只包含生命周期

4. 是否需要 Send/Sync bound？
   ├── 是 → impl Trait + use<..> + Send
   └── 否 → impl Trait + use<..>
"#
    }
}
