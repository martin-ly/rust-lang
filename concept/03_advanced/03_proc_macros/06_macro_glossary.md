> **EN**: Macro Glossary
> **Summary**: Authoritative concept page for `术语表 - C11 Macro System`. Content migrated from `crates/c11_macro_system_proc/docs/tier_01_foundations/03_glossary.md`.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [参考级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: S×Mem — 宏（Macro）术语结构化索引
> **前置依赖**: [过程宏（Procedural Macro）](02_proc_macro.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md)
> **后置概念**: [宏（Macro）卫生性](09_macro_hygiene.md) · [syn/quote 参考](08_syn_quote_reference.md)
> **定理链**: Terminology Standardization ⟹ Concept Alignment ⟹ Communication Efficiency
>
> **权威来源**: 本页为 `Macro Glossary` 的权威概念页；crate 文档仅保留导航 stub。

# 术语表 - C11 Macro System

**最后更新**: 2025-12-11

本文档汇总了 Rust 宏系统中的核心术语和概念。

---

## 📋 目录

- [术语表 - C11 Macro System](#术语表---c11-macro-system)
  - [📋 目录](#-目录)
  - [🎨 宏类型术语](#-宏类型术语)
    - [Macro (宏)](#macro-宏)
    - [Declarative Macro (声明宏)](#declarative-macro-声明宏)
    - [Procedural Macro (过程宏)](#procedural-macro-过程宏)
  - [🔧 声明宏术语](#-声明宏术语)
    - [macro\_rules](#macro_rules)
    - [Pattern Matching (模式匹配)](#pattern-matching-模式匹配)
    - [Repetition (重复)](#repetition-重复)
    - [Metavariable (元变量)](#metavariable-元变量)
  - [⚙️ 过程宏术语](#️-过程宏术语)
    - [TokenStream](#tokenstream)
    - [Derive Macro (派生宏)](#derive-macro-派生宏)
    - [Attribute Macro (属性宏)](#attribute-macro-属性宏)
    - [Function-like Macro (函数式宏)](#function-like-macro-函数式宏)
    - [syn Crate](#syn-crate)
    - [quote Crate](#quote-crate)
    - [Span](#span)
  - [🧹 卫生性与作用域](#-卫生性与作用域)
    - [Hygiene (卫生性)](#hygiene-卫生性)
    - [Call Site (调用点)](#call-site-调用点)
    - [Definition Site (定义点)](#definition-site-定义点)
    - [Mixed Site (混合点)](#mixed-site-混合点)
  - [🛠️ 工具与库](#️-工具与库)
    - [cargo-expand](#cargo-expand)
    - [proc-macro2](#proc-macro2)
    - [trybuild](#trybuild)
  - [📚 元编程概念](#-元编程概念)
    - [Metaprogramming (元编程)](#metaprogramming-元编程)
    - [AST (抽象语法树)](#ast-抽象语法树)
    - [DSL (领域特定语言)](#dsl-领域特定语言)
    - [Code Generation (代码生成)](#code-generation-代码生成)
    - [Zero-Cost Abstraction (零成本抽象)](#zero-cost-abstraction-零成本抽象)
    - [Compile-time Computation (编译时计算)](#compile-time-computation-编译时计算)
  - [认知路径](#认知路径)
  - [定理链](#定理链)
  - [反命题](#反命题)
  - [反向推理](#反向推理)
  - [过渡段](#过渡段)
  - [国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp0-官方--p1-学术--p2-生态)

---

## 🎨 宏类型术语

本页是宏系统术语的权威速查表。宏类型三个核心术语的精确定义：

- **Macro（宏）**：编译期执行的「代码生成规则/程序」，输入语法结构、输出代码。Rust 宏的统一特征：在解析后展开、输出必须是合法 token 树、遵循卫生性规则。与「函数」的分界线是执行时机（编译期 vs 运行期），与「泛型」的分界线是「生成代码 vs 实例化代码」。
- **Declarative Macro（声明宏）**：`macro_rules!` 定义的宏——「声明」指其定义形式是「一组模式-转录规则的陈述」而非算法。别名「示例宏」（macro by example, MBE）更贴近其本质：每条规则是一个「输入示例 → 输出示例」的模板。能力边界：只能做语法结构变换，不能分析语义（看不到类型、看不到值）。
- **Procedural Macro（过程宏）**：以 Rust 函数（过程）实现的宏——「过程」指其定义是命令式算法。编译为编译器插件动态库，在展开阶段执行。三种注册形式（derive/attribute/function-like）决定「它能标注/出现在什么语法位置」，不决定能力（三者都操作完整 TokenStream）。

术语辨析速记：「声明 vs 过程」是**实现方式**之分（规则 vs 算法），「derive/attribute/function-like」是**注册形式**之分（语法位置），两组术语正交——所有 derive 宏都是过程宏，但过程宏不只有 derive。

### Macro (宏)

编译时执行的代码生成机制，在编译前展开为 Rust 代码。

**分类**:

- **声明宏** (Declarative Macros): `macro_rules!`
- **过程宏** (Procedural Macros): 自定义 derive、属性宏、函数式宏

**特点**:

- 编译时展开
- 零运行时（Runtime）开销
- 类型安全

---

### Declarative Macro (声明宏)

基于模式匹配（Pattern Matching）的 `macro_rules!` 代码生成宏。

```rust
macro_rules! vec_of_strings {
    ($($element:expr),*) => {
        vec![$(String::from($element)),*]
    };
}
```

**特点**:

- 语法简洁
- 模式匹配（Pattern Matching）
- 卫生性保证

---

### Procedural Macro (过程宏)

编译期操作 token 流（TokenStream）的 Rust 代码宏。

**三种类型**:

1. **Derive 宏**: `#[derive(MyTrait)]`
2. **属性宏**: `#[my_attribute]`
3. **函数式宏**: `my_macro!(input)`

```rust
#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    // 处理 TokenStream
}
```

---

## 🔧 声明宏术语

本节目录化 `macro_rules!` 体系的核心术语，每个术语给出「定义 + 判别例」：

- **Pattern Matching（模式匹配）**：宏臂左侧的匹配语言——`$name:fragment` 绑定片段，字面 token 精确匹配，臂按序尝试（先到先得）；
- **Repetition（重复）**：`$( ... ),*` 语法——`$()` 内可含多个变量（同长度迭代），分隔符与 `*`/`+`/`?` 量词的组合规则；
- **Metavariable（元变量）**：`$name:fragment_specifier`——12 种片段分类符（`expr`/`ty`/`ident`/`tt`/`pat`/`literal` 等）各有限定，选错是「宏匹配不上」的首要原因；
- **局部歧义（local ambiguity）**：`expr` 后只能跟 `=>`/`,`/`;`——片段边界的解析规则，复杂宏设计的第一约束。

术语表用法：查阅式使用——遇到宏错误先定位术语再读定义，不建议通读。

### macro_rules

定义声明宏的关键字。

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}
```

---

### Pattern Matching (模式匹配)

<!-- glossary-waive: Pattern Matching — 本处为宏领域特指义项（macro_rules! 参数匹配），区别于语言级模式匹配，后者以 concept/00_meta/01_terminology/01_terminology_glossary.md 权威定义为准 -->

宏的参数匹配规则（`macro_rules!` 领域特指；语言级“解构值并根据结构执行分支”的模式匹配见权威术语表）。

**片段说明符** (Fragment Specifiers):

- `$name:expr` - 表达式
- `$name:ident` - 标识符
- `$name:ty` - 类型
- `$name:pat` - 模式
- `$name:stmt` - 语句
- `$name:block` - 代码块
- `$name:item` - 项（函数、结构体（Struct）等）
- `$name:tt` - 单个 token 树

```rust
macro_rules! create_function {
    ($func_name:ident) => {
        fn $func_name() {
            println!("Called {}", stringify!($func_name));
        }
    };
}
```

---

### Repetition (重复)

宏参数的重复模式。

**语法**: `$(...)*` 或 `$(...)+` 或 `$(...)?`

```rust
macro_rules! sum {
    ($($num:expr),*) => {
        0 $(+ $num)*
    };
}

let result = sum!(1, 2, 3, 4); // 10
```

**符号含义**:

- `*` - 零次或多次
- `+` - 一次或多次
- `?` - 零次或一次

---

### Metavariable (元变量)

宏模式中捕获的变量，如 `$name`。

```rust
macro_rules! create_var {
    ($var_name:ident, $var_value:expr) => {
        let $var_name = $var_value;
    };
}

create_var!(x, 42); // let x = 42;
```

---

## ⚙️ 过程宏术语

本节目录化过程宏体系的核心术语：

- **TokenStream**：过程宏的输入输出类型——token 序列（标识符/字面量/标点/组），携带 span 信息；`proc_macro::TokenStream`（编译器接口）与 `proc_macro2::TokenStream`（可测试的镜像）的区分是过程宏测试的前提；
- **三种宏形态**：Derive（`#[proc_macro_derive(Name, attributes(...))]`，附加到类型定义）、Attribute（`#[proc_macro_attribute]`，替换被标注项）、Function-like（`#[proc_macro]`，`name!(...)` 调用）——形态决定输入形态与输出位置；
- **syn**：`TokenStream` → AST 的解析库——`parse_macro_input!` 宏、`DeriveInput`/`ItemFn` 等语法树类型、`Error` 诊断体系；
- **quote**：AST → `TokenStream` 的生成库——准引用语法与 `#var` 插值。

配套概念：过程宏在**编译期独立 crate 中执行**——这解释了「为什么宏 crate 不能 `use` 自己」「为什么宏依赖不进入下游运行时依赖」。

### TokenStream

宏输入和输出的 token 流。

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 处理 input，返回新的 TokenStream
    input
}
```

**特点**:

- 表示代码的 token 序列
- 可解析、修改、生成

---

### Derive Macro (派生宏)

通过 `#[derive(...)]` 自动为类型生成 trait 实现的过程宏。

```rust
#[derive(Debug, Clone, MyTrait)]
struct MyStruct {
    field: i32,
}
```

**定义**:

```rust
#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    // 生成 impl MyTrait for T {}
}
```

---

### Attribute Macro (属性宏)

以 `#[...]` 形式附加到项的过程宏，可为代码添加元数据、重写或包装被标注代码。

```rust
#[route(GET, "/")]
fn index() -> String {
    "Hello!".to_string()
}
```

**定义**:

```rust
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    // attr: GET, "/"
    // item: fn index() { ... }
    // 返回修改后的函数
}
```

---

### Function-like Macro (函数式宏)

看起来像函数调用的宏。

```rust
let sql = sql!(SELECT * FROM users WHERE id = 1);
```

**定义**:

```rust
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    // 解析 SQL，生成代码
}
```

---

### syn Crate

解析 TokenStream 的库。

```rust
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    // ...
}
```

**功能**:

- 解析 Rust 语法
- 提供 AST 数据结构
- 错误处理（Error Handling）

---

### quote Crate

生成 TokenStream 的库。

```rust
use quote::quote;

let name = &input.ident;
let expanded = quote! {
    impl MyTrait for #name {
        fn my_method(&self) {
            println!("Hello from {}", stringify!(#name));
        }
    }
};
```

**功能**:

- 使用类 Rust 语法生成代码
- 插值变量 `#var`
- 重复 `#(...)*`

---

### Span

代码位置信息，用于错误消息。

```rust
use proc_macro::Span;

let span = Span::call_site(); // 宏调用位置
let span = ident.span();       // 标识符位置
```

**用途**:

- 精确的错误提示
- 保留源代码位置
- 调试信息

---

## 🧹 卫生性与作用域

卫生性（hygiene）相关四个术语定义了「宏生成代码中的名字如何解析」的完整规则体系：

- **Hygiene（卫生性）**：宏展开代码中的标识符解析遵循「定义点可见性」与「调用点可见性」的分离规则——宏内部定义的 `let tmp` 不与调用点的 `tmp` 冲突，宏参数 `$e` 中的标识符按调用点解析。形式化来源：Kohlbecker (1986) 的 hygiene 条件——「宏展开等价于先把所有标识符按来源染色，再按颜色解析绑定」。Rust 的 `macro_rules!` 是部分卫生（局部变量/标签卫生，项级路径不卫生——宏内 `println!` 需调用点可解析或写 `::std::` 全路径）。
- **Call Site（调用点）**：宏被调用的源码位置。`Span::call_site()` 使生成标识符按「调用处可见的名字」解析——过程宏生成「引用用户类型」的代码时的默认选择。
- **Definition Site（定义点）**：宏定义所在的源码位置。按定义点解析的标识符只能看到宏 crate 内部的绑定——`macro_rules!` 的局部变量默认如此（这是卫生性的实现），过程宏需 nightly 的 `Span::def_site()`。
- **Mixed Site（混合点）**：`Span::mixed_site()`——局部变量按定义点（卫生）、项路径与宏调用按调用点（可解析用户代码），复刻 `macro_rules!` 的混合卫生行为，是过程宏模拟声明宏语义的标准选择。

判定一个「cannot find X in this scope」宏错误：看 X 是什么——局部变量冲突是卫生性问题（改名或用 mixed_site），项/路径找不到是 span 选择问题（改 call_site + 全路径），`$crate` 缺失是声明宏跨 crate 问题。

### Hygiene (卫生性)

宏内外标识符不冲突的机制。

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42; // 不会与外部 a 冲突
            $e
        }
    }
}

let a = 13;
let result = using_a!(a + a); // 26，使用外部 a
```

**保证**:

- 宏内定义的标识符不泄露
- 宏外标识符不被捕获（除非显式引用（Reference））

---

### Call Site (调用点)

宏被调用的位置。

```rust
# macro_rules! my_macro { ($($t:tt)*) => {} }
// 这里是 call site
my_macro!(some_input);
```

**影响**:

- Span 信息
- 作用域解析
- 卫生性规则

---

### Definition Site (定义点)

宏被定义的位置。

```rust
// 这里是 definition site
macro_rules! my_macro {
    () => {};
}
```

---

### Mixed Site (混合点)

syn 2.0+ 引入的概念，用于更精细的卫生性控制。

```rust
use proc_macro2::Span;

let span = Span::mixed_site();
```

---

## 🛠️ 工具与库

宏工程生态的三个必备工具/库，覆盖「调试 → 基础 → 测试」全流程：

- **cargo-expand**：`cargo expand` 子命令，展示宏完全展开后的源码——调试「宏生成了什么」的唯一权威手段（编译器错误信息指向展开后代码时尤其必需）。原理是调用 rustc 的 `-Zunpretty=expanded`（nightly）或内置等效路径；大型项目用 `cargo expand --lib path::to::module` 缩小输出范围。
- **proc-macro2**：`proc_macro` API 的「宏外可用」镜像——`proc_macro::TokenStream` 只能在编译器插件进程内存在，`proc_macro2::TokenStream` 是功能等价的自有类型，使「代码生成逻辑」可在普通二进制/测试进程中构造与断言。生态事实标准：syn/quote 全部建立在 proc-macro2 之上；写过程宏时，生成逻辑一律针对 `proc_macro2::TokenStream`，只在入口边界与 `proc_macro` 互转（`From` 双向实现）。
- **trybuild**：过程宏的「编译期望测试」框架——测试用例是「应当编译通过/应当编译失败且错误信息匹配」的 `.rs` 文件，失败用例配 `.stderr` 快照。它把「宏的报错质量」纳入回归测试：错误 span 漂移、诊断文本变化都会 fail CI。这是过程宏质量与「 toy 宏」的分水岭工具。

工具链组合：开发期 `cargo expand` 看展开 → 逻辑层 proc-macro2 单元测试 → 集成层 trybuild 编译期望测试——三层覆盖「生成正确内容、内容能编译、报错可理解」的全部验收维度。

### cargo-expand

查看宏展开结果的工具。

```bash
cargo install cargo-expand
cargo expand
cargo expand my_module::my_function
```

**用途**:

- 调试宏
- 理解宏展开
- 学习宏实现

---

### proc-macro2

`proc_macro` 的独立版本，支持单元测试。

```rust
use proc_macro2::TokenStream;

fn my_helper(input: TokenStream) -> TokenStream {
    // 可以在单元测试中调用
    input
}
```

**优势**:

- 可测试
- 跨平台
- 功能完整

---

### trybuild

测试编译错误的工具。

```rust
#[test]
fn ui_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
```

**用途**:

- 测试宏的错误消息
- 确保错误提示准确

---

## 📚 元编程概念

本节聚焦「📚 元编程概念」，覆盖Metaprogramming (元编程)、AST (抽象语法树)、DSL (领域特定语言)、Code Generation (代码生成)等方面。论述顺序由定义到边界：先明确「📚 元编程概念」在「术语表 - C11 Macro System」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「📚 元编程概念」的判定标准，并指出它在全页论证链中的位置。

### Metaprogramming (元编程)

编写生成或操作程序的程序。

**Rust 宏的元编程能力**:

- 代码生成
- 编译时计算
- 零成本抽象（Zero-Cost Abstraction）

---

### AST (抽象语法树)

Abstract Syntax Tree，源代码解析后的树形结构表示，是编译器前端的输出。

```rust
// 代码
let x = 1 + 2;

// AST (简化表示)
LetStmt {
    pat: Ident("x"),
    init: BinaryOp {
        op: Add,
        left: Lit(1),
        right: Lit(2),
    }
}
```

**在宏中**:

- syn 解析为 AST
- 操作 AST
- quote 生成代码

---

### DSL (领域特定语言)

针对特定领域的小语言。

**示例**:

```rust
# macro_rules! html { ($($t:tt)*) => {} }
html! {
    <div class="container">
        <h1>"Hello, World!"</h1>
    </div>
}
```

**实现方式**:

- 函数式宏
- 自定义解析
- 代码生成

---

### Code Generation (代码生成)

宏的核心功能，在编译时生成代码。

```rust
#[derive(Builder)]
struct User {
    name: String,
    age: u32,
}

// 自动生成 UserBuilder
let user = User::builder()
    .name("Alice".to_string())
    .age(30)
    .build();
```

---

### Zero-Cost Abstraction (零成本抽象)

高级语言特性编译后不产生运行时开销的设计原则：宏展开后的代码性能与手写代码相同。

```rust
// 宏定义的高层抽象
for_each!(vec, |x| println!("{}", x));

// 展开后等价于
for x in vec {
    println!("{}", x);
}
```

**验证方式**:

- 查看宏展开
- 分析 LLVM IR
- 性能基准测试

---

### Compile-time Computation (编译时计算)

在编译期完成计算，运行时（Runtime）零开销。

```rust
const SIZE: usize = compute_size!(some_input);
```

---

**上一步**: [主索引导航](/crates/c11_macro_system_proc/docs/tier_01_foundations/02_navigation.md)
**下一步**: [常见问题](/crates/c11_macro_system_proc/docs/tier_01_foundations/04_faq.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

> **向下引用（Reference）**: 参见 [17_macro_patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md)

## 认知路径

1. **问题识别**: 识别 Rust 宏系统中大量术语（declarative/procedural macro、token、span、hygiene 等）容易混淆的问题。
2. **概念建立**: 掌握每个术语的精确定义、适用场景及其与其他概念的关系。
3. **机制推理**: 通过术语标准化 ⟹ 概念对齐 ⟹ 沟通效率的定理链构建共同语言。
4. **边界辨析**: 辨析“术语表只是字典”等反命题，理解术语是概念网络的入口。
5. **迁移应用**: 将术语表与卫生性、syn/quote 参考等主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 统一术语 ⟹ 减少沟通歧义 | 在团队与文档中使用一致定义 | 技术讨论与代码审查更高效 |
| 术语与概念链接 ⟹ 加速学习 | 每个术语指向权威概念页或示例 | 读者可以从 glossary 进入深度内容 |
| 分类维度清晰 ⟹ 快速检索 | 按宏类型、机制、工具分层组织 | 查找特定术语的时间缩短 |

## 反命题

> **反命题 1**: "术语表只是字典" ⟹ 不成立。良好的术语表还揭示概念之间的关系与学习路径。
>
> **反命题 2**: "初学者不需要术语表" ⟹ 不成立。精确的术语是避免“宏很黑魔法”误解的基础。
>
> **反命题 3**: "术语翻译可以随意" ⟹ 不成立。中英双语应遵循项目统一约定，避免一词多译。
>
## 反向推理

> **反向推理 1**: 发现文档中对同一宏机制使用了多个不同名称 ⟸ 说明缺少统一术语表或约定未被执行。
>
> **反向推理 2**: 学习者在 hygiene 与 span 之间混淆 ⟸ 说明术语表未清晰区分二者层级关系。
>
## 过渡段

> **过渡**: 从术语收集过渡到分类维度，可以理解 glossary 不仅是列表，更是概念地图。
>
> **过渡**: 从分类维度过渡到概念链接，可以建立“查到术语即可进入权威解释”的导航体验。
>
> **过渡**: 从导航体验过渡到与卫生性、参考页的结合，可以形成宏系统学习的完整入口。
>

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Kohlbecker et al.: Hygienic Macro Expansion (LFP 1986, 卫生宏奠基)](https://dl.acm.org/doi/10.1145/319838.319859)
- **P2 生态/社区**: [docs.rs/syn — 宏开发权威 API 文档](https://docs.rs/syn) · [docs.rs/quote — 宏开发权威 API 文档](https://docs.rs/quote)
