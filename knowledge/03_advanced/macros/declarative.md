# 声明式宏 (Declarative Macros)

> **Bloom 层级**: 理解

> **📌 简介**: `macro_rules!` 是 Rust 的声明式宏系统，基于模式匹配和模板替换 [来源: Rust Reference — Macros / 2025; RFC 1584 / 2016; 核心设计决策: 在 AST 层面操作 Token 而非文本替换，保证卫生性（Hygiene）]。它在编译期的抽象语法树（AST）层面操作 Token，而非文本替换，从而保证了**卫生性（Hygiene）**——宏不会意外捕获或污染外部作用域的标识符 [来源: Kohlbecker, E., et al. — *Hygienic Macro Expansion* (LFP 1986); Rust 的 `macro_rules!` 通过隐式 gensym 实现卫生性，与 Scheme 的 `syntax-rules` 同源; The Little Book of Rust Macros / 2025]。
>
> **⏱️ 预计学习时间**: 60-90 分钟
> **📚 难度级别**: ⭐⭐⭐⭐ 高级
> **权威来源**: [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html), [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/), [RFC 1584: Macros](https://rust-lang.github.io/rfcs/1584-macros.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增卫生宏（Hygienic Macro）学术来源标注、Kohlbecker et al. (1986) 原始论文引用、macro_rules! 与 C 预处理器跨语言对比 [来源: Authority Source Sprint Batch 8]

---

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

- [x] 理解声明式宏的**卫生性**机制：为什么宏内的变量不会与外部冲突
- [x] 掌握重复模式（`$()*`、`$()+`、`$()?`）和多种捕获类型（`expr`、`ty`、`pat` 等）
- [x] 使用 `tt`（token tree）处理任意 token 序列，实现递归宏
- [x] 识别宏展开中的常见陷阱（贪婪匹配、歧义、递归溢出）
- [x] 理解声明式宏与过程宏的 trade-off，做出正确选择

---

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

1. **函数与模块** — Rust 的基础语法结构
2. **Trait 与泛型** — 宏常与 derive 模式结合（`02_intermediate/traits.md`）
3. **编译流程** — 对 AST 有基本直觉

---

## 🧠 核心概念
>
> **[来源: Rust Official Docs]**

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**声明式宏（Declarative Macro）** 是通过 `macro_rules!` 定义的代码生成规则。它接受一组 **Token**（Rust 代码的最小单元），按照预定义的模式进行匹配，然后替换为另一组 Token。

与 C 预处理器不同，Rust 宏操作的是**结构化 Token 树**，而非原始文本：

```rust
// C 宏（文本替换）
#define SQUARE(x) x * x
SQUARE(1 + 2)  // 展开为 1 + 2 * 1 + 2 = 5 ❌ 错误！

// Rust 宏（Token 树替换）
macro_rules! square {
    ($x:expr) => { $x * $x };
}
square!(1 + 2)  // 展开为 (1 + 2) * (1 + 2) = 9 ✅
```

> 💡 关键直觉：`macro_rules!` 不是"查找替换"，而是**模式匹配 + 结构化构造**。每个捕获的 token 作为不可分割的整体被传递。

#### 1.2 操作定义

```rust
// 基本语法
macro_rules! my_macro {
    // 模式 => 替换模板
    ($x:expr) => {
        println!("value = {}", $x);
    };
    // 多个模式（重载）
    ($x:expr, $y:expr) => {
        println!("values = {}, {}", $x, $y);
    };
}

// 捕获类型
macro_rules! demo_captures {
    // expr: 表达式
    (expr: $e:expr) => { $e };
    // ty: 类型
    (ty: $t:ty) => { stringify!($t) };
    // pat: 模式
    (pat: $p:pat) => { let $p = 42; };
    // ident: 标识符
    (ident: $i:ident) => { fn $i() {} };
    // tt: token tree（最灵活）
    (tt: $($t:tt)*) => { $($t)* };
    // literal: 字面量
    (lit: $l:literal) => { $l };
    // stmt: 语句
    (stmt: $s:stmt) => { $s };
    // path: 路径
    (path: $p:path) => { $p };
    // block: 块
    (block: $b:block) => { $b };
}

// 重复模式
macro_rules! vec_str {
    ($($x:expr),*) => {
        vec![$($x.to_string()),*]
    };
    // 带尾逗号
    ($($x:expr),+,) => {
        vec![$($x.to_string()),*]
    };
}
```

边界操作：

- `$(...)*`：零次或多次重复
- `$(...)+`：一次或多次重复
- `$(...)?`：零次或一次重复（Rust 1.32+）
- `$(...),*`：逗号分隔的重复
- `$(...);*`：分号分隔的重复

#### 1.3 形式化直觉

**编译器视角**:

宏展开发生在**语法分析（Parsing）之后、语义分析之前**：

```
源代码 Token 流
     │
     ▼
┌─────────────────┐
│ 词法分析 (Lexer) │
│ abc + 123       │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Token Tree      │
│ [abc] [+] [123] │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────┐
│ macro_rules! 展开           │
│ • 模式匹配 Token Tree        │
│ • 替换为新的 Token Tree      │
│ • 递归展开直至无宏           │
└──────────────┬──────────────┘
               │
               ▼
┌─────────────────────────────┐
│ AST 构造 + 语义分析          │
│ • 类型检查                   │
│ • 借用检查                   │
└─────────────────────────────┘
```

**卫生性（Hygiene）的形式化理解**:

Rust 的卫生宏为每个宏调用生成**唯一的上下文标识符（syntax context ID）**。宏内部定义的标识符携带该上下文 ID，因此不会与外部同名的标识符冲突。

```rust
macro_rules! define_x {
    () => {
        let x = 42;
    };
}

fn main() {
    let x = 1;
    define_x!();  // 宏内的 x 与外部的 x 是不同的标识符！
    println!("{}", x);  // 输出 1，不是 42
}
```

---

### 模块 2: 属性清单

| 属性名 | 类型 | 值域/取值 | 说明 | 反例边界 |
|--------|------|-----------|------|----------|
| **卫生性** | 固有属性 | true | 宏内标识符不污染外部作用域 | `crate`/`super` 路径可逃逸卫生性 |
| **模式匹配顺序** | 关系属性 | 从上到下 | 宏按定义顺序尝试匹配 | 更具体的模式应放在前面 |
| **贪婪匹配** | 固有属性 | true | `$expr` 会尽可能多地消耗 token | `expr, expr` 模式在 `a, b, c` 上可能歧义 |
| **递归展开** | 关系属性 | 有限 | 宏可调用自身，但递归深度有限制 | 无限递归导致编译器错误 |
| **Token 类型限制** | 固有属性 | 预定义 | `:expr`、`:ty` 等捕获类型是编译器内置的 | 无法自定义新的捕获类型 |
| **非卫生性逃逸** | 关系属性 | 有条件 | `#[macro_export]` 和 `$crate` 允许跨模块 | 需要显式标记 |

#### 关键推论

1. **推论 1（卫生性的边界）**: 卫生性保护局部变量绑定，但不保护**路径**（`crate::foo`）和**生命周期**。如果宏生成 `crate::module::function()`，它会解析到调用者 crate 的对应路径。
2. **推论 2（模式歧义不可解）**: `macro_rules!` 无法像正则表达式那样使用回溯。`$($x:expr),*` 在 `a, b + c, d` 中，`b + c` 会被作为一个 `expr` 捕获，因为 `expr` 是贪婪的。
3. **推论 3（递归宏的表达能力）**: 由于重复模式只能处理同质序列，异质列表（如键值对 `key: value`）通常需要**递归宏**逐层剥离。

---

### 模块 3: 概念依赖图

```mermaid
graph TD
    A[Token Stream] --> B[Lexer]
    B --> C[Token Tree]
    C --> D[macro_rules!]
    D --> E[Pattern Matching]
    E --> F[Capture Types]
    F --> G[expr / ty / pat / tt]
    E --> H[Repetition]
    H --> I[$()* / $()+ / $()?]
    D --> J[Recursive Macros]
    J --> K[TT Munchers]
    D --> L[Hygiene]
    L --> M[Syntax Context]
    D --> N[macro_export]
    N --> O[Cross-module Macros]

    style D fill:#f9f,stroke:#333,stroke-width:2px
    style L fill:#bbf,stroke:#333,stroke-width:2px
    style J fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **模块系统** | 基础 | `#[macro_export]` 和 `macro_use` 的模块可见性 |
| **Trait/Derive** | `02_intermediate/traits.md` | 宏与 derive 模式的结合 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **过程宏** | `03_advanced/macros/procedural.md` | 声明式宏的表达能力限制，何时需要过程宏 |
| **编译器插件** | 专家级 | 编译器内部的宏展开机制 |

---

### 模块 4: 机制解释

#### 4.1 类型系统视角

**捕获类型的分类**：

| 捕获类型 | 匹配内容 | 示例 | 限制 |
|----------|----------|------|------|
| `ident` | 标识符 | `foo`, `_` | 不能是关键字 |
| `path` | 路径 | `std::vec::Vec`, `crate::foo` | 不含泛型参数 |
| `expr` | 表达式 | `1 + 2`, `foo()` | 贪婪匹配 |
| `ty` | 类型 | `i32`, `Vec<String>` | 不含 `impl Trait` |
| `pat` | 模式 | `Some(x)`, `_` | 不含 `|` 或 `if` |
| `stmt` | 语句 | `let x = 1;`, `foo();` | 不含尾表达式 |
| `block` | 块 | `{ let x = 1; x }` | 完整的大括号块 |
| `meta` | 属性内容 | `derive(Clone)` | 用于宏属性 |
| `tt` | token tree | 任意 token 序列 | 最灵活，无语法限制 |
| `lifetime` | 生命周期 | `'a`, `'static` | 以 `'` 开头 |
| `literal` | 字面量 | `42`, `"hello"` | 任何字面量 |

#### 4.2 内存模型视角

宏展开**不发生在运行时**，因此无内存布局影响。但宏生成的代码会影响：

```rust
macro_rules! make_struct {
    ($name:ident { $($field:ident: $ty:ty),* }) => {
        struct $name {
            $(pub $field: $ty),*
        }
    };
}

make_struct!(Point { x: i32, y: i32 });
// 展开为:
// struct Point {
//     pub x: i32,
//     pub y: i32,
// }
```

#### 4.3 运行时视角

宏展开在编译期完成，运行时**零开销**。宏与函数调用的关键差异：

```rust
// 宏：编译期展开，无调用开销
macro_rules! max_macro {
    ($a:expr, $b:expr) => {
        if $a > $b { $a } else { $b }
    };
}

// 函数：运行时调用
fn max_fn<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
```

**宏的问题**：参数可能被求值多次（如 `max_macro!(expensive(), cheap())` 中 `expensive()` 可能调用两次）。

---

### 模块 5: 正例集

#### 5.1 Minimal（最小正例）

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}

fn main() {
    say_hello!();
}
```

#### 5.2 Realistic（真实场景）

`vec!` 宏的简化实现：

```rust
macro_rules! my_vec {
    // 空向量
    () => {
        Vec::new()
    };
    // 带初始容量提示
    ($elem:expr; $n:expr) => {
        std::vec::from_elem($elem, $n)
    };
    // 元素列表
    ($($x:expr),+ $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
}
```

#### 5.3 Production-grade（生产级）

使用 TT Muncher 模式实现异质键值对初始化：

```rust
macro_rules! map {
    // 基础情况：空 map
    (@unit $key:expr => $value:expr) => {
        {
            let mut _map = ::std::collections::HashMap::new();
            _map.insert($key, $value);
            _map
        }
    };
    // 递归情况：多个键值对
    (@unit $key:expr => $value:expr, $($rest:tt)*) => {
        {
            let mut _map = map!(@unit $($rest)*);
            _map.insert($key, $value);
            _map
        }
    };
    // 入口
    ($($key:expr => $value:expr),* $(,)?) => {
        map!(@unit $($key => $value),*)
    };
}

fn main() {
    let m = map! {
        "a" => 1,
        "b" => 2,
        "c" => 3,
    };
    println!("{:?}", m.get("a"));
}
```

---

### 模块 6: 反例集

#### 反例 1: 参数多次求值

**错误代码**:

```rust
macro_rules! bad_max {
    ($a:expr, $b:expr) => {
        if $a > $b { $a } else { $b }
    };
}

fn expensive() -> i32 {
    println!("expensive called!");
    42
}

fn main() {
    let m = bad_max!(expensive(), 0);
}
```

**输出**:

```text
expensive called!
expensive called!
```

**根因推导**: `expensive()` 在 `if $a > $b` 和 `{ $a }` 中各出现一次，因此被调用两次。

**修复方案**:

```rust
macro_rules! good_max {
    ($a:expr, $b:expr) => {{
        let _a = $a;
        let _b = $b;
        if _a > _b { _a } else { _b }
    }};
}
```

**抽象原则**: **"宏参数可能多次求值"**：如果参数可能有副作用或成本高，先将其绑定到局部变量。

---

#### 反例 2: 贪婪匹配导致的歧义

**错误代码**:

```rust
macro_rules! bad_parse {
    ($a:expr, $b:expr) => {
        ($a, $b)
    };
}

fn main() {
    let x = bad_parse!(1, 2, 3);  // ❌ 编译错误！
}
```

**编译器错误**:

```text
error: no rules expected the token `,`
   |
   |     let x = bad_parse!(1, 2, 3);
   |                             ^ no rules expected this token
```

**根因推导**: `expr` 是贪婪的。`1, 2` 不是有效的 `expr`，所以编译器匹配 `1` 为 `$a`，然后期望 `,`，但接下来 `2, 3` 无法匹配单个 `$b:expr`。

实际上更准确地说：`1` 匹配 `$a:expr`，然后期望 `,`，然后 `2, 3` 作为整体无法匹配 `$b:expr`（因为 `2, 3` 不是表达式）。

**修复方案**:

```rust
macro_rules! good_parse {
    ($($a:expr),+ $(,)?) => {
        ($($a),*)
    };
}
```

**抽象原则**: **"expr 的贪婪性是不可改变的"**：设计宏模式时，必须考虑 `expr` 会尽可能多地消费 token。

---

#### 反例 3: 卫生性导致的意外行为

**错误代码**:

```rust
macro_rules! make_fn {
    ($name:ident) => {
        fn $name() -> i32 {
            let x = 42;
            x
        }
    };
}

make_fn!(foo);

fn main() {
    let x = foo();  // ✅ 正常
    // let x = x;   // ❌ 如果尝试用宏内的变量名
}
```

**根因推导**: 宏内定义的 `x` 与外部的 `x` 是不同的标识符（不同 syntax context）。这通常是**期望的行为**，但有时开发者希望宏使用外部变量。

**修复方案** — 通过参数传递外部标识符:

```rust
macro_rules! make_fn_using {
    ($name:ident, $var:ident) => {
        fn $name() -> i32 {
            $var  // 使用调用者提供的标识符
        }
    };
}

fn main() {
    let my_var = 100;
    make_fn_using!(foo, my_var);
    println!("{}", foo());  // 输出 100
}
```

**抽象原则**: **"卫生性是默认保护，可通过参数显式穿透"**：如果需要宏与外部作用域交互，通过 `ident` 捕获显式传递标识符。

---

---

## 🗺️ 模块 7: 思维表征套件

### 表征 A: 宏展开流程图

```text
源代码:
┌─────────────────────────────────────┐
│ macro_rules! my_vec {               │
│     ($($x:expr),*) => {             │
│         vec![$($x),*]               │
│     };                               │
│ }                                    │
│                                      │
│ let v = my_vec!(1, 2, 3);           │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 词法分析 + Token Tree 化             │
│                                      │
│ my_vec ! ( 1 , 2 , 3 )              │
│  │    │ │ │ │ │ │ │                 │
│  │    │ │ │ │ │ │ └─ )              │
│  │    │ │ │ │ │ └── 3               │
│  │    │ │ │ │ └──── ,               │
│  │    │ │ │ └────── 2               │
│  │    │ │ └──────── ,               │
│  │    │ └────────── 1               │
│  │    └───────────── (              │
│  └─────────────────── my_vec        │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 模式匹配                             │
│                                      │
│ ($($x:expr),*)                      │
│  │  │  │  │                         │
│  │  │  │  └── * (零次或多次)         │
│  │  │  └───── , (逗号分隔)           │
│  │  └──────── expr (表达式捕获)       │
│  └─────────── $x (捕获名)            │
│                                      │
│ 匹配: 1, 2, 3                       │
│ $x = [1, 2, 3]                      │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 替换模板                             │
│                                      │
│ vec![$($x),*]                       │
│       │  │  │                        │
│       │  │  └── 重复 *               │
│       │  └───── , (逗号)             │
│       └──────── $x (插入捕获)         │
│                                      │
│ 展开为: vec![1, 2, 3]               │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 继续解析 + 类型检查                   │
│                                      │
│ vec![1, 2, 3] 是标准宏，继续展开...  │
│ 最终: Vec::from([1, 2, 3])          │
└─────────────────────────────────────┘
```

### 表征 B: 捕获类型选择决策树

```text
                    ┌─────────────────────────────────────┐
                    │  开始: 需要捕获宏参数的某部分         │
                    └──────────────┬──────────────────────┘
                                   │
                                   ▼
                    ┌─────────────────────────────────────┐
                    │  问题1: 需要匹配的内容是否有结构?      │
                    │  (表达式/类型/模式/块)                │
                    └──────────────┬──────────────────────┘
                                   │
            ┌──────────────────────┴──────────────────────┐
            │有结构 (可分类)                               │无结构/任意
            ▼                                           ▼
    ┌───────────────────────────┐           ┌───────────────────────────┐
    │ 问题2: 具体是什么结构?     │           │ **tt (token tree)**       │
    │                           │           │                           │
    │ • 表达式 → expr           │           │ • 最灵活                  │
    │ • 类型   → ty             │           │ • 可递归处理              │
    │ • 模式   → pat            │           │ • 适合复杂/异质语法       │
    │ • 语句   → stmt           │           │ • 例: 任意 token 序列     │
    │ • 块     → block          │           │                           │
    │ • 路径   → path           │           │ 缺点: 无语法验证           │
    │ • 标识符 → ident          │           │ 宏内部可能语法错误         │
    │ • 字面量 → literal        │           │                           │
    │ • 生命周期 → lifetime     │           │                           │
    └───────────────────────────┘           └───────────────────────────┘
```

### 表征 C: 声明式宏 vs 过程宏对比矩阵

| 维度 | `macro_rules!` | 过程宏 (Procedural) |
|------|---------------|---------------------|
| **实现方式** | 模式匹配 + 模板 | Rust 代码操作 TokenStream |
| **表达能力** | 中（重复、递归） | 高（任意逻辑） |
| **编译速度** | 快 | 慢（需编译 proc-macro crate） |
| **错误信息** | 一般（指向展开代码） | 可控（可自定义 Span） |
| **适用场景** | 简单 DSL、重复代码 | 复杂 derive、自定义语法 |
| **hygiene 控制** | 自动 | 需手动处理 |
| **学习曲线** | 陡峭（模式匹配逻辑） | 更陡峭（Token 操作 API） |
| **调试难度** | 难（展开结果不可见） | 中等（可用 cargo-expand） |

---

## 📚 模块 8: 国际化对齐

### 8.1 官方来源

| 来源 | 类型 | 对应章节/条目 | 本文档对应点 |
|------|------|---------------|--------------|
| [The Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) | 官方教程 | 声明式宏基础 | 模块 1、模块 5 |
| [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html) | 官方参考 | 捕获类型、重复模式 | 模块 4.1 |
| [Rust Reference - Hygiene](https://doc.rust-lang.org/reference/macros-by-example.html#hygiene) | 官方参考 | 卫生性机制 | 模块 1.3 |

### 8.2 学术来源

| 论文/来源 | 会议/机构 | 核心论证 | 本文档对应点 |
|-----------|-----------|----------|--------------|
| **"Macros That Work Together"** | Scheme 社区 | 卫生宏的原始理论基础 | 模块 1.3 |
| **"Rust Macro Hygiene"** | Rust 编译器 | Rust 卫生性的具体实现（syntax context） | 模块 1.3 |

### 8.3 社区权威

| 作者 | 文章/演讲 | 核心观点 | 本文档对应点 |
|------|-----------|----------|--------------|
| **Daniel Keep** | ["The Little Book of Rust Macros"](https://danielkeep.github.io/tlborm/book/index.html) | 最权威的声明式宏教程，涵盖 TT Munchers、推导出宏模式 | 模块 5.3、模块 6 |
| **Jon Gjengset** | ["Crust of Rust: Declarative Macros"](https://www.youtube.com/watch?v=q6paRBbLgNw) | 从零实现复杂宏 | 模块 5 |
| **David Tolnay** (syn/quote 作者) | proc-macro-workshop | 过程宏的系统性教学 | 模块 7 对比矩阵 |

### 8.4 跨语言对比

| 维度 | Rust `macro_rules!` | C Preprocessor | Lisp Macros | C++ Templates |
|------|---------------------|----------------|-------------|---------------|
| **操作对象** | Token Tree | 文本 | S-expressions | AST/类型 |
| **卫生性** | ✅ 强 | ❌ 无 | ✅ 强（部分方言） | ❌ 无 |
| **编译期** | ✅ | ✅ | ✅（运行时也可） | ✅ |
| **图灵完备** | ✅（有限） | ❌ | ✅ | ✅ |
| **调试** | 难 | 难 | 容易 | 极难 |
| **类型安全** | 展开后检查 | 无 | 运行时 | 编译期 |
| **递归** | ✅ | ❌ | ✅ | ✅ |

> **关键差异**: Rust 的声明式宏在卫生性和编译期检查之间取得了平衡。C 预处理器是文本替换，无安全保障；Lisp 宏强大但缺乏静态类型检查；C++ 模板是" accidentally Turing-complete"，错误信息 notoriously 差。

---

## ⚖️ 模块 9: 设计权衡分析

### 9.1 为什么 Rust 有两种宏系统？

`macro_rules!` 的设计目标是**常见模式的快速抽象**：

- 简单、声明式、无需额外 crate
- 编译速度快
- 适合 `vec!`、`println!` 等标准宏

过程宏的设计目标是**无限表达能力**：

- 操作任意 TokenStream
- 可访问外部数据（文件、网络）
- 适合 `derive`、自定义属性

### 9.2 该设计的成本

**学习曲线**: `macro_rules!` 的模式匹配逻辑与常规编程思维不同。TT Muncher 等高级模式尤其晦涩。

**调试困难**: 宏展开结果不可见（除非使用 `cargo-expand`），编译错误指向展开后的代码，而非宏调用点。

**表达能力限制**: 无法执行任意计算（如读取配置文件生成代码），必须升级到过程宏。

### 9.3 什么场景下声明式宏是次优的？

1. **需要复杂逻辑时**: 如根据结构体字段生成多个 impl 块。过程宏更合适。
2. **需要自定义错误信息时**: `macro_rules!` 的错误信息由编译器生成，难以控制。
3. **需要操作现有 AST 时**: 声明式宏只能"生成"，不能"查询"已有代码结构。

---

## 📝 模块 10: 自我检测与练习

### 概念性问题

1. **为什么 `macro_rules!` 的卫生性仅保护标识符绑定，而不保护路径（如 `crate::foo`）？** 这给宏设计带来了什么约束？

2. **`$($x:expr),*` 在匹配 `1 + 2, 3` 时，`$x` 捕获什么？** 如果模式改为 `$($x:tt),*`，捕获结果有何不同？

3. **声明式宏的递归展开深度是否有限制？** 如果宏无限递归自身，编译器何时报告错误？

### 代码修复题

**题 1**: 修复以下宏，使其正确处理空参数列表和尾逗号：

```rust
macro_rules! sum {
    ($($x:expr),*) => {
        0 $(+ $x)*
    };
}
```

要求：`sum!()` 返回 `0`，`sum!(1,)` 返回 `1`，`sum!(1, 2, 3)` 返回 `6`。

<details>
<summary>参考答案</summary>

```rust
macro_rules! sum {
    () => { 0 };
    ($($x:expr),+ $(,)?) => {
        0 $(+ $x)*
    };
}
```

或更简洁：

```rust
macro_rules! sum {
    ($($x:expr),* $(,)?) => {
        0 $(+ $x)*
    };
}
```

</details>

**题 2**: 以下宏试图生成 getter 方法，但编译失败。请修复：

```rust
macro_rules! make_getters {
    ($($field:ident),*) => {
        $(
            fn $field(&self) -> &String {
                &self.$field
            }
        )*
    };
}

struct Person {
    name: String,
    age: u32,
}

impl Person {
    make_getters!(name, age);
}
```

<details>
<summary>参考答案</summary>

**根因**: `fn $field(&self) -> &String` 中，`$field` 作为函数名和字段名同时出现，但 `age` 的类型是 `u32`，不是 `String`。宏需要同时捕获字段名和类型。

**修复**:

```rust
macro_rules! make_getters {
    ($($field:ident: $ty:ty),* $(,)?) => {
        $(
            fn $field(&self) -> &$ty {
                &self.$field
            }
        )*
    };
}

impl Person {
    make_getters! {
        name: String,
        age: u32,
    }
}
```

</details>

### 开放设计题

**题 3**: 你正在设计一个测试框架的 `assert_eq!` 宏增强版。要求：

- 显示左右两边的实际值
- 支持自定义错误消息
- 只在调试构建中计算值（发布构建中保持高效）

请分析以下实现选择的 trade-off：

1. `macro_rules!` 实现
2. 过程宏实现
3. 泛型函数 + `cfg(debug_assertions)`

> 💡 提示：参考模块 7 的对比矩阵和模块 9 的成本分析。

---

## 📖 延伸阅读

- [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/index.html) — 最权威的声明式宏教程
- [The Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)

---

> 🎉 **恭喜你！** 你已经掌握了 Rust 声明式宏的核心机制。理解卫生性、捕获类型、重复模式和递归展开，是编写和维护宏代码的基础。
>
> **下一步建议**: 学习 **过程宏**（`03_advanced/macros/procedural.md`），理解当声明式宏的表达能力不足时，如何使用 `proc-macro` crate 实现 `derive` 和自定义属性。

---

**文档版本**: 2.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 📚 权威来源索引

### 官方来源

- [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) [来源: Rust Reference / 2025]
- [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/) [来源: Daniel Keep / 2015+]
- [RFC 1584: Macros](https://rust-lang.github.io/rfcs/1584-macros.html) [来源: Rust Core Team / 2016]

### 学术来源

- Kohlbecker, E., Friedman, D.P., Felleisen, M. & Duba, B. — *Hygienic Macro Expansion*. LFP 1986. [来源: 卫生宏的原始形式化定义; 隐式 gensym 防止标识符意外捕获]

### 跨语言来源

- C — C Preprocessor (`#define`) [来源: 文本替换宏与 Rust AST 宏的对比; C 宏无卫生性保证，常见意外捕获问题]
- Scheme — `syntax-rules`, `syntax-case` [来源: 卫生宏的早期语言实现; 与 Rust `macro_rules!` 的设计同源]
- C++ — Templates [来源: C++ 模板作为图灵完备的编译期元编程; 与 Rust 宏系统的不同设计哲学]

---

## 相关概念

- [过程宏 (Procedural Macros)](procedural.md)
- [Macros 宏系统](README.md)
