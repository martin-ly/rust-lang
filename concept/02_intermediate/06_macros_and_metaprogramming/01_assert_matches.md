> **内容分级**: [综述级]
> **本节关键术语**: assert_matches! · 模式匹配（Pattern Matching）断言 (Pattern Match Assertion) · debug_assert_matches! · 测试断言 (Test Assertion) — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
# `assert_matches!`：模式匹配断言的形式化语义
>
> **EN**: assert_matches! Macro
> **Summary**: The `assert_matches!` macro for pattern-based assertions on enums and trait objects.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: F×App — 断言和模式匹配（Pattern Matching）语法应用
> **定位**: 将 Rust 的**模式匹配（Pattern Matching）**能力从"表达式求值"扩展到"测试断言"的工程机制，实现编译期模式检查与运行时（Runtime）断言的统一。
> **前置概念**: [Type System](../../01_foundation/02_type_system/01_type_system.md) · [Error Handling](../03_error_handling/01_error_handling.md)
> **后置概念**: [Macros](../../03_advanced/03_proc_macros/01_macros.md) · [Version Tracking](../../07_future/00_version_tracking/01_rust_version_tracking.md)

---

> **来源**: · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982) · [Unicode UAX #31 — Identifier and Pattern Syntax](https://www.unicode.org/reports/tr31/)
> [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) ·
> Rust 1.96 Release Notes ·
> [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/) ·
> [std::assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html) ·
> [RFC 2005 — `matches!`](https://github.com/rust-lang/rfcs/pull/2005) ·
> [std::matches](https://doc.rust-lang.org/std/macro.matches.html)

## 📑 目录

- [`assert_matches!`：模式匹配断言的形式化语义](#assert_matches模式匹配断言的形式化语义)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 `matches!`：模式匹配的布尔化](#11-matches模式匹配的布尔化)
    - [1.2 `assert_matches!`：从判断到断言](#12-assert_matches从判断到断言)
    - [1.3 `debug_assert_matches!`：编译期条件断言](#13-debug_assert_matches编译期条件断言)
  - [二、形式化语义](#二形式化语义)
    - [2.1 与 `assert!` / `assert_eq!` 的对比](#21-与-assert--assert_eq-的对比)
    - [2.2 绑定捕获与作用域](#22-绑定捕获与作用域)
  - [三、使用场景与最佳实践](#三使用场景与最佳实践)
    - [3.1 测试中的 Result/Option 断言](#31-测试中的-resultoption-断言)
    - [3.2 复杂枚举变体验证](#32-复杂枚举变体验证)
    - [3.3 与 `if let` 的互补关系](#33-与-if-let-的互补关系)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、来源与延伸阅读](#五来源与延伸阅读)
    - [编译验证示例](#编译验证示例)
  - [相关概念](#相关概念)
  - [逆向推理链（Backward Reasoning）](#逆向推理链backward-reasoning)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：assert\_matches 的编译错误](#十边界测试assert_matches-的编译错误)
    - [10.1 边界测试：`assert_matches!` 在非 Option/Result 上使用（编译错误）](#101-边界测试assert_matches-在非-optionresult-上使用编译错误)
    - [10.2 边界测试：嵌套模式匹配中的绑定冲突（编译错误）](#102-边界测试嵌套模式匹配中的绑定冲突编译错误)
    - [10.3 边界测试：`assert_matches!` 与嵌套模式的绑定（编译错误）](#103-边界测试assert_matches-与嵌套模式的绑定编译错误)
    - [10.4 边界测试：自定义断言失败消息的类型约束（编译错误）](#104-边界测试自定义断言失败消息的类型约束编译错误)
    - [10.4 边界测试：所有权移动后的再次使用](#104-边界测试所有权移动后的再次使用)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：`assert_matches!(value, pattern)` 的主要用途是什么？与 `assert!(matches!(value, pattern))` 相比有什么优势？（理解层）](#测验-1assert_matchesvalue-pattern-的主要用途是什么与-assertmatchesvalue-pattern-相比有什么优势理解层)
    - [测验 2：`assert_matches!` 是否可以在模式中绑定变量？绑定后的变量在测试体中可用吗？（理解层）](#测验-2assert_matches-是否可以在模式中绑定变量绑定后的变量在测试体中可用吗理解层)
    - [测验 3：如果 `assert_matches!` 在你的 stable Rust 版本中不可用，最简单的替代方案是什么？（理解层）](#测验-3如果-assert_matches-在你的-stable-rust-版本中不可用最简单的替代方案是什么理解层)
    - [测验 4：`assert_matches!(x, Some(_))` 与 `assert!(x.is_some())` 在语义上有区别吗？（理解层）](#测验-4assert_matchesx-some_-与-assertxis_some-在语义上有区别吗理解层)
    - [测验 5：`assert_matches!` 对测试枚举变体有什么特别便利之处？（理解层）](#测验-5assert_matches-对测试枚举变体有什么特别便利之处理解层)
  - [实践](#实践)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
  - [📋 关键属性](#-关键属性)
  - [🔗 概念关系](#-概念关系)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、核心概念
>
>

### 1.1 `matches!`：模式匹配的布尔化
>

Rust 1.42 引入 `matches!` 宏（Macro），将模式匹配从**控制流**转化为**布尔表达式**：

```rust
let x = Some(42);

// 传统方式：需要 match 控制流
let is_some_forty_two = match x {
    Some(42) => true,
    _ => false,
};

// matches! 方式：直接返回 bool
let is_some_forty_two = matches!(x, Some(42));
assert!(is_some_forty_two);
```

> **形式化语义**: `matches!(e, p)` ≡ `match e { p => true, _ => false }`
>
> 即 `matches!` 是模式匹配的**布尔投影**（boolean projection），将 `match` 的代数结果 `{true, false}` 显式提取为 `bool` 类型。
> [来源: [RFC 2005](https://github.com/rust-lang/rfcs/pull/2005)]

**支持守卫条件（guard）**:

```rust
let x = Some(42);
assert!(matches!(x, Some(n) if n > 10)); // ✅ 通过
assert!(matches!(x, Some(n) if n > 100)); // ❌ 失败
```

> **关键洞察**: `matches!` 不改变模式匹配的语义，仅改变**返回类型**——从 `()`（控制流）到 `bool`（表达式值）。这是 Rust 宏（Macro）系统的典型应用：语法糖不改变语义，仅改变语法形式。
> [💡 原创分析](../../00_meta/00_framework/methodology.md)

---

### 1.2 `assert_matches!`：从判断到断言
>

Rust 1.96.0 稳定化 `assert_matches!`，将 `matches!` 的布尔结果**提升为断言契约**：

```rust
// 需要 Rust 1.96+
use std::assert_matches;

let result: Result<i32, &str> = Ok(42);

// 断言 result 匹配 Ok 变体
assert_matches!(result, Ok(n) if n == 42);

// 支持嵌套模式
let nested: Result<Option<i32>, &str> = Ok(Some(42));
assert_matches!(nested, Ok(Some(n)) if n > 0);
```

> **语义核心**: `assert_matches!(e, p)` 执行以下操作：
>
> 1. 计算表达式 `e`
> 2. 尝试将 `e` 与模式 `p` 匹配
> 3. 若匹配成功：断言通过
> 4. 若匹配失败：触发 panic，显示不匹配信息
> 5. 支持 guard 条件：`assert_matches!(e, p if guard)`
>
> **注意**: 绑定不可导出到宏（Macro）外部。如需提取值并后续使用，请使用 `if let`。
> [来源: [std::assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html)]

**与 `assert!(matches!(...))` 的对比**:

```rust
use std::assert_matches;

let result: Result<i32, &str> = Ok(42);

// 方式 A: assert! + matches!（Rust < 1.96）
assert!(matches!(result, Ok(n) if n > 10));
// 失败时信息: "assertion failed: matches!(result, Ok(n) if n > 10)"

// 方式 B: assert_matches!（Rust 1.96.0+）
assert_matches!(result, Ok(n) if n > 10);
// 失败时信息: 显示实际值和期望模式，更易于调试
```

> **关键差异**: `assert_matches!` 在匹配成功时**保留绑定**，允许在断言通过后继续使用模式绑定的变量。这是 `assert!(matches!(...))` 无法实现的——后者在 `matches!` 返回后绑定已丢失。

---

### 1.3 `debug_assert_matches!`：编译期条件断言
>

与 `assert!` / `debug_assert!` 的关系一致：

```rust,ignore
use std::assert_matches::debug_assert_matches;

// release 模式下被消除（零运行时开销）
let config = Some(true);
debug_assert_matches!(config, Some(true));
```

> ⚠️ **重要**: `assert_matches!` 和 `debug_assert_matches!`**未加入标准 prelude**。这是因为它们与流行的第三方 crate（如 `assert_matches` crate）存在命名冲突。使用时需显式导入：
>
> ```rust
> use std::assert_matches; // 或 core::assert_matches
> ```
>
> 来源: [Rust 1.96 Release Notes — Assert matching patterns]

| 宏（Macro） | debug 模式 | release 模式 | 用例 |
|:---|:---:|:---:|:---|
| `assert_matches!` | ✅ 执行 | ✅ 执行 | 不变量检查、测试 |
| `debug_assert_matches!` | ✅ 执行 | ❌ 消除 | 性能敏感路径的调试断言 |

> **定理**: `debug_assert_matches!` 在 release 模式下不产生任何机器码。
> (Source: [Rust Reference — debug_assertions](https://doc.rust-lang.org/reference/conditional-compilation.html#debug_assertions))
> **证明**: 宏（Macro）展开为 `if cfg!(debug_assertions) { assert_matches!(...) }`，编译器在 `cfg!(false)` 时消除整个分支。
> [来源: [Rust Reference — debug_assertions](https://doc.rust-lang.org/reference/conditional-compilation.html#debug_assertions)]

---

## 二、形式化语义

`assert_matches!` 的形式语义可以经与既有断言宏（Macro）的对比精确刻画：

- **与 `assert!` / `assert_eq!` 的对比**：`assert!(matches!(x, pat))` 与 `assert_matches!(x, pat)` 语义等价，但失败信息不同——`assert_matches!` 在失败时打印「实际值 : 模式」的对照（经 `Debug`），而 `assert!(matches!(...))` 只报 `matches! 返回 false`。与 `assert_eq!` 的区别更深：`assert_eq!` 要求 `PartialEq + Debug` 且比较整个值；`assert_matches!` 用模式匹配，可断言「结构性形状」而忽略字段细节（`Some(_)`, `Err(Error::Io(_))`），也不要求 `PartialEq`——这使它能断言不可比较类型（如含闭包（Closures）的枚举）。
- **绑定捕获与作用域**：`assert_matches!(x, Some(v) if v > 0)` 中的绑定 `v` 只在断言内部（宏展开生成的 `match` 臂）有效，不泄漏到外围作用域；守卫表达式 `if ...` 与 `match` 守卫语义完全一致。带守卫的版本语义为「`match x { pat if guard => (), _ => panic!() }`」的宏封装。

形式化：`assert_matches!(e, p)` ⟺ `match e { p => {}, _ => panic!("assertion failed: {:?} does not match {}", e, stringify!(p)) }`——它是「单臂 match + 调试输出」的命名化，价值在诊断质量而非新语义。

### 2.1 与 `assert!` / `assert_eq!` 的对比
>

```mermaid
graph LR
    subgraph 断言家族["Rust 断言宏家族"]
        A["assert!"] -->|泛化| B["assert_eq!"]
        A -->|模式匹配扩展| C["assert_matches!"]
        B -->|特定类型| D["assert_ne!"]
        C -->|调试模式| E["debug_assert_matches!"]
    end

    subgraph 语义差异["核心语义差异"]
        F["assert!(expr)"] -->|expr: bool| G[panic if false]
        H["assert_eq!(a, b)"] -->|a == b| I[panic if unequal]
        J["assert_matches!(e, p)"] -->|e ~ p| K[panic if no match<br/>+ bind variables]
    end
```

> **认知功能**: 此图展示 Rust 断言宏（Macro）的**家族关系**和**语义演进**。`assert_matches!` 填补了"模式匹配断言"的空白，使断言系统从"值相等"扩展到"结构匹配"。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> [来源: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html)]
> **使用建议**: 在测试枚举（Enum）类型时，优先选择 `assert_matches!` 而非 `assert_eq!`——前者验证结构形状，后者仅验证相等性。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> **关键洞察**: 断言系统的演进轨迹是**从具体值到抽象模式**：`assert!`（任意布尔）→ `assert_eq!`（部分相等）→ `assert_matches!`（结构模式）。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))

**形式化对比表**:

| 特性 | `assert!` | `assert_eq!` | `assert_matches!` |
|:---|:---|:---|:---|
| 检查对象 | 任意 `bool` 表达式 | 两个值的 `PartialEq` | 表达式 vs 模式 |
| 失败信息 | 表达式字符串 | 左右值差异 | 实际值 + 期望模式 |
| 绑定捕获 | ❌ 无 | ❌ 无 | ✅ 有 |
| 守卫条件 | ❌ 不支持 | ❌ 不支持 | ✅ `if` guard |
| 适用类型 | 任何类型 | `PartialEq` | 任何可模式匹配类型 |
| 编译期优化 | 无 | 无 | `debug_` 变体可消除 |

---

### 2.2 绑定捕获与作用域
>

```ignore
enum Message {
    Text(String),
    Number(i32),
    Coord { x: f64, y: f64 },
}

let msg = Message::Coord { x: 1.5, y: 2.5 };

// assert_matches! 绑定不可导出到宏外部
// 如需在断言后使用绑定的值，应使用 if let
assert_matches!(msg, Message::Coord { x: 1.5, y: 2.5 });

// 如需提取值并后续使用：
if let Message::Coord { x, y } = msg {
    assert!((x - 1.5).abs() < f64::EPSILON);
    assert!((y - 2.5).abs() < f64::EPSILON);
}
```

> **形式化规则**: `assert_matches!(e, p)` 进行模式匹配断言，绑定不可导出宏（Macro）外部。
>
> - 设 `p` 中的绑定变量集合为 `Vars(p)`
> - 则 `Vars(p)` 的作用域仅限于 `block`
> - 这与 `if let p = e { block }` 的作用域规则完全一致
> [来源: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html)]

---

## 三、使用场景与最佳实践

`assert_matches!` 的最佳实践场景按「断言对象的形状复杂度」递进：

- **测试中的 `Result`/`Option` 断言**：`assert_matches!(resp, Ok(body) if body.status() == 200)` 把「成功 + 内容条件」压成一行，替代「`unwrap` 后再 `assert_eq!`」两步（且失败时不会 panic 在 unwrap 而丢失「是 Err」的诊断信息）。这是它最高频的用途：错误路径测试（`assert_matches!(f(bad), Err(E::Invalid(_)))`）比任何 `is_err()` 断言都精确。
- **复杂枚举变体验证**：多层嵌套枚举（AST、协议消息）的断言，模式可以写到任意深度（`Message::Response { id, payload: Payload::Data(d) } if !d.is_empty()`），而 `assert_eq!` 需要构造完整期望值——对含随机 id/时间戳的消息，模式断言是唯一实用手段。
- **与 `if let` 的互补关系**：`if let` 是生产代码的「条件解构」（不匹配则跳过），`assert_matches!` 是测试代码的「强制匹配」（不匹配则失败）。二者共享同一模式语法——测试中用 `assert_matches!` 锁定的形状，与生产代码 `if let`/`match` 处理的形状形成对照，构成「期望与实际处理」的一致性（Coherence）校验。

实践判定：断言对象是「值相等」用 `assert_eq!`；是「形状匹配 + 忽略细节」用 `assert_matches!`；是「布尔条件」用 `assert!`。三者不互斥，按精度需求选择。

### 3.1 测试中的 Result/Option 断言
>

```rust,ignore
use std::assert_matches::assert_matches;

#[derive(Debug, PartialEq)]
struct Config { port: u16, host: String }

fn parse_config() {
    let result: Result<Config, &str> = Ok(Config { port: 8080, host: "localhost".to_string() });

    // ✅ 推荐: 验证结构形状
    assert_matches!(result, Ok(Config { port, .. }) if *port == 8080);

    // 也可结合 if let 提取值做进一步断言
    if let Ok(Config { port, .. }) = result {
        assert_eq!(port, 8080);
    }
}
```

> **最佳实践**: 在测试中，使用 `assert_matches!` 验证**结构形状**（是否为 `Ok`），然后使用 `assert_eq!` 验证**具体值**。分层断言使测试失败信息更精确。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))

---

### 3.2 复杂枚举变体验证
>

```rust,ignore
use std::assert_matches::assert_matches;

#[derive(Debug)]
enum State {
    Idle,
    Processing { id: u64, progress: f32 },
    Completed(Vec<u8>),
    Error { code: u16, message: String },
}

fn state_machine_transition() {
    let state = State::Processing { id: 42, progress: 0.5 };

    // 验证特定变体
    assert_matches!(state, State::Processing { id, progress } if *id > 0 && *progress <= 1.0);
}
```

---

### 3.3 与 `if let` 的互补关系
>

```mermaid
flowchart TD
    Q{需要 panic 吗?}
    Q -->|是| Q2{需要绑定后续使用?}
    Q -->|否| IfLet["if let / while let<br/>控制流处理"]

    Q2 -->|是| AssertMatches["assert_matches!<br/>断言 + 绑定"]
    Q2 -->|否| AssertMatches2["assert_matches!<br/>无绑定断言"]

    style IfLet fill:#e3f2fd
    style AssertMatches fill:#c8e6c9
    style AssertMatches2 fill:#c8e6c9
```

> **认知功能**: 此决策树帮助开发者在 `if let` 和 `assert_matches!` 之间选择。核心判断标准是"失败是否应导致 panic"。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> **使用建议**: 生产代码中的可选处理用 `if let`；测试和不变量检查用 `assert_matches!`。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> **关键洞察**: `assert_matches!` 本质上是 **"panic-if-no-match + if-let"** 的语法糖，将两个操作压缩为单一表达式。
> (Source: [std::assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html))

---

## 四、反命题与边界分析

本节检验关于 `assert_matches!` 的两条流行说法，并划出其能力边界：

- **反命题 1：「`assert_matches!` 完全替代 `matches!` + `assert!`」** —— 不成立。`assert_matches!`（`assert_matches` feature，仍 nightly）的优势是失败时打印**实际值的 Debug 表示**，但 `matches!` 返回 `bool` 可用于断言之外的控制流；在 stable 上 `assert!(matches!(...))` 仍是唯一选择。
- **反命题 2：「模式绑定后可在断言外使用」** —— 不成立。`assert_matches!(x, Some(v) if v > 0)` 中的绑定 `v` 只在守卫表达式内有效，断言通过后变量不泄漏到测试体——需要绑定值时应先 `let Some(v) = x else { panic!() };` 再断言。

边界极限小节进一步量化：嵌套模式的深度、自定义失败消息的类型约束（必须实现 `Debug`）、以及与非 `Option`/`Result` 枚举的配合模式。

### 4.1 反命题树

```mermaid
graph TD
    ROOT["命题: assert_matches! 适合所有枚举测试断言"]
    ROOT --> Q1{"断言失败时应 panic?"}
    Q1 -->|否| FALSE1["❌ 不适合 — 使用 if let"]
    Q1 -->|是| Q2{"需要提取绑定变量?"}

    Q2 -->|是| TRUE["✅ 适合 — assert_matches!"]
    Q2 -->|否| Q3{"模式复杂度?"}

    Q3 -->|简单| Q4{"是否仅需相等检查?"}
    Q3 -->|复杂| TRUE

    Q4 -->|是| ALT["⚠️ assert_eq! 更简洁"]
    Q4 -->|否| TRUE

    style TRUE fill:#c8e6c9
    style FALSE1 fill:#ffebee
    style ALT fill:#fff3e0
```

> **认知功能**: 此决策树帮助测试编写者在 `assert_matches!`、`assert_eq!` 和 `if let` 之间选择最合适的工具。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> **使用建议**: 对简单标量相等检查，使用 `assert_eq!` 更简洁；对结构匹配和绑定提取，使用 `assert_matches!`。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
> **关键洞察**: 工具选择的本质是**信息粒度**的权衡——`assert_eq!` 验证值，`assert_matches!` 验证形状 + 提取成分。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))

---

### 4.2 边界极限

```rust,ignore
use std::assert_matches::assert_matches;

// 边界 1: 嵌套模式
let x = Some(Some(42));
assert_matches!(x, Some(Some(n)) if n == 42); // ✅ 嵌套模式正常工作

// 边界 2: 或模式 (|)
let x: Result<i32, i32> = Ok(42);
assert_matches!(x, Ok(n) | Err(n) if n > 0); // ✅ 或模式支持

// 边界 3: .. 忽略剩余字段
#[derive(Debug)]
struct Point { x: i32, y: i32, z: i32 }
let x = Point { x: 1, y: 2, z: 3 };
assert_matches!(x, Point { x: 1, .. }); // ✅ .. 正常工作

// 边界 4: 不可反驳模式（编译警告）
let x = 42;
// assert_matches!(x, n); // ⚠️ 不可反驳模式，编译器可能警告
```

> **边界要点**: `assert_matches!` 支持所有标准模式语法（嵌套、或模式、`..`、守卫条件），但**不可反驳模式**（irrefutable patterns）会触发编译器警告——因为断言在此情况下永不为假。
> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))

---

## 五、来源与延伸阅读
>

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust 1.96 Release Notes](https://releases.rs/docs/1.96.0/) | ✅ 一级 | 稳定化公告 |
| [std::assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html) | ✅ 一级 | API 文档 |
| [std::matches](https://doc.rust-lang.org/std/macro.matches.html) | ✅ 一级 | `matches!` 宏（Macro）文档 |
| [RFC 2005 — `matches!`](https://github.com/rust-lang/rfcs/pull/2005) | ✅ 一级 | 设计动机与语义 |
| [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) | ✅ 一级 | 模式匹配权威规范 |

---

```rust
fn main() {
    let opt = Some(42);
    if let Some(v) = opt {
        println!("{}", v);
    }
}
```

### 编译验证示例

```rust
fn main() {
    let x = Some(42);
    assert!(matches!(x, Some(n) if n > 10));
    assert!(!matches!(x, Some(n) if n > 100));

    let y: Result<i32, &str> = Ok(7);
    assert!(matches!(y, Ok(_)));
}
```

```rust
fn main() {
    let msg = "hello";
    assert!(matches!(msg, "hello"));
    assert!(matches!(msg, "world" | "hello"));
}
```

## 相关概念

- [Type System](../../01_foundation/02_type_system/01_type_system.md) — 模式匹配的形式化根基
- [Error Handling](../03_error_handling/01_error_handling.md) — Result/Option 测试断言实践
- [Macros](../../03_advanced/03_proc_macros/01_macros.md) — 宏（Macro）系统的语法糖机制
- [Version Tracking](../../07_future/00_version_tracking/01_rust_version_tracking.md) — Rust 1.96 特性演进

---

> **权威来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html), [std::assert_matches](https://doc.rust-lang.org/std/macro.assert_matches.html), [std::matches](https://doc.rust-lang.org/std/macro.matches.html), [RFC 2005 — matches!](https://github.com/rust-lang/rfcs/pull/2005), [The Rust Programming Language — Patterns](https://doc.rust-lang.org/book/ch19-00-patterns.html)
> **权威来源对齐变更日志**: 2026-05-21 创建，对齐 Rust 1.97.0 (Edition 2024)

**文档版本**: 1.1
**最后更新**: 2026-06-19
**状态**: ✅ 已对齐 Rust 1.97.0 稳定版发布内容

---

## 逆向推理链（Backward Reasoning）

> **从编译错误反推**：
>
> ```text
> 模式匹配穷尽 ⟸ 所有变体被覆盖
> ```
>
## 权威来源索引

>
>
>

---

> **补充来源**

## 十、边界测试：assert_matches 的编译错误

本节的五个边界用例围绕「模式匹配的静态规则在断言宏中同样生效」这一主题：

1. **非枚举/非结构化类型上的模式**：对整数直接写 `assert_matches!(x, Some(_))` 触发 E0308——模式类型必须与值类型匹配；
2. **嵌套模式绑定冲突**：同一模式中两次绑定同名变量（如 `(a, (a, _))`）触发 E0416；
3. **守卫中的绑定**：守卫 `if` 表达式可读取绑定但不能修改（绑定在守卫中为不可变）；
4. **自定义消息的类型约束**：附加的失败消息参数走 `format!` 路径，参数必须实现 `Debug`/`Display`；
5. **所有权移动**：断言按值匹配会 move 被测值，断言后再次使用触发 E0382——需要复用时应匹配引用（Reference）（`assert_matches!(&x, Some(_))`）。

每个用例附最小修复版本，对照学习可同时复习模式匹配规则本身。

### 10.1 边界测试：`assert_matches!` 在非 Option/Result 上使用（编译错误）

```rust,compile_fail
// ❌ 编译错误: assert_matches! 未导入
fn main() {
    let result: Result<i32, &str> = Ok(42);
    assert_matches!(result, Ok(_)); // 错误: 找不到宏 assert_matches!
}
```

```rust
// ✅ 正确: 导入后使用
use std::assert_matches;

fn main() {
    let result: Result<i32, &str> = Ok(42);
    assert_matches!(result, Ok(_)); // ✅ 匹配 Ok 变体
}
```

> **修正**: `assert_matches!`（Rust 长期未稳定，于 Rust 1.96.1 稳定化）专门用于测试枚举（Enum）变体匹配。
> 它不同于 `assert_eq!`——后者要求值实现 `PartialEq`，而 `assert_matches!` 使用模式匹配，不要求 `PartialEq`。
> 在 `assert_matches!` 稳定前，使用 `matches!` 宏（Macro）或 `if let` 进行测试断言。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/index.html)]

### 10.2 边界测试：嵌套模式匹配中的绑定冲突（编译错误）

```rust,compile_fail
fn main() {
    let opt = Some(Some(5));
    // ❌ 编译错误: identifier `x` is bound more than once in the same pattern
    match opt {
        Some(x) | Some(Some(x)) => println!("{}", x),
        None => println!("none"),
    }
}

// 正确: 避免或模式中的绑定冲突
fn fixed() {
    let opt = Some(Some(5));
    match opt {
        Some(Some(x)) => println!("nested: {}", x),
        Some(None) => println!("inner none"),
        None => println!("none"),
    }
}
```

> **修正**: 在 Rust 模式匹配的 `|`（或模式）中，所有分支必须绑定**相同的变量名和类型**。若一个分支绑定 `x: i32`，另一个分支绑定 `x: Option<i32>`，编译器报错。这是 Rust 模式匹配（Pattern Matching）"穷尽性检查"的一部分——确保每个绑定在所有分支中具有一致性（Coherence）。[来源: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)]

### 10.3 边界测试：`assert_matches!` 与嵌套模式的绑定（编译错误）

```rust,ignore
#[test]
fn test_nested_match() {
    let result: Result<Option<i32>, ()> = Ok(Some(42));
    // ⚠️ 设计限制: assert_matches! 是宏，绑定不可导出到宏外部
    // assert_matches!(result, Ok(Some(x)) if x > 0);
    // 如需在断言后使用 x，应改用 if let
}
```

> **修正**: `assert_matches!`（Rust 1.97.0 stable，当前 patch 1.97.0）检查值是否匹配给定模式，但**模式中的绑定**（`x`）在宏（Macro）外部不可见。
> `assert_matches!(result, Ok(Some(x)))` 中 `x` 只在宏（Macro）内部有效，测试代码不能后续使用 `x`。
> 若需提取绑定值，使用 `if let`：`if let Ok(Some(x)) = result { assert!(x > 0); } else { panic!("match failed"); }`。
> `assert_matches!` 的优势是简洁和良好的失败消息（打印不匹配的值），劣势是绑定不可导出。
> 这与 `matches!` 宏（返回 `bool`，无绑定）或 `insta` 的 snapshot 测试（结构化匹配）互补。
> `assert_matches!` 的设计体现了 Rust 宏的能力边界：宏生成的代码在词法上封闭，无法将绑定泄露到外部。
> [来源: [Rust Standard Library](https://doc.rust-lang.org/std/macro.assert_matches.html)] ·
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch19-00-patterns.html)]

### 10.4 边界测试：自定义断言失败消息的类型约束（编译错误）

```rust,compile_fail
fn main() {
    let x = 5;
    // ❌ 编译错误: assert! 的消息参数必须实现 Display
    assert!(x > 10, vec!["failed", "at", "line", "10"]);
    // Vec<&str> 未实现 Display
}
```

> **修正**:
> `assert!`、`assert_eq!`、`assert_ne!` 的自定义消息参数必须实现 `std::fmt::Display` trait。
> `Vec<&str>` 未实现 `Display`，因此不能直接作为消息。
>
> 解决方案：
>
> 1) 使用 `format!("{:?}", vec)`（`Debug` 实现）；
> 2) 使用 `vec.join(", ")` 转为 `String`；
> 3) 使用 `assert!(..., "message", args...)` 的格式化语法。
>
> 这与 C 的 `assert`（只接受布尔，无自定义消息）或 Python 的 `assert`（接受任意表达式作为消息）不同——Rust 的断言消息有类型约束，保证错误输出可读。
> `assert!` 的格式化参数使用与 `println!` 相同的语法，支持 `{}`、`{:?}`、`{:x}` 等格式说明符。
> [来源: [Rust Standard Library](https://doc.rust-lang.org/std/macro.assert.html)] ·
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch19-00-patterns.html)]

### 10.4 边界测试：所有权移动后的再次使用

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    let s2 = s;
    // ❌ 编译错误: s 已被 move 到 s2
    println!("{}", s);
}
```

> **修正**: **Move 语义**：1) `String` 非 `Copy`，赋值时 move 所有权（Ownership）；2) move 后原变量无效；3) 解决：使用 `.clone()` 或引用（Reference） `&s`。

## 嵌入式测验（Embedded Quiz）

本节 5 道测验按 Bloom 认知层级递进，全部聚焦「断言宏与模式匹配的交叉点」：

- 测验 1–2（理解层）：`assert_matches!` 与 `matches!` 的能力差异、模式绑定的作用域规则；
- 测验 3–4（理解→应用层）：stable 替代方案的等价性证明、`assert_matches!(x, Some(_))` 与 `x.is_some()` 的语义差距（前者消费/借用（Borrowing）值，后者只读）；
- 测验 5（理解层）：枚举变体断言在测试驱动开发中的实际收益。

建议作答前先默写每个宏的展开形式，再对照答案中的展开代码——理解宏的展开结果是避免宏相关编译错误的最短路径。

### 测验 1：`assert_matches!(value, pattern)` 的主要用途是什么？与 `assert!(matches!(value, pattern))` 相比有什么优势？（理解层）

**题目**: `assert_matches!(value, pattern)` 的主要用途是什么？与 `assert!(matches!(value, pattern))` 相比有什么优势？

<details>
<summary>✅ 答案与解析</summary>

它断言值匹配给定模式。失败时 `assert_matches!` 通常能显示不匹配值的具体内容，调试信息比 `assert!(matches!(...))` 更丰富。
</details>

---

### 测验 2：`assert_matches!` 是否可以在模式中绑定变量？绑定后的变量在测试体中可用吗？（理解层）

**题目**: `assert_matches!` 是否可以在模式中绑定变量？绑定后的变量在测试体中可用吗？

<details>
<summary>✅ 答案与解析</summary>

可以在模式中绑定变量（如 `assert_matches!(x, Ok(v))` 中的 `v`），绑定变量在 `assert_matches!` 宏展开后的作用域中可用。
</details>

---

### 测验 3：如果 `assert_matches!` 在你的 stable Rust 版本中不可用，最简单的替代方案是什么？（理解层）

**题目**: 如果 `assert_matches!` 在你的 stable Rust 版本中不可用，最简单的替代方案是什么？

<details>
<summary>✅ 答案与解析</summary>

使用 `assert!(matches!(value, pattern))`。`matches!` 宏在 stable Rust 中可用。
</details>

---

### 测验 4：`assert_matches!(x, Some(_))` 与 `assert!(x.is_some())` 在语义上有区别吗？（理解层）

**题目**: `assert_matches!(x, Some(_))` 与 `assert!(x.is_some())` 在语义上有区别吗？

<details>
<summary>✅ 答案与解析</summary>

语义等价，但 `assert_matches!` 更通用，可以匹配任意模式；`is_some()` 仅适用于 `Option`。
</details>

---

### 测验 5：`assert_matches!` 对测试枚举变体有什么特别便利之处？（理解层）

**题目**: `assert_matches!` 对测试枚举变体有什么特别便利之处？

<details>
<summary>✅ 答案与解析</summary>

可以直接写模式匹配枚举的具体变体及其内部结构，避免先 `unwrap` 再 `assert_eq`，更简洁且安全。
</details>

## 实践

> **相关资源**:
>
> - [crates/ 示例代码](../crates) — 与本文概念对应的可编译示例
> - [exercises/ 练习](../exercises) — 动手编程挑战
> - [MVP 学习路径](../../00_meta/04_navigation/08_learning_mvp_path.md) — 从零到多线程 CLI 的 40 小时路径
>
> **建议**: 阅读完本概念文件后，打开对应 crate 的示例代码，尝试修改并运行。完成至少 1 道相关练习以巩固理解。

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **`assert_matches!`：模式匹配断言的形式化语义** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| `assert_matches!`：模式匹配断言的形式化语义 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| `assert_matches!`：模式匹配断言的形式化语义 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时（Runtime） bug | 高 |
| `assert_matches!`：模式匹配断言的形式化语义 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> 测试断言安全 ⟸ assert_matches! 穷尽 ⟸ 模式匹配
> 编译期检查 ⟸ 常量断言 ⟸ const 求值

---

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 语义等价 | `assert_matches!(expr, pat)` ⇔ `assert!(matches!(expr, pat))` 且失败时打印表达式值 | 本文 §1.1–1.2 |
| 稳定状态 | `matches!` 早已稳定；`assert_matches!` 于 Rust 1.96 稳定化 | 本文 §一、§十 |
| debug 变体 | `debug_assert_matches!` 仅在 debug 构建生效 | 本文 §1.3 |
| 绑定捕获 | 模式中的绑定不泄漏到断言之外的作用域 | 本文 §2.2 |
| 互补关系 | 与 `if let` 互补：断言场景更声明式、失败信息更丰富 | 本文 §3.3 |

## 🔗 概念关系

- **上位（is-a）**：[属性与宏](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) 中的标准库断言宏实例。
- **下位（实例）**：`matches!`、`assert_matches!`、`debug_assert_matches!` 三件套。
- **组合**：与 [控制流](../../01_foundation/04_control_flow/01_control_flow.md) 的模式匹配、测试工具链（[常用开发工具](../../01_foundation/10_testing_basics/02_useful_development_tools.md)）组合。
- **依赖**：依赖 [模式](../../01_foundation/04_control_flow/02_patterns.md) 语法。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/syn — 生态权威 API 文档](https://docs.rs/syn) · [docs.rs/quote — 生态权威 API 文档](https://docs.rs/quote)

---

> **Rust 1.96 起**：`assert_matches!` 与 `debug_assert_matches!` 稳定为标准库宏，替代手写 `assert!(matches!(...))` 的模式断言。详见 [版本页](../../07_future/00_version_tracking/rust_1_96_stabilized.md)（特性矩阵节）。

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((assert_matches!模式匹配断言的形式化语))
    一、核心概念
      1.1 matches!模式匹配的布尔化
      1.2 assert_matches!从判断到断言
      1.3 debug_assert_matches!编
    二、形式化语义
      2.1 与 assert! /
      2.2 绑定捕获与作用域
    四、反命题与边界分析
      4.1 反命题树
      4.2 边界极限
```
