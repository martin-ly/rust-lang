> **内容分级**:
>
> [综述级]
> **本节关键术语**: Diagnostic · `Diag` · Span · Error Code · Lint · Lint Pass · UI Test · Compiletest · `--bless` · Applicability — [完整对照表](../00_meta/terminology_glossary.md)
>
# rustc 编译器诊断与 UI Tests

> **EN**: Compiler Diagnostics and UI Tests
> **Summary**: Explains the structure of rustc diagnostics, how lints are defined and emitted, and how UI tests in compiletest verify compiler output.
> **受众**: [专家 / 研究者]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **F** — Formal
> **双维定位**: F×Inf — 编译器基础设施
> **定位**: 把“rustc 的错误信息是怎么构造的、如何测试错误输出”讲清楚，为贡献 rustc 或编写自定义 lint 打下基础。
> **前置概念**: [Rustc Query System](../04_formal/19_rustc_query_system.md) · [Rustc Driver and Stable MIR](68_rustc_driver_and_stable_mir.md)
> **后置概念**: [Rustc Bootstrap](70_rustc_bootstrap.md) · [Compiler Infrastructure](47_compiler_infrastructure.md)

---

> **来源**: [Rustc Dev Guide — Diagnostics](https://rustc-dev-guide.rust-lang.org/diagnostics.html) · [compiletest](https://rustc-dev-guide.rust-lang.org/tests/compiletest.html)
> [Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html) ·
> [Rustc Dev Guide — Compiletest](https://rustc-dev-guide.rust-lang.org/tests/intro.html) ·
> [Rust Reference — Lint Levels](https://doc.rust-lang.org/reference/attributes/diagnostics.html#lint-check-attributes)

## 📑 目录

- [rustc 编译器诊断与 UI Tests](.#rustc-编译器诊断与-ui-tests)
  - [📑 目录](.#-目录)
  - [一、诊断的组成部分](.#一诊断的组成部分)
  - [二、`Diag` 与诊断等级](.#二diag-与诊断等级)
  - [三、Span 与建议（Suggestions）](.#三span-与建议suggestions)
  - [四、Lint 与 Lint Pass](.#四lint-与-lint-pass)
    - [Lint 定义](.#lint-定义)
    - [Lint Pass](.#lint-pass)
  - [五、Error Codes 与 `--explain`](.#五error-codes-与---explain)
  - [六、UI Tests 与 `--bless`](.#六ui-tests-与---bless)
    - [UI Test 是什么](.#ui-test-是什么)
    - [`--bless`](.#--bless)
  - [嵌入式测验](.#嵌入式测验)
    - [测验 1：一条 rustc 诊断至少包含哪三个核心部分？](.#测验-1一条-rustc-诊断至少包含哪三个核心部分)
    - [测验 2：`Applicability::MachineApplicable` 表示什么？](.#测验-2applicabilitymachineapplicable-表示什么)
    - [测验 3：Late lint pass 相比 Early lint pass 的主要优势是什么？](.#测验-3late-lint-pass-相比-early-lint-pass-的主要优势是什么)
    - [测验 4：`--bless` 在 UI testing 中的作用是什么？](.#测验-4--bless-在-ui-testing-中的作用是什么)
  - [权威来源索引](.#权威来源索引)

---

## 一、诊断的组成部分

一条 rustc 诊断通常包含：

```text
error[E0308]: mismatched types
 --> src/main.rs:3:9
  |
3 |     let x: u32 = "hello";
  |                  ^^^^^^^ expected `u32`, found `&str`
  |
  = note: expected type `u32`
             found type `&str`
```

| 部分 | 说明 |
|:---|:---|
| **Level** | `error` / `warning` / `note` / `help` |
| **Error Code** | 如 `E0308`，可通过 `rustc --explain E0308` 查看长说明 |
| **Message** | 问题的主描述 |
| **Span** | 指向源码位置的 `Span`，包含主次 label |
| **Sub-diagnostics** | `note`、`help`、建议等补充信息 |

> [来源: Rustc Dev Guide — Diagnostic structure](https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-structure)

---

## 二、`Diag` 与诊断等级

`rustc_errors` crate 提供诊断 API。推荐方式是用 `Diagnostic` trait / derive 宏（Macro）定义结构化诊断：

```rust,ignore
let mut err = sess.dcx().struct_span_err(sp, fluent::my_lint::my_error);
err.span_label(sp, fluent::my_lint::label);
err.emit();
```

诊断等级：

| 等级 | 含义 |
|:---|:---|
| `error` | 编译失败 |
| `warning` | 警告但不阻止编译 |
| `note` | 补充上下文 |
| `help` | 给出修复建议 |

Lint 等级（用户可控）：

| 等级 | 行为 |
|:---|:---|
| `forbid` | 完全禁止，不能覆盖 |
| `deny` | 视为 error |
| `warn` | 视为 warning |
| `allow` | 忽略 |

---

## 三、Span 与建议（Suggestions）

`Span` 表示源码中的位置，用于精确指向问题代码：

```rust,ignore
err.span_suggestion(
    sp,
    fluent::my_lint::try_this,
    "fix".to_string(),
    Applicability::MachineApplicable,
);
```

`Applicability` 表示建议的可靠程度：

| 值 | 含义 |
|:---|:---|
| `MachineApplicable` | 可机械应用 |
| `HasPlaceholders` | 需要用户填写占位符 |
| `MaybeIncorrect` | 可能不正确 |
| `Unspecified` | 不确定 |

> 结构化建议是 `cargo fix` 和 IDE 自动修复的基础。
>
> [来源: Rustc Dev Guide — Suggestions](https://rustc-dev-guide.rust-lang.org/diagnostics.html#suggestions)

---

## 四、Lint 与 Lint Pass

### Lint 定义

```rust,ignore
declare_lint! {
    WHILE_TRUE,
    Warn,
    "suggest using `loop { }` instead of `while true { }`"
}
```

### Lint Pass

```rust,ignore
declare_lint_pass!(WhileTrue => [WHILE_TRUE]);

impl EarlyLintPass for WhileTrue {
    fn check_expr(&mut self, cx: &EarlyContext<'_>, e: &ast::Expr) {
        // 检查 while true { ... }
    }
}
```

Lint 运行的时机：

| Pass | 时机 | 信息可用性 |
|:---|:---|:---|
| Pre-expansion | 宏（Macro）展开前 | 最少 |
| Early | AST 后、HIR lowering 前 | 语法级 |
| Late | HIR 后、类型检查等分析后 | 完整类型信息 |
| MIR | MIR 上 | 控制流 |

> [来源: Rustc Dev Guide — Lints](https://rustc-dev-guide.rust-lang.org/diagnostics.html#lints)

---

## 五、Error Codes 与 `--explain`

每个主要错误都有唯一代码：

```bash
rustc --explain E0308
```

错误代码的长说明存放在 `compiler/rustc_error_codes/src/error_codes/`。新增错误代码需要同步添加说明文档。

---

## 六、UI Tests 与 `--bless`

### UI Test 是什么

UI test 是 rustc 测试的一种，验证编译器对特定代码产生的诊断输出。测试文件放在 `tests/ui/` 目录：

```rust,compile_fail
// tests/ui/my_feature/error.rs
fn main() {
    let x: u32 = "hello";
    //~^ ERROR mismatched types
}
```

`//~^ ERROR` 等注释标记期望的诊断。

### `--bless`

当诊断输出格式发生变化时，可自动更新期望文件：

```bash
./x test tests/ui/my_feature --bless
```

> **警告**: `--bless` 会覆盖 `.stderr` 文件，应仔细审查变更。
>
> [来源: Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html)

---

## 嵌入式测验

### 测验 1：一条 rustc 诊断至少包含哪三个核心部分？

<details>
<summary>✅ 答案与解析</summary>

Level（如 error/warning）、Message（问题描述）、Span（指向源码位置）。

</details>

---

### 测验 2：`Applicability::MachineApplicable` 表示什么？

<details>
<summary>✅ 答案与解析</summary>

表示该建议可以机械地、安全地自动应用到源码中。

</details>

---

### 测验 3：Late lint pass 相比 Early lint pass 的主要优势是什么？

<details>
<summary>✅ 答案与解析</summary>

Late lint pass 在类型检查等分析之后运行，可以使用完整的类型信息。

</details>

---

### 测验 4：`--bless` 在 UI testing 中的作用是什么？

<details>
<summary>✅ 答案与解析</summary>

当编译器输出格式变化时，`--bless` 自动更新 `.stderr` 等期望文件，但应人工审查。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rustc Dev Guide — Errors and lints](https://rustc-dev-guide.rust-lang.org/diagnostics.html) | ✅ 一级 | 诊断官方文档 |
| [Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html) | ✅ 一级 | UI 测试官方文档 |
| [Rustc Dev Guide — Compiletest](https://rustc-dev-guide.rust-lang.org/tests/intro.html) | ✅ 一级 | compiletest 官方文档 |
| [Rust Reference — Lint Levels](https://doc.rust-lang.org/reference/attributes/diagnostics.html#lint-check-attributes) | ✅ 一级 | lint 等级语言规则 |

---

> **权威来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/), [The Rust Reference](https://doc.rust-lang.org/reference/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.0 / rustc 诊断与 UI tests

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Rustc Dev Guide diagnostics / UI tests 文档
