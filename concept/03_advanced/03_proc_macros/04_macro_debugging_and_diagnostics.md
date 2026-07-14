> **内容分级**: [专家级]
>

# 宏调试与诊断
>
> **EN**: Macro Debugging and Diagnostics
> **Summary**: Debugging procedural and declarative macros in Rust: cargo expand, compiler callbacks, macro expansion tracing, compile-time performance profiling, and producing precise span-based error messages.
>
> **受众**: [专家]
> **层级**: L3 高级概念
> **Bloom 层级**: L3-L4
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: P×App — 宏（Macro）调试与错误诊断流程
> **前置概念**: [过程宏（Procedural Macro）](02_proc_macro.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md)
> **后置概念**: [生产级宏（Macro）开发](05_production_grade_macro_development.md) · [rustc 编译器诊断](../../06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md)
>
> **主要来源**:
> [The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html) ·
> [cargo-expand](https://github.com/dtolnay/cargo-expand) ·
> [rustc-dev-guide — Macro Expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html) ·
> [proc-macro2 crate](https://docs.rs/proc-macro2/)
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。

---

> **来源**: 本文档由 `crates/*/docs/` 合规整改迁移而来。原始 crate 文档现为摘要页，指向本权威页：
> **权威来源**: [concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md](04_macro_debugging_and_diagnostics.md)

---

## 📑 目录

- [宏调试与诊断](#宏调试与诊断)
  - [📑 目录](#-目录)
  - [一、核心定位](#一核心定位)
  - [二、使用 cargo expand](#二使用-cargo-expand)
    - [2.1 安装与基础用法](#21-安装与基础用法)
    - [2.2 比较宏展开差异](#22-比较宏展开差异)
  - [三、在宏中打印诊断信息](#三在宏中打印诊断信息)
    - [3.1 过程宏中的 stderr 输出](#31-过程宏中的-stderr-输出)
    - [3.2 声明宏中的条件调试](#32-声明宏中的条件调试)
  - [四、精确错误定位](#四精确错误定位)
    - [4.1 使用 syn::Error](#41-使用-synerror)
    - [4.2 组合多个错误](#42-组合多个错误)
    - [4.3 proc-macro-error 友好错误](#43-proc-macro-error-友好错误)
  - [五、编译期性能分析](#五编译期性能分析)
    - [5.1 cargo build --timings](#51-cargo-build---timings)
    - [5.2 RUSTC\_LOG](#52-rustc_log)
    - [5.3 测量宏展开耗时](#53-测量宏展开耗时)
  - [六、编译器回调（高级）](#六编译器回调高级)
  - [七、调试检查清单](#七调试检查清单)
  - [认知路径](#认知路径)
  - [定理链](#定理链)
  - [反命题](#反命题)
  - [反向推理](#反向推理)
  - [过渡段](#过渡段)
  - [📋 关键属性](#-关键属性)
  - [🔗 概念关系](#-概念关系)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

---

## 一、核心定位

宏在编译期展开，传统运行时（Runtime）调试器无法直接介入。因此宏开发需要专用工具链：

- **查看展开结果**: `cargo expand`
- **打印中间状态**: `eprintln!` / `tracing` / `RUSTC_LOG`
- **精确定位错误**: `Span` + `syn::Error`
- **性能分析**: `cargo build --timings`, `cargo-llvm-lines`
- **高级需求**: 自定义 `rustc` 回调或 lint

---

## 二、使用 cargo expand

`cargo expand` 是宏调试的第一工具——它展示宏展开后的完整代码。三个核心用法：

- **基础用法（2.1）**：`cargo expand`（整个 crate）、`cargo expand path::to::item`（单项）——配合 `--ugly` 跳过格式化看原始生成；安装：`cargo install cargo-expand`（依赖 nightly 内部工具但可用于 stable 项目）；
- **比较展开差异（2.2）**：`cargo expand > before.rs`，修改宏后再次展开 `diff`——宏版本升级审查的标准流程，「升级后生成代码变了什么」一目了然；
- **诊断流程**：宏相关编译错误的标准处置是「先展开、再定位」——错误指向展开结果时，在展开代码中搜索报错标识符，反推是哪段生成逻辑产生。

局限：`cargo expand` 展示的是**成功展开**的结果——宏自身 panic 或生成非法语法时无输出，此时需配合 `RUSTC_LOG` 或宏内 stderr 调试（下节）。

### 2.1 安装与基础用法

```bash
cargo install cargo-expand

# 展开当前 crate 所有宏
cargo expand

# 展开指定模块或项
cargo expand my_module::my_function

# 展开测试
cargo expand --tests

# 按 feature 展开
cargo expand --features my_feature
```

(Source: [cargo-expand](https://github.com/dtolnay/cargo-expand))

### 2.2 比较宏展开差异

```bash
cargo expand > before.rs
# 修改宏代码...
cargo expand > after.rs
diff -u before.rs after.rs
```

> **关键洞察**: `cargo expand` 是宏调试的“printf 调试器”——当编译错误指向宏调用处但你看不出原因时，查看展开后的代码通常能立刻定位问题 (Source: [cargo-expand README](https://github.com/dtolnay/cargo-expand))。

---

## 三、在宏中打印诊断信息

本节聚焦「在宏中打印诊断信息」，覆盖过程宏中的 stderr 输出 与 声明宏中的条件调试。论述顺序由定义到边界：先明确「在宏中打印诊断信息」在「宏调试与诊断」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「在宏中打印诊断信息」的判定标准，并指出它在全页论证链中的位置。

### 3.1 过程宏中的 stderr 输出

```rust
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    eprintln!("[MACRO DEBUG] input: {}", input);
    let output = generate_code(&input);
    eprintln!("[MACRO DEBUG] output: {}", output);
    output
}
```

### 3.2 声明宏中的条件调试

```rust
macro_rules! debug_macro {
    ($($arg:tt)*) => {{
        #[cfg(feature = "macro-debug")]
        eprintln!("[MACRO DEBUG] expanding: {}", stringify!($($arg)*));
        // 实际逻辑...
    }};
}
```

---

## 四、精确错误定位

宏错误的定位质量取决于 span 管理，三个层次的工具：

- **`syn::Error`（4.1）**：`Error::new(span, msg)`/`Error::new_spanned(tokens, msg)` 把错误绑定到具体 token——`to_compile_error()` 转为可注入输出流的编译错误代码，错误在 IDE 中精确标红用户输入而非宏调用整体；
- **组合多个错误（4.2）**：`Error::combine` 累积全部问题一次性报告——「一次修复一个错误」的循环是宏用户体验的最大杀手；
- **`proc-macro-error2`（4.3）**：属性宏风格的错误流——`abort!(span, msg)` 立即终止并报告、`emit_error!` 累积后继续，省去手动 thread `Result` 的样板（本库 vendor 目录维护其修复版）。

定位基准：宏的每个错误都应能回答「用户改哪一行」——答不出的错误信息需要重写。

### 4.1 使用 syn::Error

```rust
use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput, Error};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    match &input.data {
        syn::Data::Struct(s) if matches!(s.fields, syn::Fields::Named(_)) => {
            // generate...
            TokenStream::new()
        }
        _ => {
            Error::new_spanned(
                input,
                "Builder can only be derived for structs with named fields",
            )
            .to_compile_error()
            .into()
        }
    }
}
```

### 4.2 组合多个错误

```rust
fn validate_all(input: &DeriveInput) -> Result<(), Vec<Error>> {
    let mut errors = Vec::new();
    if let Err(e) = validate_generics(input) { errors.push(e); }
    if let Err(e) = validate_fields(input) { errors.push(e); }
    if errors.is_empty() { Ok(()) } else { Err(errors) }
}

// 使用：
match validate_all(&input) {
    Ok(_) => generate_code(),
    Err(errors) => errors.into_iter()
        .map(|e| e.to_compile_error())
        .collect::<proc_macro2::TokenStream>()
        .into(),
}
```

### 4.3 proc-macro-error 友好错误

```rust
use proc_macro_error::{abort, proc_macro_error};

#[proc_macro_derive(MyTrait)]
#[proc_macro_error]
pub fn my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    if input.generics.params.is_empty() {
        abort!(
            input.ident.span(),
            "expected at least one generic parameter";
            help = "try: struct {}<T> {{ ... }}", input.ident
        );
    }
    // ...
}
```

---

## 五、编译期性能分析

宏拖慢编译的定位工具链：

- **`cargo build --timings`（5.1）**：定位宏 crate 在编译关键路径上的耗时——过程宏 crate 本身（proc-macro2/syn/quote 依赖树）编译时间常占小项目一半；
- **`RUSTC_LOG`（5.2）**：`RUSTC_LOG=expand` 等日志通道观察展开行为（需 nightly `-Z` 配合），追踪宏展开的触发次数与耗时；
- **测量宏展开耗时（5.3）**：过程宏内用 `std::time::Instant` + feature 门控的 stderr 输出——找到「哪个输入类型触发最慢展开」，常见元凶是深层 `syn` 递归解析与逐 token 的 `to_string` 拼接。

优化顺序：先减 syn 解析深度（只 parse 需要的节点），再减 token 往返（`TokenStream` 直接操作优于 `to_string` 来回），最后考虑缓存（相同输入的展开结果 memoize，注意 span 失效）。

### 5.1 cargo build --timings

```bash
cargo build --release --timings
```

### 5.2 RUSTC_LOG

```bash
RUSTC_LOG=rustc_expand::trace_macros cargo build 2>&1 | tee expand.log
```

(Source: [rustc-dev-guide — Logging](https://rustc-dev-guide.rust-lang.org/compiler-debugging.html?highlight=RUSTC_LOG#logging))

### 5.3 测量宏展开耗时

```rust
use std::time::Instant;

#[proc_macro]
pub fn timed_macro(input: TokenStream) -> TokenStream {
    let start = Instant::now();
    let output = expand(input);
    eprintln!("[TIMING] macro expansion took {:?}", start.elapsed());
    output
}
```

---

## 六、编译器回调（高级）

> ⚠️ 以下代码需要每日构建版工具链与实验特性门 `rustc_private`。

```rust,ignore
// 需启用实验特性门 rustc_private（每日构建版工具链）

extern crate rustc_driver;
extern crate rustc_interface;

use rustc_interface::interface::Compiler;
use rustc_interface::Queries;

struct MyCallbacks;

impl rustc_driver::Callbacks for MyCallbacks {
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        println!("✅ macro expansion completed");
        rustc_driver::Compilation::Continue
    }
}
```

> **关键洞察**: 自定义 `rustc` 回调是强大的诊断手段，但它将代码绑定到每日构建版编译器内部 API，通常只用于研究和教学工具，不推荐用于生产宏库 (Source: [rustc-dev-guide — Rustc Driver](https://rustc-dev-guide.rust-lang.org/))。

---

## 七、调试检查清单

- [ ] 用 `cargo expand` 查看最终生成的代码
- [ ] 用 `eprintln!` 打印宏输入/输出 TokenStream
- [ ] 用 `quote_spanned!` / `syn::Error::new_spanned` 保留错误位置
- [ ] 用 `cargo build --timings` 识别慢速 proc-macro crate
- [ ] 用 `cargo llvm-lines` 定位单态化（Monomorphization）膨胀
- [ ] 用 `trybuild` 做编译失败快照测试
- [ ] 用 `#[cfg(feature = "macro-debug")]` 提供可选调试输出

---

> **权威来源**: [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) · [cargo-expand](https://github.com/dtolnay/cargo-expand) · [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/macro-expansion.html) · [proc-macro2](https://docs.rs/proc-macro2/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c11_macro_system_proc/docs/tier_04_advanced/04_macro_debugging_in_depth.md` 按 AGENTS.md §6.4 迁移至此

**文档版本**: 1.0
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成

## 认知路径

1. **问题识别**: 识别宏在编译期展开导致传统运行时（Runtime）调试器失效的问题。
2. **概念建立**: 掌握 cargo-expand、编译器回调、span 跟踪与编译期性能分析技术。
3. **机制推理**: 通过展开追踪 ⟹ span 保留 ⟹ 精确诊断的定理链提升排错效率。
4. **边界辨析**: 辨析“宏错误信息必然模糊”等反命题，理解 span 与诊断 API 的价值。
5. **迁移应用**: 将宏调试与生产级开发、编译器诊断主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| cargo-expand ⟹ 可视化展开结果 | 查看宏实际生成的代码 | 快速定位逻辑错误与生成的意外代码 |
| Span 保留 ⟹ 错误定位到调用点 | 使用 `Span::call_site` / `Span::mixed_site` | 用户看到的报错位置更准确 |
| 编译期性能分析 ⟹ 定位慢宏 | 测量各宏的展开耗时 | 优化工作聚焦在真正的热点上 |

## 反命题

> **反命题 1**: "可以用常规 debugger 调试过程宏（Procedural Macro）" ⟹ 不成立。宏在编译期执行，运行时调试器无法介入。
>
> **反命题 2**: "宏错误信息必然模糊" ⟹ 不成立。通过 `proc_macro::Diagnostic` 与 span 可以输出精确错误。
>
> **反命题 3**: "cargo-expand 只在本地开发有用" ⟹ 不成立。CI 中对比展开结果可及早发现回归。
>
## 反向推理

> **反向推理 1**: 用户报告错误指向宏内部而非调用处 ⟸ 说明 span 未正确传递，应检查 quote/parse 的 span 来源。
>
> **反向推理 2**: 编译时间未变但 CI 报宏展开结果差异 ⟸ 说明缺少展开快照测试或 rustc 版本漂移。
>
## 过渡段

> **过渡**: 从传统调试失效过渡到 cargo-expand，可以理解宏开发需要专门的“展开视图”。
>
> **过渡**: 从展开视图过渡到 span 保留，可以建立“代码生成在哪里发生，错误就报告在哪里”的原则。
>
> **过渡**: 从 span 保留过渡到诊断 API，可以形成用户友好的宏错误信息工程实践。
>

---

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 展开查看 | `cargo expand` 查看宏展开结果，支持模块/测试/feature 维度过滤 | 本文 §二 |
| 诊断输出 | 过程宏可向 stderr 输出诊断；`syn::Error` 提供精确定位 | 本文 §三–§四 |
| 错误聚合 | `syn::Error::combine` 一次报告多个错误 | 本文 §4.2 |
| 性能分析 | `cargo build --timings` / `RUSTC_LOG` / 宏展开耗时测量 | 本文 §五 |
| 排查路径 | 展开 → 定位 → 性能三步检查清单 | 本文 §七 |

## 🔗 概念关系

- **上位（is-a）**：[过程宏](02_proc_macro.md) 的工程化支撑层（调试 / 诊断 / 性能）。
- **下位（实例）**：cargo expand、syn::Error、proc-macro-error、`--timings` 四组工具。
- **组合**：与 [宏卫生](09_macro_hygiene.md)（Span 决定错误定位精度）组合。
- **依赖**：依赖 [常用开发工具](../../01_foundation/10_testing_basics/02_useful_development_tools.md) 的工具链。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Kohlbecker et al.: Hygienic Macro Expansion (LFP 1986, 卫生宏奠基)](https://dl.acm.org/doi/10.1145/319838.319859)
