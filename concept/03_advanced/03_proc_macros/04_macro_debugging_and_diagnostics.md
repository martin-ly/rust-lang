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

## 一、核心定位

宏在编译期展开，传统运行时（Runtime）调试器无法直接介入。因此宏开发需要专用工具链：

- **查看展开结果**: `cargo expand`
- **打印中间状态**: `eprintln!` / `tracing` / `RUSTC_LOG`
- **精确定位错误**: `Span` + `syn::Error`
- **性能分析**: `cargo build --timings`, `cargo-llvm-lines`
- **高级需求**: 自定义 `rustc` 回调或 lint

---

## 二、使用 cargo expand

「使用 cargo expand」部分包含安装与基础用法 与 比较宏展开差异 两条主线，本节依次说明。

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

本节从过程宏中的 stderr 输出 与 声明宏中的条件调试 两个层面剖析「在宏中打印诊断信息」。

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

「精确错误定位」部分按使用 syn::Error、组合多个错误与proc-macro-error 友好错误的顺序逐层展开。

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

「编译期性能分析」涉及 cargo build --timings、RUSTC_LOG与测量宏展开耗时，本节逐一说明其要点。

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

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Kohlbecker et al.: Hygienic Macro Expansion (LFP 1986, 卫生宏奠基)](https://dl.acm.org/doi/10.1145/319838.319859)
