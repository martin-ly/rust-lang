> **内容分级**: [专家级]
>

# 宏调试与诊断
>
> **EN**: Macro Debugging and Diagnostics
> **Summary**: Debugging procedural and declarative macros in Rust: cargo expand, compiler callbacks, macro expansion tracing, compile-time performance profiling, and producing precise span-based error messages.
>
> **受众**: [专家]
> **层级**: L3 高级概念
> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: P×App — 宏调试与错误诊断流程
> **前置概念**: [过程宏](07_proc_macro.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/21_metaprogramming.md)
> **后置概念**: [生产级宏开发](31_production_grade_macro_development.md) · [rustc 编译器诊断](../../06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md)
>
> **主要来源**: [The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html) · [cargo-expand](https://github.com/dtolnay/cargo-expand) · [rustc-dev-guide — Macro Expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html) · [proc-macro2 crate](https://docs.rs/proc-macro2/)
>
> **Rust 版本**: 1.96.1+ (Edition 2024)

---

> **来源**: 本文档由 `crates/*/docs/` 合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：
> **权威来源**: [concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md](30_macro_debugging_and_diagnostics.md)

---

## 一、核心定位

宏在编译期展开，传统运行时调试器无法直接介入。因此宏开发需要专用工具链：

- **查看展开结果**: `cargo expand`
- **打印中间状态**: `eprintln!` / `tracing` / `RUSTC_LOG`
- **精确定位错误**: `Span` + `syn::Error`
- **性能分析**: `cargo build --timings`, `cargo-llvm-lines`
- **高级需求**: 自定义 `rustc` 回调或 lint

---

## 二、使用 cargo expand

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

### 2.2 比较宏展开差异

```bash
cargo expand > before.rs
# 修改宏代码...
cargo expand > after.rs
diff -u before.rs after.rs
```

> **关键洞察**: `cargo expand` 是宏调试的“printf 调试器”——当编译错误指向宏调用处但你看不出原因时，查看展开后的代码通常能立刻定位问题。

---

## 三、在宏中打印诊断信息

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

### 5.1 cargo build --timings

```bash
cargo build --release --timings
```

### 5.2 RUSTC_LOG

```bash
RUSTC_LOG=rustc_expand::trace_macros cargo build 2>&1 | tee expand.log
```

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

> ⚠️ 以下代码需要 nightly 工具链与 `#![feature(rustc_private)]`。

```rust,ignore
#![feature(rustc_private)]

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

> **关键洞察**: 自定义 `rustc` 回调是强大的诊断手段，但它将代码绑定到 nightly 编译器内部 API，通常只用于研究和教学工具，不推荐用于生产宏库。

---

## 七、调试检查清单

- [ ] 用 `cargo expand` 查看最终生成的代码
- [ ] 用 `eprintln!` 打印宏输入/输出 TokenStream
- [ ] 用 `quote_spanned!` / `syn::Error::new_spanned` 保留错误位置
- [ ] 用 `cargo build --timings` 识别慢速 proc-macro crate
- [ ] 用 `cargo llvm-lines` 定位单态化膨胀
- [ ] 用 `trybuild` 做编译失败快照测试
- [ ] 用 `#[cfg(feature = "macro-debug")]` 提供可选调试输出

---

> **权威来源**: [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) · [cargo-expand](https://github.com/dtolnay/cargo-expand) · [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/macro-expansion.html) · [proc-macro2](https://docs.rs/proc-macro2/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c11_macro_system_proc/docs/tier_04_advanced/04_macro_debugging_in_depth.md` 按 AGENTS.md §6.4 迁移至此

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成
