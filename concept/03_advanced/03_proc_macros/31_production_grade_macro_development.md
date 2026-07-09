> **内容分级**: [专家级]
>

# 生产级宏开发
>
> **EN**: Production-Grade Macro Development
> **Summary**: Engineering practices for shipping and maintaining Rust procedural macro crates: MSRV policy, edition compatibility, span-aware diagnostics, documentation, semantic versioning, CI/CD, and long-term maintenance.
>
> **受众**: [专家]
> **层级**: L3 高级概念
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: P×Eva — 评估宏库工程实践
> **前置概念**: [过程宏](07_proc_macro.md) · [宏调试与诊断](30_macro_debugging_and_diagnostics.md) · [元编程](../../02_intermediate/06_macros_and_metaprogramming/21_metaprogramming.md) · [Cargo 注册表与包发布](../../06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md)
> **后置概念**: [Cargo semver-checks](../../07_future/03_preview_features/46_cargo_semver_checks_preview.md) · [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/82_engineering_and_production_patterns.md)
>
> **主要来源**: [The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html) · [Cargo Book](https://doc.rust-lang.org/cargo/index.html) · [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Semantic Versioning](https://semver.org/) · [Keep a Changelog](https://keepachangelog.com/)
>
> **Rust 版本**: 1.96.1+ (Edition 2024)

---

> **来源**: 本文档由 `crates/*/docs/` 合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：
> **权威来源**: [concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md](31_production_grade_macro_development.md)

---

## 一、核心定位

生产级宏开发不仅是“让宏能工作”，还需要考虑：

- **版本兼容性**: MSRV、Edition、依赖版本策略。
- **错误诊断**: 用户遇到宏错误时能否快速修复。
- **文档与示例**: 生成的 API 是否易于理解和使用。
- **发布与维护**: 语义化版本、Changelog、CI/CD、安全审计。

---

## 二、版本兼容性

### 2.1 MSRV 管理

```toml
[package]
name = "my_macro"
version = "1.0.0"
rust-version = "1.70.0"  # 最低支持的 Rust 版本
```

**保守策略**（推荐）：

- Minor 版本不提升 MSRV。
- Major 版本可提升 MSRV，且应至少支持最近 6 个月的稳定版。

```text
v1.0.0 (MSRV 1.65)
v1.1.0 (MSRV 1.65) ✅ 不变
v2.0.0 (MSRV 1.70) ✅ Major 可更新
```

### 2.2 Edition 兼容

过程宏 crate 本身的 `edition` 不影响使用方的 edition，但生成代码中使用的语法特性需要兼容目标 edition：

```rust
// 生成代码时使用全限定路径，避免 edition 相关解析差异
quote! { ::std::vec::Vec::new() }
```

### 2.3 核心依赖固定

```toml
[dependencies]
syn = "2.0"
quote = "1.0"
proc-macro2 = "1.0"
```

> **关键洞察**: `syn`、`quote`、`proc-macro2` 是过程宏生态的“基石依赖”。固定其 Major 版本可避免用户依赖图中出现不兼容的多个版本。

---

## 三、错误诊断最佳实践

### 3.1 保留原始 Span

```rust
use syn::{Error, Field};

fn validate_field(field: &Field) -> Result<(), Error> {
    if field.attrs.is_empty() {
        return Err(Error::new(
            field.span(),
            "expected at least one attribute",
        ));
    }
    Ok(())
}
```

### 3.2 提供上下文和帮助

```rust
use syn::Error;

fn report_type_mismatch(field: &syn::Field, expected: &str, found: &str) -> Error {
    Error::new(
        field.span(),
        format!(
            "expected field type `{}`, found `{}`\n\
             \n\
             help: change the field type to `{}`\n\
             note: this restriction is due to the `Serialize` trait requirement",
            expected, found, expected
        ),
    )
}
```

### 3.3 多错误聚合

一次性报告所有问题，避免用户逐个修复：

```rust
match validate_all(&input) {
    Ok(_) => generate_code(),
    Err(errors) => errors
        .into_iter()
        .map(|e| e.to_compile_error())
        .collect::<proc_macro2::TokenStream>()
        .into(),
}
```

---

## 四、文档生成

### 4.1 完整示例

````rust
/// Derive a builder for a struct.
///
/// # Examples
///
/// ```
/// use my_macro::Builder;
///
/// #[derive(Builder)]
/// struct Config {
///     host: String,
///     port: u16,
/// }
///
/// let config = ConfigBuilder::new()
///     .host("localhost".to_string())
///     .port(8080)
///     .build();
/// ```
#[proc_macro_derive(Builder, attributes(builder))]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // ...
}
````

### 4.2 隐藏实现细节

```rust
/// ⚠️ Internal implementation detail, do not use directly.
#[doc(hidden)]
pub mod __internal {
    pub fn helper_function() {}
}
```

### 4.3 Doc Tests

````rust
/// ```compile_fail
/// use my_macro::Builder;
/// #[derive(Builder)]
/// struct Invalid { field } // 缺少类型
/// ```
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream { /* ... */ }
````

---

## 五、发布策略

### 5.1 语义化版本

| 变更类型 | 版本段 | 示例 |
|:---|:---|:---|
| 破坏性变更 | MAJOR | 1.5.0 → 2.0.0 |
| 新功能（向后兼容） | MINOR | 1.5.0 → 1.6.0 |
| Bug 修复 | PATCH | 1.5.0 → 1.5.1 |

### 5.2 预发布版本

```toml
[package]
version = "2.0.0-rc.1"
```

### 5.3 Breaking Changes 处理

```rust
// v1.8.0: 先添加弃用警告
#[deprecated(since = "1.8.0", note = "will be removed in 2.0.0, use `new_api()`")]
pub fn old_api() { new_api(); }

// v2.0.0: 移除旧 API
```

### 5.4 CI/CD 发布流程

```yaml
# .github/workflows/release.yml
name: Release
on:
  push:
    tags: ["v*"]

jobs:
  publish:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions-rust-lang/setup-rust-toolchain@v1
      - run: cargo test --all-features
      - run: cargo publish --token ${{ secrets.CARGO_TOKEN }}
```

---

## 六、维护策略

### 6.1 安全审计

```yaml
# .github/workflows/audit.yml
name: Security Audit
on:
  schedule:
    - cron: "0 0 * * *"

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: rustsec/audit-check@v1
```

### 6.2 依赖更新节奏

| 版本类型 | 检查频率 |
|:---|:---|
| PATCH | 每周 |
| MINOR | 每月 |
| MAJOR | 每季度 |

### 6.3 长期支持承诺

- Major 版本至少维护 2 年。
- 弃用旧 API 前提前 6 个月通告。
- 提供迁移指南或自动化迁移工具。

---

## 七、生产级宏开发检查清单

- [ ] 声明 MSRV 并在 CI 中测试
- [ ] 核心依赖固定 Major 版本
- [ ] 错误消息指向用户代码位置
- [ ] 提供清晰的帮助文本（help/note）
- [ ] 文档包含完整可运行示例
- [ ] 使用 `#[doc(hidden)]` 隐藏内部实现
- [ ] 包含编译失败 doc test 或 trybuild 测试
- [ ] 遵循语义化版本
- [ ] 维护 Changelog
- [ ] 配置 `cargo audit` 安全扫描
- [ ] 发布前运行 `cargo publish --dry-run`

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Cargo Book](https://doc.rust-lang.org/cargo/index.html) · [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [SemVer](https://semver.org/) · [Keep a Changelog](https://keepachangelog.com/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c11_macro_system_proc/docs/tier_04_advanced/05_production_grade_macro_development.md` 按 AGENTS.md §6.4 迁移至此

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成
