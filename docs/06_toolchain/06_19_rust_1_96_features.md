> **版本状态声明**: 本文档覆盖 **Rust 1.96.0 (2026-05-28)** 稳定版内容，含 1.95 关键特性回顾。
> **分级**: [A]
>
> - 1.96.0 内容已与官方 Release Notes (#156512) 逐条核对。
> - 标注 `🔴 nightly-only` 的特性**不是** stable 内容。
> **最后更新**: 2026-05-29

# Rust 1.96 稳定特性全景

> **Bloom 层级**: L3 (应用)

---

## Rust 1.95 新特性（回顾）

> **[来源: Rust 1.95 Release Notes](https://github.com/rust-lang/rust/releases/tag/1.95.0)**

### 1. `if let` 守卫 (if let guards)

Rust 1.95 在 match 表达式中引入了 `if let` 守卫，允许在模式匹配守卫中进行嵌套模式匹配。

```rust
match msg {
    Message::Text(text) if let Some(u) = user => {
        println!("{} says: {}", u.name, text);
    }
    Message::Text(text) => {
        println!("Anonymous says: {}", text);
    }
    _ => {}
}
```

### 2. `RangeInclusive` 迭代性能优化

Rust 1.95 对 `RangeInclusive` 的迭代性能进行了内部优化。

---

## Rust 1.96 稳定特性

> **[来源: Rust Compiler Documentation]**
> **来源**: [GitHub rust-lang/rust #156512](https://github.com/rust-lang/rust/issues/156512) · [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)

### 语言特性

#### 3. `expr` Metavariable 传递给 `cfg`

宏可以将 `expr` 类型的 metavariable 传递给 `cfg` 属性，增强了宏的元编程能力：

```rust
macro_rules! feature_gate {
    ($name:expr, $item:item) => {
        #[cfg($name)]
        $item
    };
}
```

#### 4. Never 类型在 Tuple 中强制转换

`!`（never type）在 tuple 表达式中始终被强制转换为目标类型：

```rust
fn abort() -> ! { panic!("abort") }

// 1.96+: 自动将 `!` coerce 为 i32，无需显式标注
let pair: (i32, i32) = (abort(), 42);
```

#### 5. `ManuallyDrop` 常量作为模式

修复了 1.94.0 引入的回归，允许在 match 模式中使用 `ManuallyDrop` 常量：

```rust
use std::mem::ManuallyDrop;

const TAG: ManuallyDrop<u32> = ManuallyDrop::new(1);

match value {
    TAG => println!("matched"),
    _ => println!("other"),
}
```

#### 6. s390x Vector Registers 内联汇编

`s390x` 架构获得向量寄存器内联汇编支持。

---

### 标准库新 API

> **[来源: Rust Standard Library](https://doc.rust-lang.org/std/)**

#### 7. `assert_matches!` / `debug_assert_matches!`

```rust
use std::assert_matches;

let result: Result<i32, &str> = Ok(42);
assert_matches!(result, Ok(n) if n > 0);

// debug 模式专用（仅在 debug build 中执行）
debug_assert_matches!(config, Config::Debug { verbose: true });
```

**版本勘误**: 部分历史文档错误标注为 "1.77 稳定"。实际稳定版本为 **1.96.0**。

#### 8. `core::range` 类型族

Rust 1.96.0 补齐了 `core::range` 模块，所有 range 类型获得对应的显式迭代器类型：

| `core::range` 类型 | 对应 `std::ops` | 迭代器类型 | 区间语义 |
|:---|:---|:---|:---|
| `Range` | `std::ops::Range` | `RangeIter` | `[start, end)` |
| `RangeFrom` | `std::ops::RangeFrom` | `RangeFromIter` | `[start, ∞)` |
| `RangeToInclusive` | `std::ops::RangeToInclusive` | `RangeToInclusiveIter` | `(-∞, end]` |
| `RangeInclusive` (1.95) | `std::ops::RangeInclusive` | `RangeInclusiveIter` | `[start, end]` |

```rust
use core::range::{Range, RangeFrom, RangeToInclusive};

let r = Range { start: 1, end: 5 };
let sum: i32 = r.into_iter().sum();
assert_eq!(sum, 10);
```

#### 9. `From<T>` for `LazyLock<T, F>` / `LazyCell<T, F>` / `AssertUnwindSafe<T>`

```rust
use std::sync::LazyLock;
use std::cell::LazyCell;
use std::panic::AssertUnwindSafe;

// 直接从值构造
static NAME: LazyLock<String> = LazyLock::from("default".to_string());
let cell: LazyCell<Vec<u8>> = LazyCell::from(vec![1, 2, 3]);
let safe: AssertUnwindSafe<i32> = AssertUnwindSafe::from(42);
```

#### 9a. `LazyLock` / `LazyCell` 访问器方法 (`get`, `get_mut`, `force_mut`)

Rust 1.96 为 `LazyLock` 和 `LazyCell` 新增了无锁/可变访问器，优化热路径性能：

```rust
use std::sync::LazyLock;
use std::cell::LazyCell;

static CFG: LazyLock<String> = LazyLock::new(|| "config".to_string());

// get() — 无锁检查，若未初始化返回 None（热路径优化）
if let Some(val) = LazyLock::get(&CFG) {
    println!("已初始化: {}", val);
}

// get_mut() — 获取可变引用（仅当当前线程独有时可用）
let mut cell: LazyCell<i32> = LazyCell::new(|| 42);
*LazyCell::get_mut(&mut cell).unwrap() += 1;

// force_mut() — 强制初始化并获取可变引用
let val = LazyCell::force_mut(&mut cell);
*val = 100;
```

#### 10. `NonZero` 整数范围迭代

```rust
use std::num::NonZeroU32;

let start = NonZeroU32::new(1).unwrap();
let end = NonZeroU32::new(5).unwrap();

for nz in start..end {
    println!("{}", nz.get()); // 1, 2, 3, 4
}
```

---

### Rustdoc 改进

> **[来源: Rustdoc Documentation](https://doc.rust-lang.org/rustdoc/)**

| 改进 | 说明 | 影响 |
|:---|:---|:---|
| Deprecation notes 渲染方式变更 | 弃用说明现在像普通文档一样渲染，不再使用 `white-space: pre-wrap` 和剥离 `<p>` 标签。多行弃用说明如需换行，请使用标准 Markdown 方法 `" \n"`（两个空格 + 换行） | 文档可视化更可预测 |
| `missing_doc_code_examples` lint | 不再在 impl items 上触发此 lint | 减少误报 |
| Sidebar 分离 | 方法和关联函数在侧边栏中分开显示 | 导航更清晰 |

### Cargo 变更

> **[来源: Cargo Documentation](https://doc.rust-lang.org/cargo/)**

#### 11. Git + Alternate Registry 共存

```toml
[dependencies]
my-crate = { git = "https://github.com/example/my-crate", registry = "corp" }
```

本地使用 git 版本，发布时使用 registry 版本。

#### 12. `target.'cfg(..)'.rustdocflags`

Cargo 1.96 支持按目标条件配置 `rustdoc` 标志，此前只能通过 `RUSTDOCFLAGS` 环境变量全局设置。

**基础示例**：仅在 Unix 平台上启用 `docsrs` 条件编译

```toml
[target.'cfg(unix)']
rustdocflags = ["--cfg", "docsrs"]
```

**实际应用场景**：

| 场景 | 配置 | 说明 |
|:---|:---|:---|
| 跨平台文档特性门控 | `[target.'cfg(windows)'].rustdocflags = ["--cfg", "windows_doc"]` | Windows 专属 API 仅在 Windows 目标下出现在文档中 |
| docs.rs 风格平台标注 | `[target.'cfg(unix)'].rustdocflags = ["--cfg", "docsrs"]` | 配合 `#[cfg(docsrs)]` 控制文档专用特性标注 |
| 自定义 CSS/JS 注入 | `rustdocflags = ["--html-in-header", "custom.html"]` | 按目标注入分析脚本或样式 |
| 内部项目文档搜索 | `rustdocflags = ["--extern-html-root-url", "crate_name=https://internal.docs/crate_name"]` | 为内部 crate 指定文档根 URL |

**与 `RUSTDOCFLAGS` 环境变量的优先级**：

```bash
# 环境变量优先级高于 cargo 配置
RUSTDOCFLAGS="--cfg custom" cargo doc
```

Cargo 配置中的 `rustdocflags` 与 `RUSTDOCFLAGS` **合并**而非覆盖，但环境变量的标志在命令行中更靠后，可能覆盖同名配置。

#### 13. 安全修复：CVE-2026-5222 / CVE-2026-5223

修复了 Cargo 两个安全漏洞：CVE-2026-5222（sparse registry URL 规范化错误，`.git` 后缀剥离，影响 1.68–1.95）和 CVE-2026-5223（tarball symlink 缓存覆盖，第三方注册表有风险，crates.io 不受影响）。

---

### 编译器改进

> **[来源: Rust Compiler Documentation](https://doc.rust-lang.org/rustc/)**

| 改进 | 说明 |
|:---|:---|
| LoongArch Linux link relaxation | 龙芯架构启用链接松弛优化 |
| `riscv64gc-unknown-fuchsia` RVA22 + vector | RISC-V Fuchsia 目标基线提升至 RVA22 |
| `unused_features` lint | 恢复/新增 lint，警告未使用的 `#![feature(...)]` |

### 平台支持

> **[来源: Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)**

| 目标 | 变更 |
|:---|:---|
| `loongarch64-unknown-linux-gnu` | Link relaxation 启用 |
| `riscv64gc-unknown-fuchsia` | 基线提升至 RVA22 + vector |
| `s390x-unknown-linux-gnu` | 向量寄存器内联汇编支持 |

### 兼容性注意

> **[来源: Rust Reference](https://doc.rust-lang.org/reference/)**

| 变更 | 影响范围 |
|:---|:---|
| `#[repr(Int)]` enum layout 修复 | 涉及 uninhabited ZST 字段的边缘情况 |
| 禁止 `Pin<Foo>` unsize-coerce（Foo 不实现 `Deref`） | 此前错误允许的 coercion |
| `#![reexport_test_harness_main]` 被正确 gate | 意外稳定属性的限制 |
| RPITIT 类型过严报错 | 过于私有的返回类型 |
| `uninhabited_static` deny-by-default | 依赖项中的 static uninhabited 类型 |
| 移除 `-Csoft-float` | 改用 `target-feature` |
| `use S::{self as Other}` 禁止 | `{self}` 要求模块父级 |
| 重复属性首项优先 | `export_name`/`link_name`/`link_section` |
| 最低外部 LLVM 升至 21 | 构建 rustc 的 LLVM 要求 |
| `avr` 目标 `c_double` 为 `f32` | 匹配 AVR 上 C 的 double 宽度 |

---

## 项目覆盖映射表

> **[来源: 本项目内部跟踪]**

| 1.96 特性 | 概念文档 | Crate 代码示例 | 测试 |
|:---|:---|:---:|:---:|
| `assert_matches!` | `concept/02_intermediate/05_assert_matches.md` | `c02_type_system` | ✅ 183 passed |
| `core::range::*` | `concept/02_intermediate/06_range_types.md` | `c02_type_system` | ✅ |
| `NonZero` 范围迭代 | `concept/02_intermediate/06_range_types.md` | `c02_type_system` | ✅ |
| `From<T>` for cell types | `concept/02_intermediate/08_interior_mutability.md` | `c02_type_system` | ✅ |
| `ManuallyDrop` 常量模式 | `concept/02_intermediate/03_memory_management.md` | `c02_type_system` | ✅ |
| `expr` metavariable to `cfg` | `concept/03_advanced/04_macros.md` | `c11_macro_system` | ✅ 97 passed |
| Never 类型 tuple coercion | `concept/02_intermediate/02_generics.md` | `c02_type_system` | ✅ |
| Cargo Git + registry 共存 | `docs/06_toolchain/06_19_rust_1_96_features.md` | — | 文档 |
| Cargo `target.cfg.rustdocflags` | `docs/06_toolchain/06_19_rust_1_96_features.md` | — | 文档 |

## 与 1.95 特性对比

> **[来源: Rust Release Tracking](https://releases.rs/)**

| 特性 | 1.95 | 1.96 |
|:---|:---|:---|
| `if let` guards | ✅ 已稳定 | ✅ 已稳定 |
| `assert_matches!` | ❌ 不稳定 | ✅ **稳定** |
| `core::range::Range` / `RangeFrom` / `RangeToInclusive` | ❌ 不稳定 | ✅ **稳定** |
| `From<T>` for `LazyLock` / `LazyCell` | ❌ 不存在 | ✅ **新增** |
| `NonZero` 范围迭代 | ❌ 不支持 | ✅ **新增** |
| `expr` metavariable to `cfg` | ❌ 不支持 | ✅ **新增** |
| `ManuallyDrop` 常量模式 | ❌ 回归 | ✅ **修复** |
| Never 类型 tuple coercion | ❌ 不完整 | ✅ **完善** |

---

## 🔗 参考资源

- [Rust 1.96.0 Official Release Notes](https://github.com/rust-lang/rust/issues/156512)
- [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)
- [Cargo 1.96 CHANGELOG](https://doc.rust-lang.org/stable/cargo/CHANGELOG.html)
- [Rust 1.95 特性速查表](../02_reference/quick_reference/02_rust_195_features_cheatsheet.md)
- [Rust 1.96 知识层文档](../../knowledge/06_ecosystem/emerging/05_rust_1_96.md)
- [Rust 1.97 特性速查表](../02_reference/quick_reference/02_rust_197_features_cheatsheet.md)
- [Rust 版本跟踪](../../concept/07_future/05_rust_version_tracking.md)

---

> **权威来源**: [GitHub rust-lang/rust #156512](https://github.com/rust-lang/rust/issues/156512), [releases.rs](https://releases.rs/docs/1.96.0/)
>
> **权威来源对齐变更日志**: 2026-05-29 全面重写 1.96 部分，删除未进入 stable 的虚假特性（`truncate_front`、`int_format_into`、`RefCell::try_map`、`proc_macro_value` 等），补充实际稳定内容 [来源: Official Release Notes]

**文档版本**: 2.1
**对应 Rust 版本**: 1.96.0 (Stable) / 1.95.0 回顾
**最后更新**: 2026-05-29
**状态**: ✅ 已与官方 Release Notes (#156512) 逐条核对
