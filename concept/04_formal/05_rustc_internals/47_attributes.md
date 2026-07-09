# 属性（Attributes）

> **EN**: Attributes
> **Summary**: Rust 属性系统：内置属性分类（测试、derive、诊断、代码生成、限制、类型系统、调试器）及其在 item、表达式、语句上的应用规则。 Rust attribute system: built-in attribute categories and application rules on items, expressions, and statements.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Items Reference](46_items_reference.md) · [Macros](../../03_advanced/03_proc_macros/04_macros.md)
> **后置概念**: [Conditional Compilation](../../03_advanced/03_proc_macros/28_conditional_compilation.md) · [Derive Traits](../../02_intermediate/00_traits/31_derive_traits.md)
> **定理链**: Attribute → Metadata → Compiler Behavior
>
> **来源**: [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

---

## 认知路径

> **认知路径**: 本节从 "属性（Attributes）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么属性在 Rust 中值得关注？属性是编译期元编程的核心机制，控制代码生成、条件编译、lint 级别和测试标记。
2. **概念建立**: 掌握属性的语法、分类和应用规则。
3. **机制推理**: 通过 ⟹ 定理链将属性元数据与编译器行为串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与属性的适用边界。
5. **迁移应用**: 将属性与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "属性在所有场景下都适用" ⟹ 不成立。某些属性只在特定 item 类型或 nightly 编译器上有效，错误使用会触发编译错误。

> **反命题 2**: "忽略属性的细节也能写出正确代码" ⟹ 不成立。`#[repr(C)]`、`#[must_use]`、`#[non_exhaustive]` 等属性直接影响类型布局和接口语义。

> **反命题 3**: "其他语言对属性的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 属性在词法阶段即被解析并影响宏展开和类型检查，与 C# 注解或 Java 注解的运行时反射模型不同。

## 一、属性语法

属性以 `#[...]`（外层属性）或 `#![...]`（内层属性）形式出现：

- 外层属性作用于其后的 item。
- 内层属性作用于包含它的 item 或 crate。

```bnf
Attribute      ::= "#" "[" Attr "]"
InnerAttribute ::= "#!" "[" Attr "]"
Attr           ::= Path ("=" Literal | "(" TokenTree* ")")?
```

```rust
#![allow(dead_code)] // 内层：作用于当前模块/crate

#[derive(Debug)]     // 外层：作用于结构体
struct Point { x: i32, y: i32 }
```

## 二、属性分类

| 类别 | 主要属性 | 作用 |
|:---|:---|:---|
| 测试 | `#[test]`, `#[bench]`, `#[should_panic]` | 标记测试函数 |
| Derive | `#[derive(Trait)]` | 自动生成 trait 实现 |
| 诊断 | `#[allow]`, `#[warn]`, `#[deny]`, `#[forbid]`, `#[deprecated]` | 控制 lint 与弃用 |
| 代码生成 | `#[inline]`, `#[cold]`, `#[no_mangle]`, `#[repr(...)]` | 影响代码生成 |
| 限制 | `#[allow(...)]`, `#[feature(...)]`（nightly） | 能力开关 |
| 类型系统 | `#[non_exhaustive]`, `#[must_use]` | 影响类型/接口语义 |
| 调试器 | `#[debugger_visualizer]` | 调试器可视化 |
| 运行时 | `#[global_allocator]`, `#[windows_subsystem]` | 运行时行为 |

## 三、属性应用位置

| 位置 | 示例 | 说明 |
|:---|:---|:---|
| Crate | `#![feature(...)]` | 内层属性，作用于整个 crate |
| Module | `#![allow(...)]` | 作用于当前模块 |
| 函数 | `#[test]` | 作用于单个函数 |
| 结构体/枚举 | `#[derive(Debug)]` | 作用于类型定义 |
| 字段 | `#[serde(rename = "...")]` | 作用于结构体字段 |
| 表达式/语句 | 部分属性允许 | 如 `#[allow(unreachable_code)]` |

## 四、常用内置属性速查

| 属性 | 类别 | 作用 |
|:---|:---|:---|
| `#[derive(Trait)]` | 派生 | 自动生成 trait 实现 |
| `#[inline]` | 代码生成 | 建议内联 |
| `#[repr(C)]` | 代码生成 | C 兼容布局 |
| `#[must_use]` | 类型系统 | 忽略返回值时警告 |
| `#[non_exhaustive]` | 类型系统 | 禁止外部 crate 穷尽匹配 |
| `#[deprecated]` | 诊断 | 标记弃用 API |
| `#[cfg(...)]` | 条件编译 | 按条件包含代码 |
| `#[path = "..."]` | 模块 | 指定模块文件路径 |
| `#[no_mangle]` | 代码生成 | 禁用符号名修饰 |
| `#[global_allocator]` | 运行时 | 指定全局分配器 |

## 五、条件编译属性

`#[cfg(...)]` 与 `cfg_attr(...)` 在编译期决定是否包含代码或属性。

```rust
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
struct Data;
```

| 谓词 | 说明 |
|:---|:---|
| `cfg(target_os = "...")` | 目标操作系统 |
| `cfg(target_arch = "...")` | 目标架构 |
| `cfg(feature = "...")` | Cargo feature |
| `cfg(test)` | 测试模式 |
| `cfg(debug_assertions)` | debug 构建 |

详见 [Conditional Compilation](../../03_advanced/03_proc_macros/28_conditional_compilation.md)。

## 四、文档注释

文档注释 `///` 与 `//!` 本质上是 `#[doc = "..."]` 属性的语法糖。

```rust
/// A point in 2D space.
struct Point;
```

等价于：

```rust
#[doc = " A point in 2D space."]
struct Point;
```

## 五、与宏的关系

过程宏（procedural macro）和声明宏（`macro_rules!`）都可生成属性。属性宏在宏展开阶段执行，可读取或替换被装饰的 item。

```rust
#[my_attribute_macro]
fn decorated() {}
```

属性宏接收整个 item 的 token tree，可以：

- 保留原 item 不变。
- 生成额外的 item。
- 完全替换原 item。

## 六、Unsafe 相关属性

| 属性 | 作用 | 示例 |
|:---|:---|:---|
| `#[no_mangle]` | 禁止符号名修饰，用于 FFI | `#[no_mangle] pub extern "C" fn foo() {}` |
| `#[export_name = "..."]` | 显式指定导出符号名 | `#[export_name = "bar"] fn foo() {}` |
| `#[link(name = "...")]` | 链接外部库 | `#[link(name = "openssl")]` |

这些属性经常与 [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) 和 FFI 代码配合使用。

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Items Reference](46_items_reference.md) | 属性修饰 item |
| [Macros](../../03_advanced/03_proc_macros/04_macros.md) | 属性宏在宏展开阶段执行 |
| [Conditional Compilation](../../03_advanced/03_proc_macros/28_conditional_compilation.md) | `#[cfg]` 控制条件编译 |
| [Generics Compiler Behavior](53_generics_compiler_behavior.md) | `#[inline]` 影响单态化代码生成 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | `#[no_mangle]`、`#[link]` 用于 unsafe/FFI 场景 |

---

> **权威来源**: [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) · [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) · [Rust Reference — Derive](https://doc.rust-lang.org/reference/attributes/derive.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
