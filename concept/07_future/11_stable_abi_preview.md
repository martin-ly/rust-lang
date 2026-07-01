# Stable ABI Preview

> **代码状态**: [综述级 — 待补充代码]
>
> **EN**: Stable Abi Preview
> **Summary**: Stable Abi Preview: emerging Rust language feature or ecosystem trend.
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析 Rust ABI 稳定性问题
> **前置依赖**: [FFI](../03_advanced/05_rust_ffi.md) · [Unsafe](../03_advanced/03_unsafe.md)
> **后置延伸**: [Rust for Linux](19_rust_for_linux.md)
> **来源**: [Rust Reference — ABI](https://doc.rust-lang.org/reference/items/external-blocks.html) · [RFC 2945](https://rust-lang.github.io/rfcs//2945-c-unwind-abi.html)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 10.4 边界测试：稳定 ABI 与 extern "C" 的符号兼容性（链接错误）

```rust,compile_fail
// Rust 的默认 ABI 不稳定（随编译器版本变化）
#[no_mangle]
pub extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}

// ❌ 链接错误: 若 C 代码按 Rust 默认 ABI 调用（而非 extern "C"）
// C 代码:
// int rust_function(int x); // 声明匹配 extern "C"
// // 但 C++ 的 name mangling 可能与 Rust 的 #[no_mangle] 冲突

fn main() {}
```
> **修正**:
>
> **稳定 ABI** 是 Rust 的长期目标：
>
> 1) 当前 `extern "C"` 是唯一稳定的跨语言 ABI；
> 2) Rust 的默认 ABI（`extern "Rust"`）随编译器版本变化（字段重排、enum 布局优化）；
> 3) `#[repr(C)]` 强制 C 兼容布局，但仍有限制（如 enum 的大小）。
>
> `crabi`（C Rust ABI）提案：
>
> 1) 定义 Rust 类型在 FFI 中的稳定布局；
> 2) 与 C ABI 兼容但支持 Rust 特性（如 panic、trait object）；
> 3) 允许 Rust 动态库跨版本安全链接。
>
> 当前限制：
>
> 1) `String` / `Vec` 不能安全传递（需 `CString` / 原始指针（Raw Pointer））；
> 2) `panic` 跨 FFI 边界是 UB；
> 3) `Drop` 在 FFI 中的行为未定义。这与 C++ 的 ABI（由 Itanium/MSVC 定义，稳定但不跨编译器）或 Swift 的 ABI（稳定但版本锁定）不同——Rust 追求语言级别的稳定 ABI，而非依赖平台约定。
>
> [来源: [crabi Proposal](https://rust-lang.github.io/rfcs//3325-unsafe-attributes.html)] ·
> [来源: [Rust FFI](https://doc.rust-lang.org/nomicon/ffi.html)]
>
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Stable ABI Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| Stable ABI Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Stable ABI Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Stable ABI Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Stable ABI Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Stable ABI Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Stable ABI Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Stable ABI Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。

## 嵌入式测验（Embedded Quiz）

### 测验 1：为什么 Rust 目前没有稳定的 ABI？（理解层）

**题目**: 为什么 Rust 目前没有稳定的 ABI？

<details>
<summary>✅ 答案与解析</summary>

编译器优化（单态化（Monomorphization）、布局优化）可能改变结构体（Struct）和枚举（Enum）的内存布局。稳定 ABI 会限制这些优化，影响性能。
</details>

> **前置概念**: N/A
---

### 测验 2：`repr(C)` 和 `extern "C"` 如何提供稳定的跨语言边界？（理解层）

**题目**: `repr(C)` 和 `extern "C"` 如何提供稳定的跨语言边界？

<details>
<summary>✅ 答案与解析</summary>

`repr(C)` 使用 C 的布局规则，`extern "C"` 使用 C 的调用约定。这是 Rust 与 C/C++ 互操作的标准方式，但不是 Rust 到 Rust 的 ABI。
</details>

---

### 测验 3：Stable ABI 提案对 Rust 的动态链接有什么意义？（理解层）

**题目**: Stable ABI 提案对 Rust 的动态链接有什么意义？

<details>
<summary>✅ 答案与解析</summary>

允许不同编译器版本编译的动态库相互调用。目前 Rust 动态库要求使用相同编译器版本，限制了插件系统和二进制分发。
</details>

---

### 测验 4：稳定 ABI 与性能之间的权衡是什么？（理解层）

**题目**: 稳定 ABI 与性能之间的权衡是什么？

<details>
<summary>✅ 答案与解析</summary>

稳定 ABI 限制编译器优化布局的能力，可能导致更大的结构体（Struct）和更慢的字段访问。需要精心设计以最小化性能损失。
</details>

---

### 测验 5：哪些场景最需要 Rust 的稳定 ABI？（理解层）

**题目**: 哪些场景最需要 Rust 的稳定 ABI？

<details>
<summary>✅ 答案与解析</summary>

插件系统（动态加载扩展）、操作系统接口（驱动 ABI）、闭源库分发、语言服务器协议等长期稳定的接口。
</details>
