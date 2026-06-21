# Const Trait Preview

> **代码状态**: [综述级 — 待补充代码]
>
> **EN**: Const Trait Preview
> **Summary**: Preview of const traits for generic compile-time computation.
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价 const trait 的设计权衡
> **前置依赖**: [Trait](../02_intermediate/01_traits.md) · [Const Generics](../02_intermediate/02_generics.md)
> **后置延伸**: [Const Trait Impl](./11_const_trait_impl_preview.md)
> **来源**: [Rust Reference — Const Eval](https://doc.rust-lang.org/reference/const_eval.html) · [RFC 2632](https://github.com/rust-lang/rust/issues/67792)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 10.4 边界测试：const trait 与泛型 const 求值（编译错误/未来特性）

```rust,ignore
// 概念代码: const trait（开发中）
// const trait Compute {
//     const fn compute() -> i32;
// }

// ❌ 编译错误: const trait 不是当前稳定特性
// 它允许在 const context 中使用 trait bounds

fn main() {
    // 当前限制: 不能在 const fn 中使用 trait 方法
    // const fn double<T: std::ops::Add>(x: T) -> T { x + x } // 错误
}
```

> **修正**:
>
> **Const traits** 是 Rust 常量求值的关键扩展：
>
> 1) `~const Trait` 语法标记"可在 const 上下文中使用的 trait"；
> 2) `const impl Trait for Type` 标记实现支持常量求值；
> 3) 目标：在 `const fn` 中使用泛型 trait bound（如 `T: ~const Add`）。
>
> 当前状态：部分实现（nightly `const_trait_impl`）， design 迭代中。
>
> 替代方案：
>
> 1) `macro_rules!` 生成多份代码；
> 2) `min_specialization` 为常量/非常量分别实现；
> 3) 放弃 const，使用运行时计算。
> 这与 C++ 的 `constexpr`（函数可自动在编译期/运行期使用，无需特殊标记）或 D 的 `CTFE`（Compile Time Function Execution，类似但更灵活）不同——Rust 追求显式控制：const 函数有严格的副作用限制，trait 的 const 支持需显式声明。
> [来源: [Const Trait RFC](https://github.com/rust-lang/rust/issues/67792)] ·
> [来源: [Const Generics](https://rust-lang.github.io/rfcs//2000-const-generics.html)]

> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Const Trait Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Const Trait Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Const Trait Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Const Trait Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Const Trait Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Const Trait Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Const Trait Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Const Trait Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。

## 嵌入式测验（Embedded Quiz）

### 测验 1：`const trait` 与 `const fn` 有什么区别？（理解层）

**题目**: `const trait` 与 `const fn` 有什么区别？

<details>
<summary>✅ 答案与解析</summary>

`const fn` 是单个函数可在编译期执行。`const trait` 允许 trait 的方法在常量上下文中使用，使泛型常量代码成为可能。
</details>

---

### 测验 2：为什么 `Vec::new()`  historically 不是 `const fn`？（理解层）

**题目**: 为什么 `Vec::new()`  historically 不是 `const fn`？

<details>
<summary>✅ 答案与解析</summary>

因为 `Vec` 的分配需要堆内存，而常量上下文 historically 不支持分配。`const_mut_refs` 和 `const_heap` 功能逐步放宽限制。
</details>

---

### 测验 3：`~const Trait` 语法是什么意思？（理解层）

**题目**: `~const Trait` 语法是什么意思？

<details>
<summary>✅ 答案与解析</summary>

表示"这个泛型参数可以是 const 或非 const 的 trait 实现"。允许函数同时服务于 const 和运行时上下文。
</details>

---

### 测验 4：`const trait` 对嵌入式开发有什么意义？（理解层）

**题目**: `const trait` 对嵌入式开发有什么意义？

<details>
<summary>✅ 答案与解析</summary>

允许在编译期构造复杂数据结构（如查找表、配置结构），无需运行时初始化代码，减少二进制体积和启动时间。
</details>

---

### 测验 5：这个特性目前的实现状态如何？（理解层）

**题目**: 这个特性目前的实现状态如何？

<details>
<summary>✅ 答案与解析</summary>

已在 nightly 中实验性提供，部分功能（如 `~const`）正在稳定化讨论中。是 Rust 常量求值能力扩展的重要一步。
</details>
