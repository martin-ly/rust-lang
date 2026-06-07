# Inline Const Pattern Preview
>
> **EN**: Inline Const Pattern Preview (Chinese)
> **Summary**: ```rust,ignore fn main() { let x = 42; match x { // ❌ 编译错误: 当前稳定 Rust 不支持 const 块 in pattern // const { 40 + 2 } => println!("forty-two"), _ => println!("other"), } // 正确: 使用字面量或 const item const ANSWER: i32 = 42; match x { ANSWER => println!("forty-two"), _ => println!("other"), } }``` | 定理 | 前提 |
>
> **状态**: 🧪 Nightly 实验性
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **A** — Application
> **双维定位**: F×App — 应用 const 块于模式匹配
> **前置依赖**: [Const Generics](../02_intermediate/02_generics.md) · [Pattern Matching](../01_foundation/07_control_flow.md)
> **后置延伸**: [Const Trait](./17_const_trait_preview.md)
> **来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [RFC 2920](https://rust-lang.github.io/rfcs/2920-inline-const.html)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链

## 10.4 边界测试：`const {}` 块在 pattern 中的使用（编译错误/未来特性）

```rust,ignore
fn main() {
    let x = 42;
    match x {
        // ❌ 编译错误: 当前稳定 Rust 不支持 const 块 in pattern
        // const { 40 + 2 } => println!("forty-two"),
        _ => println!("other"),
    }

    // 正确: 使用字面量或 const item
    const ANSWER: i32 = 42;
    match x {
        ANSWER => println!("forty-two"),
        _ => println!("other"),
    }
}
```

> **修正**: **Inline const patterns**（`const { expr }` in patterns）允许在 match arm 中直接写常量表达式：
>
> 1) `match x { const { 1 + 1 } => ... }` — 编译期计算；
> 2) 避免定义单独的 `const` item；
> 3) 适用于复杂常量（如位运算、数组长度）。
>
> 相关特性：
>
> 1) **Inline const**（稳定于 1.79）：`let x: [u8; const { 1 + 1 }] = [0; 2]`；
> 2) **Const blocks in patterns**（开发中）：将 inline const 扩展到 pattern 位置。
>
> 使用场景：
>
> 1) 复杂的 match 条件；
> 2) 从其他常量派生的常量；
> 3) 类型级计算的结果用于值级匹配。
>
> 这与 C++ 的 `constexpr`（可在编译期计算，但不支持在 switch case 中使用复杂表达式）或 C 的 `case`（仅支持整型常量表达式）不同——Rust 的 `const {}` 更灵活，支持任意编译期可计算的 Rust 代码。
> [来源: [Inline Const RFC](https://rust-lang.github.io/rfcs/2920-inline-const.html)] ·
> [来源: [Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)]
>
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Inline Const Pattern Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| Inline Const Pattern Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Inline Const Pattern Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Inline Const Pattern Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Inline Const Pattern Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Inline Const Pattern Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Inline Const Pattern Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Inline Const Pattern Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
