# Generator Blocks（gen）预览

> **代码状态**: [综述级 — 待补充代码]
>
> **EN**: Generator Blocks (gen) Preview
> **Summary**: Preview of generator blocks as a language-level lazy iteration construct.
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **A** — Application
> **双维定位**: F×App — 应用 gen 块构建迭代器（Iterator）
> **前置依赖**: [Iterator](../02_intermediate/15_iterator_patterns.md) · [Async](../03_advanced/02_async.md)
> **后置延伸**: [Async Gen](./15_gen_blocks_preview.md)
> **来源**: [RFC 3513 — Gen Blocks](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) · [Tracking Issue #117078](https://github.com/rust-lang/rust/issues/117078)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 10.4 边界测试：`gen` block 与 `async gen` 的类型推断（编译错误/未来特性）

```rust,ignore
// 概念代码: gen block（提案中，与 generator 相关）
// let iter = gen {
//     yield 1;
//     yield 2;
// };

// ❌ 编译错误: gen block 不是当前稳定特性
// 它是 generator 的语法糖，用于创建惰性迭代器

fn main() {}
```

> **修正**:
> **`gen` block** 是 Rust generator 生态的关键扩展：
>
> 1) `gen { yield expr; }` — 创建 `impl Iterator` 的生成器；
> 2) `async gen { yield expr; }` — 创建 `impl AsyncIterator`；
> 3) 语法类似 Python 的 `yield`（generator function）或 JavaScript 的 `function*`。
>
> 与当前 `std::ops::Generator`（不稳定）的关系：
>
> 1) `gen` block 是稳定语法；
> 2) 底层使用 generator trait；
> 3) 目标：替代手动实现 `Iterator` 的繁琐。
>
> 应用场景：
>
> 1) 无限序列（斐波那契、素数筛）；
> 2) 树遍历（yield 节点）；
> 3) 流处理（yield 数据块）。
>
> 这与 Python 的 generator（`yield` 创建 generator object）或 C# 的 `yield return`（编译器状态机转换）类似——Rust 的 `gen` block 是编译器转换的状态机，零成本抽象（Zero-Cost Abstraction）。
> [来源: [Gen Blocks RFC](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)] ·
> [来源: [Tracking Issue #117078 — `gen` blocks and functions](https://github.com/rust-lang/rust/issues/117078)] ·
> [来源: [Generator Tracking #43122](https://github.com/rust-lang/rust/issues/43122)]

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Gen Blocks Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| Gen Blocks Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Gen Blocks Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Gen Blocks Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Gen Blocks Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Gen Blocks Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Gen Blocks Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Gen Blocks Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。

## 嵌入式测验（Embedded Quiz）

### 测验 1：`gen` 块与 `async` 块有什么相似之处？（理解层）

**题目**: `gen` 块与 `async` 块有什么相似之处？

<details>
<summary>✅ 答案与解析</summary>

两者都是惰性计算的语法糖，编译为状态机。`async` 返回 `Future`，`gen` 返回 `Iterator`（或更一般的 `Generator`）。
</details>

> **前置概念**: N/A
---

### 测验 2：`gen` 块中的 `yield` 与 Python/JavaScript 的 `yield` 有什么区别？（理解层）

**题目**: `gen` 块中的 `yield` 与 Python/JavaScript 的 `yield` 有什么区别？

<details>
<summary>✅ 答案与解析</summary>

语义相似：暂停执行并返回值给调用者。Rust 的 `yield` 编译为状态机转移，保证内存安全（Memory Safety）（无悬垂引用（Reference））。
</details>

---

### 测验 3：`gen` 块对 `Stream` 的实现有什么帮助？（理解层）

**题目**: `gen` 块对 `Stream` 的实现有什么帮助？

<details>
<summary>✅ 答案与解析</summary>

可以自然地表达异步（Async）流：`gen { yield fetch_page(1).await; }`，比手动实现 `Stream` trait 简洁得多。
</details>

---

### 测验 4：`gen` 块目前的状态是什么？（理解层）

**题目**: `gen` 块目前的状态是什么？

<details>
<summary>✅ 答案与解析</summary>

已在 nightly 中可用（`feature(gen_blocks)`），预计在未来几个版本内稳定化。是 Rust 2024+ 的重要特性。
</details>

---

### 测验 5：`gen` 块与现有迭代器适配器（`map`、`filter`）有什么关系？（理解层）

**题目**: `gen` 块与现有迭代器（Iterator）适配器（`map`、`filter`）有什么关系？

<details>
<summary>✅ 答案与解析</summary>

`gen` 块提供了更灵活、更直观的迭代器定义方式，与适配器互补。复杂逻辑用 `gen` 块，简单转换用适配器链。
</details>
