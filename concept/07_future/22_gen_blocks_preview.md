# Gen Blocks Preview
> **受众**: [专家]
> **内容分级**: [实验级]


> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **A** — Application
> **双维定位**: F×App — 应用 gen 块构建迭代器
> **前置依赖**: [Iterator](../02_intermediate/15_iterator_patterns.md) · [Async](../03_advanced/02_async.md)
> **后置延伸**: [Async Gen](./15_gen_blocks_preview.md)

> **来源**: [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)

### 10.4 边界测试：`gen` block 与 `async gen` 的类型推断（编译错误/未来特性）

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

> **修正**: **`gen` block** 是 Rust generator 生态的关键扩展：1) `gen { yield expr; }` — 创建 `impl Iterator` 的生成器；2) `async gen { yield expr; }` — 创建 `impl AsyncIterator`；3) 语法类似 Python 的 `yield`（generator function）或 JavaScript 的 `function*`。与当前 `std::ops::Generator`（不稳定）的关系：1) `gen` block 是稳定语法；2) 底层使用 generator trait；3) 目标：替代手动实现 `Iterator` 的繁琐。应用场景：1) 无限序列（斐波那契、素数筛）；2) 树遍历（yield 节点）；3) 流处理（yield 数据块）。这与 Python 的 generator（`yield` 创建 generator object）或 C# 的 `yield return`（编译器状态机转换）类似——Rust 的 `gen` block 是编译器转换的状态机，零成本抽象。[来源: [Gen Blocks RFC](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)] · [来源: [Generator Tracking](https://github.com/rust-lang/rust/issues/43122)]
