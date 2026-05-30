# Lifetime Capture in `impl Trait` Preview
>
> **受众**: [专家]
> **内容分级**: [实验级]

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析 impl Trait 的生命周期捕获规则
> **前置依赖**: [Lifetime](../01_foundation/03_lifetimes.md) · [Trait](../02_intermediate/01_traits.md)
> **后置延伸**: [RPITIT](./15_rpitit_preview.md)

> **来源**: [Rust Reference — Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) · [RFC 2289](https://rust-lang.github.io/rfcs/2289-associated-type-bounds.html)

### 10.4 边界测试：impl trait 的精确 lifetime capture（编译错误/未来特性）

```rust,ignore
fn make_iter<'a>(s: &'a str) -> impl Iterator<Item = char> + 'a {
    s.chars()
}

// ❌ 编译错误: impl trait 默认 capture 所有输入 lifetime
// 若需精确控制 capture 哪些 lifetime，当前语法有限制

// 未来语法（提案）:
// fn make_iter<'a>(s: &'a str) -> impl Iterator<Item = char> + use<'a> {
//     s.chars()
// }

fn main() {}
```

> **修正**: **Precise capturing**（`use<'lt>` syntax）是 Rust 2024 edition 的关键特性：1) 当前 `impl Trait` 捕获所有输入 lifetime（即使未使用），导致不必要的 lifetime 绑定；2) `use<'a>` 精确声明只捕获 `'a`，其他 lifetime 不隐式捕获；3) 减少 lifetime 传播，使 API 更灵活。应用场景：1) 返回迭代器但只借用部分输入；2) 闭包捕获部分环境；3) 复杂嵌套的 lifetime 关系简化。这与 TypeScript 的泛型（默认全部捕获，无精确控制）或 Swift 的 `@escaping`（控制闭包捕获，但不精确到 lifetime）不同——Rust 的 `use<>` 是类型系统的精确性扩展，解决 impl trait 的 lifetime 泄露问题。[来源: [Precise Capturing RFC](https://rust-lang.github.io/rfcs/3498-lifetime-capture-in-impl-trait.html)] · [来源: [Rust 2024 Edition](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)]
