# TAIT Preview
> **受众**: [专家]
> **内容分级**: [实验级]


> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析 TAIT 的类型系统影响
> **前置依赖**: [Generics](../02_intermediate/02_generics.md) · [Trait](../02_intermediate/01_traits.md)
> **后置延伸**: [RPITIT](./15_rpitit_preview.md)

> **来源**: [Rust Reference — Type Aliases](https://doc.rust-lang.org/reference/items/type-aliases.html) · [RFC 2515](https://rust-lang.github.io/rfcs/2515-type_alias_impl_trait.html)

### 10.4 边界测试：TAIT（Type Alias Impl Trait）的递归类型限制（编译错误）

```rust,compile_fail
// 概念代码: TAIT 允许类型别名使用 impl trait
type Recursive = impl std::fmt::Display;

fn make_recursive() -> Recursive {
    // ❌ 编译错误: TAIT 的 concrete type 必须是"确定"的
    // 递归类型（如包含自身）不被允许
    "hello"
}

fn main() {}
```

> **修正**: **TAIT**（Type Alias Impl Trait，稳定于 1.75）允许：1) `type MyIter = impl Iterator<Item = i32>;` — 类型别名隐藏具体类型；2) 模块边界抽象（库内部使用具体类型，外部只看到 trait bound）；3) 与 GAT 结合实现复杂类型关系。限制：1) TAIT 只能出现在**模块级**（不能在函数内部）；2) concrete type 必须能从所有使用点**唯一确定**；3) 不支持递归（infinite type）。应用场景：1) 库 API 隐藏实现细节；2) 复杂泛型代码的类型简化；3) 与 `impl Trait` 返回类型配合。这与 Haskell 的 `type` synonym（完全透明，不隐藏实现）或 OCaml 的 `module type`（模块签名抽象，类似但不同粒度）不同——Rust 的 TAIT 是类型系统的精确抽象机制。[来源: [TAIT Tracking Issue](https://github.com/rust-lang/rust/issues/63063)] · [来源: [Type Alias Impl Trait](https://rust-lang.github.io/rfcs/2515-type_alias_impl_trait.html)]
