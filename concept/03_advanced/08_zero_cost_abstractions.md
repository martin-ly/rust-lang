
### 10.4 边界测试：虚函数表（vtable）与动态分发的性能成本（运行时开销）

```rust,ignore
trait Drawable {
    fn draw(&self);
}

struct Circle;
impl Drawable for Circle {
    fn draw(&self) { println!("circle"); }
}

fn main() {
    let shape: &dyn Drawable = &Circle;
    shape.draw();
    // ❌ 概念问题: &dyn Trait 使用虚函数表，有间接调用开销
    // 与泛型（静态分发，零成本）不同
}
```

> **修正**: **动态分发**（`dyn Trait`）的性能成本：1) **vtable 查找** — 两次间接（指针 → vtable → 函数）；2) **缓存不友好** — vtable 可能不在 CPU cache line 中；3) **内联失败** — 编译器无法内联虚函数调用。`dyn Trait` 的适用场景：1) 异构集合（`Vec<Box<dyn Drawable>>`）；2) 递归类型（如 AST 节点）；3) 插件系统（运行时加载）。优化：1) 用泛型替代（`fn draw<T: Drawable>(shape: &T)`）— 静态分发、内联优化；2) `enum` 替代（`enum Shape { Circle(...), Rect(...) }`）—  tagged union，无 vtable；3) `SmallVec` 或 `ThinVec` — 减少指针间接。测量工具：`cargo bench` + `criterion` 对比泛型 vs dyn。这与 C++ 的虚函数（同样 vtable 开销）或 Java 的接口（JIT 可能去虚拟化，但不保证）不同——Rust 的 `dyn` 是显式的、有成本的抽象，泛型是零成本的默认选择。[来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)] · [来源: [Zero-Cost Abstractions](https://doc.rust-lang.org/book/ch10-01-syntax.html)]
