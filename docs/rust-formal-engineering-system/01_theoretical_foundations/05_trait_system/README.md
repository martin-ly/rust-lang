# Trait 系统理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [trait_system_formalization.md](../../../research_notes/type_theory/trait_system_formalization.md)

[返回主索引](../../00_master_index.md)

---

## Trait 作为类型类

Rust 的 Trait 系统受 Haskell 类型类启发：

```rust
// 定义 Trait（类型类）
trait Drawable {
    fn draw(&self);
    fn bounds(&self) -> (i32, i32, i32, i32);
}

// 为类型实现 Trait
struct Circle {
    x: i32, y: i32, radius: i32,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle at ({}, {})", self.x, self.y);
    }

    fn bounds(&self) -> (i32, i32, i32, i32) {
        (self.x - self.radius, self.y - self.radius,
         self.x + self.radius, self.y + self.radius)
    }
}

// 泛型约束（类型类约束）
fn render<T: Drawable>(item: &T) {
    item.draw();
}

// 多 Trait 约束
fn process<T: Drawable + Clone + Send>(item: &T) {
    let copy = item.clone();
    item.draw();
    drop(copy);
}
```

## 关联类型

```rust
// 关联类型：每个实现可以指定自己的类型
trait Iterator {
    type Item;  // 关联类型
    fn next(&mut self) -> Option<Self::Item>;
}

struct Counter { count: u32 }

impl Iterator for Counter {
    type Item = u32;  // 实现时指定

    fn next(&mut self) -> Option<u32> {
        self.count += 1;
        if self.count < 6 { Some(self.count) } else { None }
    }
}

// 泛型 vs 关联类型
// 泛型：外部选择类型（Vec<T> 用户可以选 T）
// 关联类型：实现者选择类型（Iterator::Item 由实现决定）
```

## Trait 对象与动态分发

```rust
// 静态分发（单态化）
fn static_dispatch<T: Drawable>(item: &T) {
    item.draw();  // 编译时确定调用哪个 draw
}

// 动态分发（Trait 对象）
fn dynamic_dispatch(item: &dyn Drawable) {
    item.draw();  // 运行时通过 vtable 查找
}

// 使用示例
fn demo() {
    let circle = Circle { x: 0, y: 0, radius: 10 };

    static_dispatch(&circle);  // 编译时展开
    dynamic_dispatch(&circle); // 运行时分发

    // 异构集合
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { x: 0, y: 0, radius: 10 }),
        // Box::new(Rectangle { ... }),
    ];
}
```

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Trait 系统形式化 | Trait 系统的完整形式化 | [../../../research_notes/type_theory/trait_system_formalization.md](../../../research_notes/type_theory/trait_system_formalization.md) |
| 类型系统基础 | 类型理论基础 | [../../../research_notes/type_theory/type_system_foundations.md](../../../research_notes/type_theory/type_system_foundations.md) |
