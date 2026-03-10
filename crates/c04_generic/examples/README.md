# C04 泛型编程 - 示例中心

> **创建日期**: 2025-10-22
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 泛型是 Rust 零成本抽象的基石，本示例集展示从基础泛型语法到高级特性（GAT、HRTB、特化）的完整技术栈。

---

## 示例概览

本目录包含 **15+ 个核心示例**，涵盖泛型编程的所有重要主题：

- ✅ 泛型函数与结构体
- ✅ Trait 定义与实现
- ✅ Trait 约束与边界
- ✅ 泛型关联类型 (GAT)
- ✅ 高阶 Trait 边界 (HRTB)
- ✅ 类型状态模式
- ✅ Rust 1.93.0 新特性

---

## 示例分类导航

### 基础示例 ⭐

适合了解 Rust 泛型基础的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `generics_basics.rs` | 泛型基础 | `<T>` 语法 | `cargo run --example generics_basics` |
| `traits_basics.rs` | Trait 基础 | trait 定义与实现 | `cargo run --example traits_basics` |
| `trait_bounds.rs` | Trait 约束 | where 子句 | `cargo run --example trait_bounds` |
| `generic_functions.rs` | 泛型函数 | 单态化 | `cargo run --example generic_functions` |
| `generic_structs.rs` | 泛型结构体 | `Vec<T>`、`Option<T>` | `cargo run --example generic_structs` |

### 进阶示例 ⭐⭐

适合需要深入理解泛型系统的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `advanced_generics.rs` | 高级泛型 | 关联类型、默认类型 | `cargo run --example advanced_generics` |
| `trait_objects.rs` | Trait 对象 | `dyn Trait` | `cargo run --example trait_objects` |
| `generic_lifetimes.rs` | 泛型与生命周期 | `T: 'a` | `cargo run --example generic_lifetimes` |
| `blanket_impls.rs` | 全覆盖实现 | `impl<T> Trait for T` | `cargo run --example blanket_impls` |

### 高级示例 ⭐⭐⭐

适合需要掌握泛型高级特性的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `hrtb.rs` | 高阶 Trait 边界 | `for<'a>` | `cargo run --example hrtb` |
| `specialization.rs` | 特化 | `min_specialization` | `cargo run --example specialization` |
| `gats.rs` | 泛型关联类型 | GAT | `cargo run --example gats` |

### 实战示例 💼

展示泛型在实际场景中的应用。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `generic_collections_demo.rs` | 泛型集合 | 自定义容器 | `cargo run --example generic_collections_demo` |
| `generic_trait_object_demo.rs` | Trait 对象实战 | 动态分发 | `cargo run --example generic_trait_object_demo` |
| `generic_type_state_demo.rs` | 类型状态模式 | 编译时状态机 | `cargo run --example generic_type_state_demo` |
| `generic_zero_cost_demo.rs` | 零成本抽象 | 性能对比 | `cargo run --example generic_zero_cost_demo` |
| `generic_gat_demo.rs` | GAT 实战 | 借用迭代器 | `cargo run --example generic_gat_demo` |
| `generic_hrtb_demo.rs` | HRTB 实战 | 高阶约束 | `cargo run --example generic_hrtb_demo` |
| `generic_specialization_demo.rs` | 特化实战 | 性能优化 | `cargo run --example generic_specialization_demo` |

### Rust 1.93.0 特性示例 ⭐ NEW

展示最新 Rust 版本的泛型相关改进。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rust_192_features_demo.rs` | Rust 1.93.0 特性演示 | 关联项多边界、迭代器特化 | `cargo run --example rust_192_features_demo` |
| `rust_191_features_demo.rs` | Rust 1.91 特性演示 | 类型推断优化 | `cargo run --example rust_191_features_demo` |
| `rust_190_real_generics_demo.rs` | 真实泛型示例 | 综合应用 | `cargo run --example rust_190_real_generics_demo` |

---

## 如何运行示例

### 基础运行

```bash
# 进入模块目录
cd crates/c04_generic

# 运行泛型基础示例
cargo run --example generics_basics

# 运行 Trait 示例
cargo run --example traits_basics

# 运行高级泛型示例
cargo run --example advanced_generics
```

### 运行实战示例

```bash
# 类型状态模式（强烈推荐）
cargo run --example generic_type_state_demo

# GAT 实战
cargo run --example generic_gat_demo

# 零成本抽象性能对比
cargo run --example generic_zero_cost_demo
```

### 运行测试

```bash
# 运行所有测试
cargo test -p c04_generic

# 运行 Rust 1.93.0 特性测试
cargo test --test rust_192_comprehensive_tests

# 运行模块测试
cargo test --lib rust_192_features
```

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench -p c04_generic

# 运行 Rust 1.93.0 特性基准测试
cargo bench --bench rust_192_benchmarks
```

---

## 学习建议

### 初学者路径 (第1-2周)

1. **学习泛型基础**

   ```bash
   cargo run --example generics_basics
   cargo run --example generic_functions
   cargo run --example generic_structs
   ```

   - 理解 `<T>` 语法
   - 学习泛型函数
   - 掌握泛型结构体

2. **掌握 Trait 系统**

   ```bash
   cargo run --example traits_basics
   cargo run --example trait_bounds
   ```

   - Trait 定义与实现
   - Trait 约束 (`T: Display`)
   - `where` 子句

### 进阶路径 (第3-4周)

1. **理解高级泛型**

   ```bash
   cargo run --example advanced_generics
   cargo run --example trait_objects
   ```

   - 关联类型
   - Trait 对象 (`dyn Trait`)
   - 默认类型参数

2. **学习泛型与生命周期**

   ```bash
   cargo run --example generic_lifetimes
   ```

   - `T: 'a` 约束
   - 生命周期省略规则
   - 复杂生命周期场景

3. **掌握全覆盖实现**

   ```bash
   cargo run --example blanket_impls
   ```

   - `impl<T> Trait for T`
   - 标准库中的 blanket impl

### 高级路径 (第5周+)

1. **探索 GAT**

   ```bash
   cargo run --example gats
   cargo run --example generic_gat_demo
   ```

   - 泛型关联类型
   - 借用迭代器
   - 类型族

2. **学习 HRTB**

   ```bash
   cargo run --example hrtb
   cargo run --example generic_hrtb_demo
   ```

   - `for<'a>` 语法
   - 高阶约束
   - 生命周期抽象

3. **掌握特化**

   ```bash
   cargo run --example specialization
   cargo run --example generic_specialization_demo
   ```

   - `min_specialization`
   - 性能优化
   - 默认实现

4. **Rust 1.93.0 新特性**

   ```bash
   cargo run --example rust_192_features_demo
   ```

   - 关联项的多个边界
   - 迭代器方法特化
   - 改进的类型推断

---

## 关键概念速查

### 泛型函数

```rust
fn identity<T>(value: T) -> T {
    value
}

// 多重约束
fn process<T>(item: T)
where
    T: Display + Clone,
{
    println!("{}", item.clone());
}
```

### 泛型结构体

```rust
struct Point<T, U> {
    x: T,
    y: U,
}

// 为泛型结构体实现方法
impl<T: Add<Output = T>> Point<T, T> {
    fn add(&self, other: &Self) -> Self {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}
```

### Trait 与关联类型

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// 泛型关联类型 (GAT)
trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

### HRTB 示例

```rust
trait Parser<'a> {
    fn parse(&self, input: &'a str) -> Result<&'a str, Error>;
}

fn parse_any<P>(parser: &P, input: &str) -> Result<&str, Error>
where
    P: for<'a> Parser<'a>,
{ /* ... */ }
```

### 类型状态模式

```rust
struct Builder<State> {
    // ...
    _state: PhantomData<State>,
}

struct Uninitialized;
struct Initialized;

impl Builder<Uninitialized> {
    fn new() -> Self { /* ... */ }
    fn init(self) -> Builder<Initialized> { /* ... */ }
}

impl Builder<Initialized> {
    fn build(self) -> Product { /* ... */ }
}
```

---

## 相关文档

### 模块文档

- [模块主页](../README.md) - 完整学习指南
- [文档中心](../docs/README.md) - 详细文档导航
- [主索引](../docs/00_MASTER_INDEX.md) - 文档完整索引
- [术语表](../docs/Glossary.md) - 核心术语
- [FAQ](../docs/FAQ.md) - 常见问题

### 理论文档

- [泛型与 Trait 指南](../docs/README.md)
- [泛型与 Trait 概念族谱](../../../docs/research_notes/GENERICS_TRAITS_MINDMAP.md)
- [多维概念矩阵](../../../docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)

### 外部资源

- [The Rust Book - 泛型](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [The Rust Book - Trait](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Rust  Reference - 泛型](https://doc.rust-lang.org/reference/items/generics.html)
- [Rust  RFC - GAT](https://rust-lang.github.io/rfcs/1598-generic_associated_types.html)

---

## 性能注意事项

```rust
// ✅ 泛型使用单态化，零运行时开销
fn generic_process<T: Process>(item: T) -> Output {
    item.process()
}

// ✅ 但对于大型泛型代码，编译时间会增加
// 考虑使用 impl Trait 减少代码膨胀
fn process_items(items: &[impl Process]) -> Vec<Output> {
    items.iter().map(|i| i.process()).collect()
}

// ✅ Trait 对象有运行时开销 (vtable)
fn dynamic_process(item: &dyn Process) -> Output {
    item.process()  // vtable 查找
}
```

---

*示例基于 Rust 1.94+，Edition 2024*:

[返回模块主页](../README.md) | [返回上级](../README.md)
