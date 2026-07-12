# C04: 泛型与 Trait 系统

> **抽象编程核心** | **代码复用** | ⭐⭐⭐⭐⭐ 重要性

## 模块职责

本 crate 深入 Rust 的泛型和 Trait 系统：

- **泛型基础**: 函数、结构体、枚举的泛型
- **Trait 高级**: 关联类型、泛型 Trait、Trait 对象
- **边界约束**: where 子句、多重约束
- **GAT**: 泛型关联类型
- **生命周期参数**: 泛型与生命周期的结合

## 目录结构

```
src/
├── lib.rs              # 模块入口
├── bin/
│   └── main.rs         # CLI 可执行文件
├── basic_generics/     # 基础泛型
├── traits/             # Trait 深入
├── advanced_patterns/  # 高级模式
└── gat/                # 泛型关联类型
```

## 主要类型和 Trait

### 泛型约束 Trait

| Trait | 功能 | 示例 |
|-------|------|------|
| `PartialOrd` | 部分有序比较 | `<`, `>`, `<=`, `>=` |
| `Ord` | 全序比较 | 排序、BTree |
| `PartialEq` | 部分相等 | `==`, `!=` |
| `Eq` | 完全相等 | HashMap 键 |
| `Display` | 格式化显示 | `println!` |
| `Debug` | 调试输出 | `{:?}` |
| `Default` | 默认值 | `Default::default()` |
| `Send` | 跨线程传递 | 线程安全 |
| `Sync` | 跨线程共享 | 线程安全 |

### 常用派生宏

| 宏 | 功能 |
|----|------|
| `#[derive(Clone)]` | 实现 Clone trait |
| `#[derive(Copy)]` | 实现 Copy trait |
| `#[derive(Debug)]` | 实现 Debug trait |
| `#[derive(Default)]` | 实现 Default trait |
| `#[derive(PartialEq, Eq)]` | 实现相等比较 |
| `#[derive(PartialOrd, Ord)]` | 实现排序比较 |
| `#[derive(Hash)]` | 实现 Hash trait |

## 使用示例

### 泛型结构体与实现

```rust
struct Point<T, U> {
    x: T,
    y: U,
}

// 为所有类型实现
impl<T, U> Point<T, U> {
    fn x(&self) -> &T {
        &self.x
    }
}

// 为特定类型实现
impl Point<f32, f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}
```

### 高级 Trait 约束

```rust
use std::fmt::Display;

fn compare_and_print<T, U>(t: &T, u: &U)
where
    T: Display + PartialOrd,
    U: Display + PartialOrd,
{
    if t > u {
        println!("{} > {}", t, u);
    } else {
        println!("{} <= {}", t, u);
    }
}
```

### 泛型关联类型 (GAT)

```rust
trait Container {
    type Item<'a> where Self: 'a;

    fn get<'a>(&'a self) -> Option<Self::Item<'a>>;
}

struct VecContainer<T> {
    items: Vec<T>,
}

impl<T> Container for VecContainer<T> {
    type Item<'a> = &'a T where T: 'a;

    fn get<'a>(&'a self) -> Option<Self::Item<'a>> {
        self.items.first()
    }
}
```

### Trait 对象

```rust
trait Drawable {
    fn draw(&self);
}

struct Button { label: String }
impl Drawable for Button {
    fn draw(&self) { println!("绘制按钮: {}", self.label); }
}

struct SelectBox { options: Vec<String> }
impl Drawable for SelectBox {
    fn draw(&self) { println!("绘制选择框"); }
}

fn draw_all(components: &[Box<dyn Drawable>]) {
    for component in components {
        component.draw();
    }
}
```

## 依赖关系

### 上游依赖

- `c02_type_system`: 类型系统基础
- `common`: 共享工具

### 下游依赖

- `c08_algorithms`: 泛型算法实现
- `c09_design_pattern`: 设计模式应用

### 外部依赖

```toml
[dependencies]
itertools = { workspace = true }
rayon = { workspace = true }
serde = { workspace = true }
anyhow = { workspace = true }
```

## 运行方式

```bash
# 运行测试
cargo test -p c04_generic

# 运行 CLI
cargo run -p c04_generic

# 运行基准测试
cargo bench -p c04_generic
```

## 学习路径建议

1. 掌握基础泛型语法
2. 理解 Trait 作为接口的概念
3. 学习 where 子句编写复杂约束
4. 研究 GAT 的高级用法
5. 理解 Trait 对象 vs 泛型的选择

## 形式化验证示例

本 crate 包含 Kani 泛型函数合约与泛型循环不变量示例，详见 [`src/kani_examples.rs`](src/kani_examples.rs)。
这些示例使用 `#[cfg(kani)]` 保护，仅在运行 `cargo kani` 时编译，不影响常规的 `cargo build/test/check`。

| 示例 | 覆盖内容 |
|:---|:---|
| `find_index` | 泛型切片查找的后置条件（`#[kani::ensures]`） |
| `verify_count_occurrences_generic` | 泛型循环不变量 |
| `clamp` | 带 `Ord` 约束的泛型函数前置/后置条件 |
| `verify_all_positive_prefix_generic` | 泛型循环不变量与全称量词 |

相关概念页：

- [Kani：Rust 有界模型检查器](../../concept/04_formal/04_model_checking/09_kani.md)
- [现代 Rust 验证工具生态（2025-2026）](../../concept/04_formal/04_model_checking/04_modern_verification_tools.md)
- [Generics（泛型系统）](../../concept/02_intermediate/01_generics/01_generics.md)

## 相关文档

- [Rust Book - Generics](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Rust Reference - GAT](https://blog.rust-lang.org/2022/10/28/gats-stabilization.html)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-09
**状态**: ✅ 权威来源对齐完成 (Batch 8) · 新增 Kani 泛型形式化验证示例导航
