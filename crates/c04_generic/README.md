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

## 相关文档

- [Rust Book - Generics](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Rust Reference - GAT](https://blog.rust-lang.org/2022/10/28/gats-stabilization.html)
