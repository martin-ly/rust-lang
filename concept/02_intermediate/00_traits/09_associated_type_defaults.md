# 关联类型默认值（Associated Type Defaults）

> **EN**: Associated Type Defaults
> **Summary**: Associated type defaults allow a trait definition to specify a default type for an associated type, which implementors can override; as of Rust 1.97.0, this feature remains unstable behind the `associated_type_defaults` feature gate.
>
> **受众**: [进阶] / [专家]
> **Bloom 层级**: L3-L4
> **内容分级**: [参考级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **Rust 版本**: nightly only（1.97.0 stable 不支持）
> **最后更新**: 2026-07-16
> **状态**: 不稳定；RFC 2532 已接受，实现与语义收敛中
>
> **前置概念**: [Traits](01_traits.md) · [Type System](../../01_foundation/02_type_system/01_type_system.md) · [Advanced Traits](04_advanced_traits.md) · [Generics](../01_generics/01_generics.md)
> **后置概念**: [Specialization](../../07_future/02_preview_features/31_specialization_preview.md) · [GATs](07_generic_associated_types.md)
>
> **权威来源**:
> · [RFC 2532 — Associated type defaults](https://rust-lang.github.io/rfcs/2532-associated-type-defaults.html) ·
> [Tracking Issue #29661](https://github.com/rust-lang/rust/issues/29661) ·
> [Rust Reference — Associated Types](https://doc.rust-lang.org/reference/items/traits.html#associated-types) ·
> [Rust Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/index.html)

---

> ⚠️ **不稳定特性警告**: 本文件包含 `#![feature(associated_type_defaults)]` 标注的代码示例，需要 **nightly 工具链** 编译。
>
> **使用方式**: `rustup run nightly rustc ...` 或 `cargo +nightly ...`
> **状态查询**: <https://doc.rust-lang.org/nightly/unstable-book/index.html>
> **注意**: 不稳定特性可能在后续版本中变更或移除，生产代码应避免依赖。

---

## 🧠 知识结构图

```mermaid
mindmap
  root((关联类型默认值))
    语法
      trait Foo { type Bar = DefaultType; }
      实现时可省略默认类型
      也可覆盖默认类型
    语义
      默认方法不能假设默认类型
      覆盖后 impl 使用指定类型
    与 Specialization 关系
      默认实现 + 特化覆盖
    限制
      nightly only
      默认类型必须是 well-formed
```

## 📑 目录

- [关联类型默认值（Associated Type Defaults）](#关联类型默认值associated-type-defaults)
  - [🧠 知识结构图](#-知识结构图)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 什么是关联类型默认值](#11-什么是关联类型默认值)
    - [1.2 语法](#12-语法)
    - [1.3 与 Specialization 的关系](#13-与-specialization-的关系)
  - [二、技术细节](#二技术细节)
    - [2.1 默认实现的限制](#21-默认实现的限制)
    - [2.2 覆盖默认类型](#22-覆盖默认类型)
    - [2.3 与泛型参数的对比](#23-与泛型参数的对比)
  - [三、应用场景](#三应用场景)
    - [3.1 渐进式 trait 演进](#31-渐进式-trait-演进)
    - [3.2 默认迭代器类型](#32-默认迭代器类型)
    - [3.3 配置 trait 的默认行为](#33-配置-trait-的默认行为)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 常见错误](#42-常见错误)
  - [五、Stable 替代方案](#五stable-替代方案)
  - [六、来源与延伸阅读](#六来源与延伸阅读)

---

## 一、核心概念

### 1.1 什么是关联类型默认值

在 Rust 中，trait 可以声明**关联类型**（associated type），实现者必须为每个具体类型指定其具体类型：

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

**关联类型默认值** 允许 trait 作者为关联类型指定一个**默认类型**。如果实现者没有显式覆盖，就使用默认值：

```rust
#![feature(associated_type_defaults)]

trait Producer {
    type Output = i32; // 默认类型为 i32
    fn produce(&self) -> Self::Output;
}

struct AlwaysOne;

impl Producer for AlwaysOne {
    // 不覆盖 Output，使用默认值 i32
    fn produce(&self) -> Self::Output {
        1
    }
}

fn main() {
    let p = AlwaysOne;
    let v: i32 = p.produce();
    println!("{}", v);
}
```

这一特性对**向后兼容地扩展 trait** 特别有用：可以在新版本中为新增关联类型提供默认值，而不破坏现有实现。

### 1.2 语法

关联类型默认值的语法是在 trait 定义中为 `type` 项添加 `= Type`：

```rust
#![feature(associated_type_defaults)]

trait Compute {
    type Input = f64;
    type Output = f64;

    fn compute(&self, input: Self::Input) -> Self::Output;
}
```

实现时可以选择覆盖：

```rust
#![feature(associated_type_defaults)]

trait Compute {
    type Input = f64;
    type Output = f64;
    fn compute(&self, input: Self::Input) -> Self::Output;
}

struct IntCompute;

impl Compute for IntCompute {
    type Input = i32;   // 覆盖默认类型
    type Output = i32;  // 覆盖默认类型
    fn compute(&self, input: Self::Input) -> Self::Output {
        input * 2
    }
}

fn main() {}
```

### 1.3 与 Specialization 的关系

关联类型默认值与 **specialization**（特化）密切相关。RFC 2532 的设计目标之一是：

> 默认实现不能假设默认关联类型的具体形态；只有覆盖关联类型的特化实现才能使用更具体的类型信息。

这意味着：

```rust
#![feature(associated_type_defaults)]

trait Transform {
    type Output = Self;
    fn transform(self) -> Self::Output;
}
```

在上述 trait 的默认实现中，方法体不能依赖 `Output = Self` 这一事实做额外假设（例如调用 `Self` 上不存在而 `Output` 上存在的方法）。默认实现只能使用所有可能类型都满足的操作。

---

## 二、技术细节

### 2.1 默认实现的限制

RFC 2532 的关键设计决策是：

> **默认方法不能假设默认关联类型的等式。**

即，在 trait 的默认方法体中，不能把 `Self::Output` 当作默认类型来用，除非该默认类型满足所需 bound。

```rust
#![feature(associated_type_defaults)]

trait Foo {
    type Output = i32;

    // 默认实现只能使用 Output 上所有可能类型都支持的运算
    fn default_method(&self) -> Self::Output {
        // 错误：不能假设 Output 支持 +，除非 trait bound 中有 Add
        // self.get() + 1
        todo!()
    }

    fn get(&self) -> Self::Output;
}

fn main() {}
```

这一限制避免了默认实现因假设默认类型而在被覆盖后产生类型错误。

### 2.2 覆盖默认类型

当实现者覆盖默认关联类型时，必须保证新类型满足 trait 中对该关联类型的所有 bound：

```rust
#![feature(associated_type_defaults)]

use std::fmt::Display;

trait Render {
    type Output: Display = String;
    fn render(&self) -> Self::Output;
}

struct MyRenderer;

impl Render for MyRenderer {
    type Output = i32; // i32: Display 成立
    fn render(&self) -> Self::Output {
        42
    }
}

fn main() {}
```

如果覆盖类型不满足 bound，编译器会报错。

### 2.3 与泛型参数的对比

| 特性 | 关联类型默认值 | 泛型参数默认值 |
|---|---|---|
| 声明位置 | trait 内部 | struct / enum / fn / trait |
| 调用时显式指定 | 通常不指定（由 impl 决定） | 可省略，使用默认值 |
| 与 impl 的关系 | 每个 impl 可覆盖 | 每个使用点可覆盖 |
| 稳定性 | nightly | stable（泛型默认值已稳定） |

示例对比：

```rust
// 泛型参数默认值（stable）
struct Buffer<T = u8>(Vec<T>);

// 关联类型默认值（nightly）
#![feature(associated_type_defaults)]
trait Processor {
    type Item = u8;
}
```

---

## 三、应用场景

### 3.1 渐进式 trait 演进

假设一个已稳定的 trait 需要新增关联类型。如果没有默认值，所有现有实现都会破坏：

```rust
#![feature(associated_type_defaults)]

trait OldTrait {
    fn work(&self);
}

// 新版本：新增关联类型并给默认值，保持向后兼容
trait OldTrait {
    type Config = (); // 默认配置为空元组
    fn work(&self);
    fn configure(&self, _cfg: Self::Config) {}
}

fn main() {}
```

### 3.2 默认迭代器类型

在自定义集合 trait 中，可以为迭代器关联类型提供默认实现：

```rust
#![feature(associated_type_defaults)]

trait Iterable {
    type Item;
    type Iter: Iterator<Item = Self::Item> = std::vec::IntoIter<Self::Item>;

    fn iter(&self) -> Self::Iter;
}

fn main() {}
```

> 注意：当前 nightly 实现可能对此复杂场景支持有限，需以实际编译为准。

### 3.3 配置 trait 的默认行为

```rust
#![feature(associated_type_defaults)]

trait Strategy {
    type Config = DefaultConfig;
    fn execute(&self, cfg: Self::Config);
}

struct DefaultConfig;

fn main() {}
```

---

## 四、反命题与边界分析

### 4.1 反命题树

```
是否使用关联类型默认值？
├── 是否在 nightly 环境？
│   ├── 否 → 不能用（等待稳定化或使用泛型默认值替代）
│   └── 是 → 继续
├── 是否需要为关联类型提供向后兼容默认值？
│   ├── 否 → 可能不需要
│   └── 是 → 继续
├── 默认实现是否依赖默认类型的具体性质？
│   ├── 是 → 需重新设计（RFC 2532 禁止此假设）
│   └── 否 → 可以使用
└── 覆盖类型是否满足 bound？
    ├── 否 → 编译错误
    └── 是 → 可用
```

### 4.2 常见错误

| 错误 | 示例 | 说明 |
|---|---|---|
| 在 stable 使用 | 忘写 `#![feature(associated_type_defaults)]` | 报 E0658 |
| 默认实现假设默认类型 | 在默认方法中调用默认类型特有方法 | 类型检查失败 |
| 覆盖类型不满足 bound | `type Output = ()` 但要求 `Display` | 编译错误 |
| 与 specialization 混淆 | 默认 impl 被特化后类型不一致 | 需遵循 coherence |

---

## 五、Stable 替代方案

由于关联类型默认值 nightly only，stable 代码可用以下替代：

1. **泛型参数默认值**：把可默认的类型移到泛型参数上。
2. **辅助 trait + 默认实现**：通过 blanket impl 提供默认行为。
3. **新增 trait 层级**：把新增关联类型放在子 trait 中。

示例：用泛型默认值替代

```rust
trait Compute<Input = f64, Output = f64> {
    fn compute(&self, input: Input) -> Output;
}

struct FloatCompute;
impl Compute for FloatCompute {
    fn compute(&self, input: f64) -> f64 {
        input * 2.0
    }
}

fn main() {}
```

> 注意：trait 泛型默认值与关联类型默认值在表达力上不等价。泛型参数会影响 trait 的对象安全、一致性和使用方式。

---

## 六、来源与延伸阅读

- [RFC 2532 — Associated type defaults](https://rust-lang.github.io/rfcs/2532-associated-type-defaults.html)
- [Tracking Issue #29661](https://github.com/rust-lang/rust/issues/29661)
- [Rust Reference — Associated Types](https://doc.rust-lang.org/reference/items/traits.html#associated-types)
- [Advanced Traits 权威页](04_advanced_traits.md)
- [Specialization 预览页](../../07_future/02_preview_features/31_specialization_preview.md)
