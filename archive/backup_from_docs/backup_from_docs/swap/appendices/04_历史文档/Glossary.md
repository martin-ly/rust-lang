# C02 类型系统: 术语表 (Glossary)

> **文档定位**: 类型系统核心术语快速参考  
> **使用方式**: 通过术语索引快速查找定义，理解核心概念  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

## 📊 目录

- [C02 类型系统: 术语表 (Glossary)](#c02-类型系统-术语表-glossary)
  - [📊 目录](#-目录)
  - [📋 术语索引](#-术语索引)
  - [泛型 (Generics)](#泛型-generics)
  - [Trait](#trait)
  - [Trait对象 (Trait Object)](#trait对象-trait-object)
  - [关联类型 (Associated Type)](#关联类型-associated-type)
  - [Newtype 模式](#newtype-模式)
  - [零大小类型 (ZST)](#零大小类型-zst)
  - [PhantomData](#phantomdata)
  - [Never类型 (!)](#never类型-)
  - [Pin](#pin)
  - [类型推导 (Type Inference)](#类型推导-type-inference)
  - [Deref强制转换](#deref强制转换)
  - [孤儿规则 (Orphan Rule)](#孤儿规则-orphan-rule)
  - [协变与逆变](#协变与逆变)
  - [单态化 (Monomorphization)](#单态化-monomorphization)
  - [📚 延伸阅读](#-延伸阅读)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[G](#泛型-generics) | [N](#newtype-模式) | [P](#phantomdata) | [T](#trait) | [Z](#零大小类型-zst)

---

## 泛型 (Generics)

**定义**: 类型参数化，允许代码适用于多种类型。

**语法**:

```rust
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    // ...
}

struct Point<T> {
    x: T,
    y: T,
}

enum Option<T> {
    Some(T),
    None,
}
```

**单态化**: 编译时为每个具体类型生成代码，零成本抽象

**相关**: [03_advanced/01_generics.md](./03_advanced/01_generics.md)

---

## Trait

**定义**: 定义类型的共同行为，类似于其他语言的接口。

**语法**:

```rust
trait Summary {
    fn summarize(&self) -> String;
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}, by {}", self.headline, self.author)
    }
}
```

**Trait Bounds**: 约束泛型类型必须实现特定trait

**相关**: [03_advanced/02_traits.md](./03_advanced/02_traits.md)

---

## Trait对象 (Trait Object)

**定义**: 运行时多态，通过 `dyn Trait` 实现。

**语法**:

```rust
fn print_summary(item: &dyn Summary) {
    println!("{}", item.summarize());
}

let items: Vec<Box<dyn Summary>> = vec![
    Box::new(article),
    Box::new(tweet),
];
```

**限制**: trait必须是对象安全的（不能有泛型方法、返回Self等）

**相关**: [03_advanced/02_traits.md](./03_advanced/02_traits.md)

---

## 关联类型 (Associated Type)

**定义**: Trait中定义的类型占位符。

**vs泛型参数**: 每个类型只能有一个实现

**示例**:

```rust
trait Iterator {
    type Item; // 关联类型
    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> { /* ... */ }
}
```

**相关**: [03_advanced/02_traits.md](./03_advanced/02_traits.md)

---

## Newtype 模式

**定义**: 用单元素元组结构体包装现有类型。

**用途**:

- 类型安全
- 绕过孤儿规则
- 隐藏实现细节

**示例**:

```rust
struct Meters(f64);
struct Seconds(f64);

fn calculate_speed(distance: Meters, time: Seconds) -> f64 {
    distance.0 / time.0
}
```

**相关**: [type_equivalence_newtype.md](./type_equivalence_newtype.md)

---

## 零大小类型 (ZST)

**定义**: 不占用内存的类型。

**示例**:

```rust
struct Unit; // ZST
struct Marker<T>(PhantomData<T>); // ZST

let x: () = (); // unit类型，ZST
```

**用途**:

- 类型标记
- 状态机状态
- 零成本抽象

**相关**: [02_core/01_type_definition.md](./02_core/01_type_definition.md)

---

## PhantomData

**定义**: 零大小类型标记，告诉编译器类型参数的使用。

**用途**:

- 标记生命周期
- 标记所有权
- 控制协变/逆变

**示例**:

```rust
use std::marker::PhantomData;

struct Slice<'a, T> {
    start: *const T,
    end: *const T,
    phantom: PhantomData<&'a T>,
}
```

**相关**: [03_advanced/01_generics.md](./03_advanced/01_generics.md)

---

## Never类型 (!)

**定义**: 表示永不返回的类型。

**用途**:

- panic函数
- 无限循环
- 程序退出

**示例**:

```rust
fn exit() -> ! {
    std::process::exit(0);
}

fn forever() -> ! {
    loop {}
}
```

**特性**: 可以强制转换为任何类型

**相关**: [never_type_control_flow.md](./never_type_control_flow.md)

---

## Pin

**定义**: 保证值在内存中不会移动。

**用途**:

- 自引用结构
- async/await
- FFI

**示例**:

```rust
use std::pin::Pin;

fn use_pinned(pinned: Pin<&mut T>) {
    // pinned保证不会移动
}
```

**相关**: [pin_self_referential_basics.md](./pin_self_referential_basics.md)

---

## 类型推导 (Type Inference)

**定义**: 编译器自动推导变量类型。

**示例**:

```rust
let x = 5; // 推导为 i32
let s = String::from("hello"); // 推导为 String
let v = vec![1, 2, 3]; // 推导为 Vec<i32>
```

**Turbofish语法**: `::<>` 显式指定类型

```rust
let numbers = Vec::<i32>::new();
let result = parse::<i32>("42");
```

**相关**: [03_advanced/04_type_inference.md](./03_advanced/04_type_inference.md)

---

## Deref强制转换

**定义**: 编译器自动插入解引用操作。

**规则**:

- `&T` to `&U` (当 `T: Deref<Target=U>`)
- `&mut T` to `&mut U` (当 `T: DerefMut<Target=U>`)
- `&mut T` to `&U` (当 `T: Deref<Target=U>`)

**示例**:

```rust
fn hello(name: &str) {
    println!("Hello, {}", name);
}

let s = String::from("Rust");
hello(&s); // &String -> &str (Deref强制转换)
```

**相关**: [type_conversion_guidelines.md](./type_conversion_guidelines.md)

---

## 孤儿规则 (Orphan Rule)

**定义**: 只能为本地类型或本地trait实现trait。

**限制**:

- 不能为外部类型实现外部trait
- 防止依赖冲突

**绕过**: 使用newtype模式

```rust
struct Wrapper(Vec<String>);

impl fmt::Display for Wrapper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}]", self.0.join(", "))
    }
}
```

**相关**: [03_advanced/02_traits.md](./03_advanced/02_traits.md)

---

## 协变与逆变

**定义**: 类型参数的子类型关系。

**协变** (Covariance): `T <: U` ⇒ `F<T> <: F<U>`  
**逆变** (Contravariance): `T <: U` ⇒ `F<U> <: F<T>`  
**不变** (Invariance): 无子类型关系

**Rust中**:

- `&'a T` 对 `'a` 和 `T` 协变
- `&'a mut T` 对 `'a` 协变，对 `T` 不变
- `fn(T)` 对 `T` 逆变

**相关**: [01_theory/01_type_system_theory.md](./01_theory/01_type_system_theory.md)

---

## 单态化 (Monomorphization)

**定义**: 编译时为泛型生成具体类型的代码。

**优点**:

- 零运行时开销
- 可以内联优化

**缺点**:

- 代码膨胀
- 编译时间增加

**示例**:

```rust
fn add<T: Add<Output=T>>(a: T, b: T) -> T {
    a + b
}

// 编译后生成两份代码
let x = add(1, 2);     // add_i32
let y = add(1.0, 2.0); // add_f64
```

**相关**: [generics_where_performance.md](./generics_where_performance.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](./README.md) - 项目概述
- [理论基础](./01_theory/) - 类型理论
- [核心概念](./02_core/) - 基础知识
- [高级主题](./03_advanced/) - 进阶内容

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [最佳实践](./05_practice/02_best_practices.md)
