# 变型与子类型 (Variance and Subtyping)

## 摘要

变型(Variance)和子类型(Subtyping)是类型系统中的核心概念，它们定义了何时可以安全地将一种类型用在需要另一种类型的上下文中。Rust 的类型系统包含精细的变型规则，这些规则在确保内存安全的同时提供了灵活性。本文探讨变型和子类型的理论基础、Rust 中的实现及其对实际编程的影响。

## 理论基础

### 1. 子类型关系

子类型是一种类型间的关系，表示一个类型是另一个类型的"子集"或"更具体版本"。形式上，若 $S$ 是 $T$ 的子类型，记作 $S <: T$，则任何需要类型 $T$ 的地方都可以使用类型 $S$。

子类型关系满足以下数学性质：
- 自反性: $\forall T. T <: T$
- 传递性: $\forall S, T, U. S <: T \land T <: U \Rightarrow S <: U$

### 2. 变型的形式定义

对于参数化类型构造器 $F<T>$，其变型描述了当参数 $T$ 的子类型关系变化时，$F<T>$ 的子类型关系如何变化。有三种基本变型：

1. **协变(Covariant)**: 保持子类型关系同向
   - 形式化定义: $S <: T \Rightarrow F<S> <: F<T>$

2. **逆变(Contravariant)**: 反转子类型关系
   - 形式化定义: $S <: T \Rightarrow F<T> <: F<S>$

3. **不变(Invariant)**: 不产生子类型关系
   - 形式化定义: $S <: T \land S \neq T \Rightarrow F<S> \not<: F<T> \land F<T> \not<: F<S>$

### 3. 变型在复合类型中的传播

对于复合类型，变型根据以下规则传播：

- 若 $F<T>$ 在 $T$ 上是协变的，且 $G<T>$ 在 $T$ 上是协变的，则 $F<G<T>>$ 在 $T$ 上是协变的
- 若 $F<T>$ 在 $T$ 上是协变的，且 $G<T>$ 在 $T$ 上是逆变的，则 $F<G<T>>$ 在 $T$ 上是逆变的
- 若 $F<T>$ 在 $T$ 上是逆变的，且 $G<T>$ 在 $T$ 上是协变的，则 $F<G<T>>$ 在 $T$ 上是逆变的
- 若 $F<T>$ 在 $T$ 上是逆变的，且 $G<T>$ 在 $T$ 上是逆变的，则 $F<G<T>>$ 在 $T$ 上是协变的

形式化表示：
- $\text{Cov}[F] \land \text{Cov}[G] \Rightarrow \text{Cov}[F \circ G]$
- $\text{Cov}[F] \land \text{Contra}[G] \Rightarrow \text{Contra}[F \circ G]$
- $\text{Contra}[F] \land \text{Cov}[G] \Rightarrow \text{Contra}[F \circ G]$
- $\text{Contra}[F] \land \text{Contra}[G] \Rightarrow \text{Cov}[F \circ G]$

## Rust 中的子类型关系

### 1. 生命周期子类型

在 Rust 中，生命周期之间存在子类型关系。若生命周期 `'a` 比生命周期 `'b` 长，则 `'a` 是 `'b` 的子类型：

```rust
// 'static 是所有生命周期的子类型
let static_str: &'static str = "hello";
fn takes_str<'a>(s: &'a str) {
    // 合法，因为 'static <: 'a
    takes_str(static_str);
}
```

形式化表示：若 `'a` 包含 `'b`，则 `'a <: 'b`。

### 2. 类型体系中的子类型关系

Rust 类型系统中的其他子类型关系：

- 具体类型与特征：实现某特征的类型是该特征对象的子类型
  - 形式化：若 `T: Trait`，则 `T <: dyn Trait`
  
- 特征对象之间：若一个特征是另一个特征的超特征，则前者的特征对象是后者的子类型
  - 形式化：若 `trait Sub: Super`，则 `dyn Sub <: dyn Super`

## Rust 中的变型规则

### 1. 基本类型构造器的变型

| 类型构造器 | 变型 | 示例 |
|------------|------|------|
| `&'a T` | 在 `'a` 和 `T` 上协变 | 若 `'b <: 'a` 且 `U <: T`，则 `&'b U <: &'a T` |
| `&'a mut T` | 在 `'a` 上协变，在 `T` 上不变 | 若 `'b <: 'a`，则 `&'b mut T <: &'a mut T` |
| `*const T` | 在 `T` 上协变 | 若 `U <: T`，则 `*const U <: *const T` |
| `*mut T` | 在 `T` 上不变 | 对任何 `U <: T` 且 `U != T`，`*mut U` 与 `*mut T` 不存在子类型关系 |
| `Box<T>` | 在 `T` 上协变 | 若 `U <: T`，则 `Box<U> <: Box<T>` |
| `fn(T) -> U` | 在参数 `T` 上逆变，在返回值 `U` 上协变 | 若 `T <: S` 且 `U <: V`，则 `fn(S) -> U <: fn(T) -> V` |

### 2. 变型的安全性原理

Rust 的变型规则设计用于保证内存安全。关键安全原则为：

- **不可变引用可协变**：因为只读访问不会破坏原数据的不变性
- **可变引用必须不变**：防止通过子类型关系破坏数据不变性
- **函数参数逆变**：确保可以用更宽泛的类型处理函数参数
- **函数返回值协变**：确保函数可以返回更具体的类型

### 3. 变型检查的形式化算法

编译器使用以下算法确定复合类型的变型：

1. 构建类型的结构依赖图
2. 为每个类型变量分配变型位置标记（正、负或不变）
3. 根据类型构造器的变型规则传播变型标记
4. 根据最终标记确定整体变型

## 实际应用与示例

### 1. 生命周期与协变

生命周期协变使代码更灵活，允许短生命周期的值用于需要长生命周期的地方：

```rust
fn process<'a>(data: &'a [u8]) -> &'a [u8] {
    // 处理逻辑
    data
}

fn main() {
    let result;
    {
        let short_lived = [1, 2, 3];
        // 'short 生命周期 <: 'a
        result = process(&short_lived); // 编译错误! 返回值生命周期不够长
    }
    println!("{:?}", result);
}
```

### 2. 函数类型与逆变

函数类型参数的逆变性质允许处理更多类型的输入：

```rust
trait Animal {}
struct Dog;
impl Animal for Dog {}

struct Cat;
impl Animal for Cat {}

fn handle_animal(f: fn(&Animal)) {
    let dog = Dog;
    f(&dog as &Animal);
}

// 接受 &Dog 的函数，从逆变角度看可以被视为 fn(&Animal) 的子类型
fn pet_dog(dog: &Dog) {
    // 宠物狗特定操作
}

// 这段代码会编译失败，因为 fn(&Dog) 不是 fn(&Animal) 的子类型
// handle_animal(pet_dog);
```

### 3. 不变性与 `Cell<T>`

Rust 标准库中的 `Cell<T>` 在 `T` 上是不变的，这是为了确保类型安全：

```rust
use std::cell::Cell;

fn requires_cell_string(c: &Cell<String>) {
    c.set(String::from("changed"));
}

fn main() {
    let cell_object = Cell::new(String::from("object"));
    
    // 假设 Cell<T> 在 T 上是协变的（实际不是）
    // 如果 Cell<String> <: Cell<Object> 成立
    // requires_cell_object(&cell_string); // 这会导致类型安全问题
}
```

如果 `Cell<T>` 是协变的，则可能通过子类型关系向 `Cell` 中存储不正确类型的值。

## 高级主题

### 1. 自定义类型的变型推断

Rust 编译器根据类型定义自动推导变型：

```rust
// 在 T 上协变，因为 T 只用于不可变位置
struct ReadOnly<T> {
    value: T,
}

// 在 T 上不变，因为 T 用于可变位置
struct WriteOnly<T> {
    value: *mut T,
}
```

### 2. PhantomData 与变型控制

使用 `PhantomData` 可以显式控制类型的变型行为：

```rust
use std::marker::PhantomData;

// 在 T 上协变
struct Covariant<T> {
    _marker: PhantomData<T>,
}

// 在 T 上逆变
struct Contravariant<T> {
    _marker: PhantomData<fn(T)>,
}

// 在 T 上不变
struct Invariant<T> {
    _marker: PhantomData<*mut T>,
}
```

### 3. 变型与内部可变性

内部可变性模式使得在不可变引用背后隐藏可变性，这影响了变型规则：

```rust
use std::cell::RefCell;

// RefCell<T> 在 T 上不变，尽管表面上它接受 &self
fn demonstrate<T>(rc: &RefCell<T>) {
    // 可以通过 &RefCell<T> 获取可变引用 &mut T
    let _mutable: &mut T = &mut *rc.borrow_mut();
}
```

## 形式化验证

### 1. Rust 变型规则的健全性

Rust 变型规则的健全性可以通过以下定理表述：

**定理**: 若 Rust 类型系统接受程序 $P$，则 $P$ 不会因子类型替换而导致未定义行为。

**证明思路**:
1. 使用 Rust 的所有权系统形式化模型
2. 证明可变引用不变性保证了内存安全
3. 证明所有子类型替换保持类型不变量

### 2. 与其他类型系统的比较

Rust 的变型系统与其他语言的比较：

| 语言 | 变型特性 |
|------|----------|
| Java | 数组协变（不安全），泛型不变，通配符提供有限的协变/逆变 |
| C# | 数组不变，泛型支持注解协变/逆变（`out`/`in`） |
| Scala | 支持类型构造器的协变/逆变注解（`+`/`-`） |
| Rust | 自动推断变型，基于位置的变型规则 |

## 结论

变型和子类型是 Rust 类型系统的重要组成部分，它们支持灵活的编程模式同时确保静态类型安全性。通过精心设计的变型规则，Rust 允许代码在适当情况下利用子类型关系，同时保持内存安全和并发安全的强保证。理解这些概念对于编写既安全又灵活的 Rust 代码至关重要，尤其在处理复杂的生命周期关系和泛型代码时。

## 参考文献

1. Pierce, B. C. (2002). Types and programming languages. MIT press.

2. Cardelli, L. (1988). Structural subtyping and the notion of power type. In Proceedings of the 15th ACM SIGPLAN-SIGACT symposium on Principles of programming languages.

3. Kennedy, A., & Pierce, B. (2007). On decidability of nominal subtyping with variance.

4. The Rust Reference. (n.d.). Subtyping and Variance. Retrieved from <https://doc.rust-lang.org/reference/subtyping.html>

5. Nomicon: The Dark Arts of Advanced and Unsafe Rust Programming. (n.d.). Subtyping and Variance. Retrieved from <https://doc.rust-lang.org/nomicon/subtyping.html>

6. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2018). RustBelt: securing the foundations of the Rust programming language. Proceedings of the ACM on Programming Languages.

7. Klabnik, S., & Nichols, C. (2019). The Rust Programming Language. No Starch Press. 