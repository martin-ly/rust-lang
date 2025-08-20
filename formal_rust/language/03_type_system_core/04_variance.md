# 3.4 型变系统

## 3.4.1 概述

型变（Variance）是类型系统中的一个重要概念，它描述了复合类型的子类型关系如何依赖于其组成类型的子类型关系。在Rust中，型变规则决定了泛型类型之间的子类型关系，这对于类型安全和类型转换至关重要。本章将从形式化的角度详细阐述Rust的型变系统，包括其数学基础、形式化定义、型变规则以及在实际编程中的应用。

## 3.4.2 型变的基本概念

### 3.4.2.1 型变的定义

型变描述了当组成类型之间存在子类型关系时，复合类型之间的子类型关系如何变化。

**形式化定义**：

对于类型构造器 $F$，给定类型 $A$ 和 $B$，如果 $A <: B$（$A$ 是 $B$ 的子类型），则 $F$ 的型变性质决定了 $F<A>$ 和 $F<B>$ 之间的关系。

### 3.4.2.2 型变的种类

Rust中存在三种主要的型变关系：

1. **协变（Covariant）**：如果 $A <: B$ 蕴含 $F<A> <: F<B>$，则 $F$ 对其参数是协变的。
2. **逆变（Contravariant）**：如果 $A <: B$ 蕴含 $F<B> <: F<A>$，则 $F$ 对其参数是逆变的。
3. **不变（Invariant）**：如果 $A <: B$ 不蕴含 $F<A>$ 和 $F<B>$ 之间的任何子类型关系，则 $F$ 对其参数是不变的。

**Rust示例**：

```rust
trait Animal {}
struct Dog;
impl Animal for Dog {}

// 协变示例
fn covariant_example() {
    let dog_box: Box<Dog> = Box::new(Dog);
    // Box<T> 对 T 是协变的，所以 Box<Dog> 可以转换为 Box<dyn Animal>
    let animal_box: Box<dyn Animal> = dog_box;
}

// 逆变示例
fn contravariant_example() {
    // 函数类型 fn(T) 对参数 T 是逆变的
    fn process_animal(_: &dyn Animal) {}
    
    fn use_dog_processor(f: fn(&Dog)) {
        let dog = Dog;
        f(&dog);
    }
    
    // 如果 Dog <: Animal，则 fn(&dyn Animal) <: fn(&Dog)
    use_dog_processor(process_animal);
}

// 不变示例
fn invariant_example() {
    let mut dog = Dog;
    let dog_ref = &mut dog;
    
    // 以下代码无法编译，因为 &mut T 对 T 是不变的
    // let animal_ref: &mut dyn Animal = dog_ref;
}
```

## 3.4.3 型变的形式化表示

### 3.4.3.1 子类型关系

在讨论型变之前，需要先形式化定义子类型关系。

**形式化定义**：

子类型关系 $<:$ 是类型之间的一个偏序关系，满足以下性质：

- 自反性：对于任意类型 $T$，$T <: T$
- 传递性：如果 $A <: B$ 且 $B <: C$，则 $A <: C$
- 反对称性：如果 $A <: B$ 且 $B <: A$，则 $A = B$

在Rust中，子类型关系主要通过特征对象和生命周期约束体现。

### 3.4.3.2 型变的形式化定义

对于单参数类型构造器 $F<\_>$，其型变性质可以形式化定义如下：

1. **协变**：$\forall A, B. A <: B \Rightarrow F<A> <: F<B>$
2. **逆变**：$\forall A, B. A <: B \Rightarrow F<B> <: F<A>$
3. **不变**：$\exists A, B. A <: B \land F<A> \not<: F<B> \land F<B> \not<: F<A>$

对于多参数类型构造器，每个参数位置可以有不同的型变性质。

### 3.4.3.3 型变的推导规则

复合类型的型变性质可以通过其组成部分的型变性质推导。

**形式化规则**：

1. **协变组合规则**：
   - 如果 $F$ 对 $X$ 是协变的，且 $G$ 对 $Y$ 是协变的，则 $F<G<\_>>$ 对其参数是协变的。
   - 如果 $F$ 对 $X$ 是逆变的，且 $G$ 对 $Y$ 是逆变的，则 $F<G<\_>>$ 对其参数是协变的。

2. **逆变组合规则**：
   - 如果 $F$ 对 $X$ 是协变的，且 $G$ 对 $Y$ 是逆变的，则 $F<G<\_>>$ 对其参数是逆变的。
   - 如果 $F$ 对 $X$ 是逆变的，且 $G$ 对 $Y$ 是协变的，则 $F<G<\_>>$ 对其参数是逆变的。

3. **不变组合规则**：
   - 如果 $F$ 或 $G$ 对其参数是不变的，则 $F<G<\_>>$ 对其参数是不变的。

## 3.4.4 Rust中的型变规则

### 3.4.4.1 常见类型构造器的型变性质

Rust中不同类型构造器具有不同的型变性质：

| 类型构造器 | 型变性质 |
|:----------:|:--------:|
| `&T` | 对 `T` 是协变的 |
| `&mut T` | 对 `T` 是不变的 |
| `Box<T>` | 对 `T` 是协变的 |
| `Vec<T>` | 对 `T` 是协变的 |
| `Option<T>` | 对 `T` 是协变的 |
| `Result<T, E>` | 对 `T` 和 `E` 都是协变的 |
| `fn(T) -> U` | 对 `T` 是逆变的，对 `U` 是协变的 |
| `*const T` | 对 `T` 是协变的 |
| `*mut T` | 对 `T` 是不变的 |
| `Cell<T>` | 对 `T` 是不变的 |
| `RefCell<T>` | 对 `T` 是不变的 |

### 3.4.4.2 型变性质的推导

Rust编译器根据类型的定义自动推导其型变性质。对于用户定义的类型，型变性质取决于其字段和泛型参数的使用方式。

**形式化规则**：

1. 如果类型参数 `T` 只在协变位置出现，则类型对 `T` 是协变的。
2. 如果类型参数 `T` 只在逆变位置出现，则类型对 `T` 是逆变的。
3. 如果类型参数 `T` 同时在协变和逆变位置出现，则类型对 `T` 是不变的。
4. 如果类型参数 `T` 在不变位置出现，则类型对 `T` 是不变的。

**Rust示例**：

```rust
// 协变：T 只在协变位置出现
struct Wrapper<T>(T);

// 不变：T 在可变引用中出现
struct MutableRef<T> {
    value: &mut T,
}

// 混合型变：T 在协变位置，U 在逆变位置
struct Function<T, U> {
    f: fn(U) -> T,
}
// Function<T, U> 对 T 是协变的，对 U 是逆变的
```

### 3.4.4.3 PhantomData与型变控制

Rust提供了 `PhantomData` 标记类型，允许程序员显式控制自定义类型的型变性质。

**Rust示例**：

```rust
use std::marker::PhantomData;

// 使 MyBox<T> 对 T 是协变的
struct MyBox<T> {
    data: *const T,
    _marker: PhantomData<T>,
}

// 使 MyFunction<T> 对 T 是逆变的
struct MyFunction<T> {
    _marker: PhantomData<fn(T)>,
}

// 使 MyInvariant<T> 对 T 是不变的
struct MyInvariant<T> {
    _marker: PhantomData<*mut T>,
}
```

## 3.4.5 型变与类型安全

### 3.4.5.1 型变与内存安全

Rust的型变规则是为了确保类型安全和内存安全而设计的。特别是，可变引用的不变性是防止数据竞争的关键机制。

**形式化证明**：

假设 `&mut T` 对 `T` 是协变的，考虑以下代码：

```rust
fn overwrite(_: &mut dyn Animal) {
    // 可能覆盖 Animal 特有的字段
}

fn unsafe_code() {
    let mut dog = Dog { /* dog-specific fields */ };
    let dog_ref = &mut dog;
    
    // 如果允许这种转换（实际上Rust不允许）
    let animal_ref: &mut dyn Animal = dog_ref;
    
    // 调用可能覆盖 Dog 特有字段的函数
    overwrite(animal_ref);
    
    // dog 现在可能处于无效状态
    dog_ref.dog_specific_method(); // 潜在的未定义行为
}
```

因此，`&mut T` 必须对 `T` 是不变的，以保证类型安全。

### 3.4.5.2 型变与生命周期

生命周期也遵循型变规则，这对于确保引用安全至关重要。

**形式化表示**：

如果生命周期 `'a` 比 `'b` 长（即 `'a: 'b`），则：

- `&'a T` 是 `&'b T` 的子类型（协变）
- `&'b mut T` 和 `&'a mut T` 之间没有子类型关系（不变）
- `fn(&'b T)` 是 `fn(&'a T)` 的子类型（逆变）

**Rust示例**：

```rust
fn lifetime_variance<'a, 'b: 'a>(longer: &'b str, shorter: &'a str) {
    // 协变：可以将长生命周期引用赋值给短生命周期引用
    let s: &'a str = longer;
    
    // 以下代码无法编译，因为函数参数位置是逆变的
    // fn takes_short(_: &'a str) {}
    // fn takes_long(_: &'b str) {}
    // let f: fn(&'a str) = takes_long;
}
```

## 3.4.6 型变的高级应用

### 3.4.6.1 型变与泛型抽象

理解型变对于设计灵活且类型安全的泛型API至关重要。

**Rust示例**：

```rust
// 设计一个对 T 是协变的容器
struct ReadOnlyVec<T> {
    data: Vec<T>,
}

impl<T> ReadOnlyVec<T> {
    fn new(data: Vec<T>) -> Self {
        ReadOnlyVec { data }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
    
    // 注意：没有提供修改元素的方法
}

// 使用协变性
fn use_container<T: Display>(container: ReadOnlyVec<T>) {
    if let Some(item) = container.get(0) {
        println!("{}", item);
    }
}

fn example() {
    let dogs = vec![Dog, Dog];
    let dog_container = ReadOnlyVec::new(dogs);
    
    // 利用协变性将 ReadOnlyVec<Dog> 转换为 ReadOnlyVec<dyn Animal>
    use_container(dog_container);
}
```

### 3.4.6.2 型变与特征对象

型变规则影响特征对象的行为和安全。

**Rust示例**：

```rust
trait Transformer<T> {
    fn transform(&self, value: T) -> T;
}

// 实现特定类型的转换器
struct IntTransformer;
impl Transformer<i32> for IntTransformer {
    fn transform(&self, value: i32) -> i32 {
        value * 2
    }
}

// 使用特征对象和型变
fn use_transformer<T>(value: T, transformer: &dyn Transformer<T>) -> T {
    transformer.transform(value)
}

fn example() {
    let transformer = IntTransformer;
    let result = use_transformer(5, &transformer);
    assert_eq!(result, 10);
}
```

### 3.4.6.3 型变与高级类型模式

型变在实现高级类型模式时起着重要作用，如函数式编程模式和容器抽象。

**Rust示例**：

```rust
// Functor 模式，利用协变性
trait Functor<A> {
    type Target<B>;
    
    fn map<B, F>(self, f: F) -> Self::Target<B>
    where
        F: FnOnce(A) -> B;
}

// 为 Option 实现 Functor
impl<A> Functor<A> for Option<A> {
    type Target<B> = Option<B>;
    
    fn map<B, F>(self, f: F) -> Option<B>
    where
        F: FnOnce(A) -> B,
    {
        match self {
            Some(a) => Some(f(a)),
            None => None,
        }
    }
}
```

## 3.4.7 型变与其他语言的比较

### 3.4.7.1 与Java的比较

| 特征 | Rust | Java |
|:----:|:----:|:----:|
| 数组型变 | 不适用（无内置数组型变） | 协变（不安全） |
| 泛型型变 | 根据类型自动推导 | 使用通配符（`? extends T`，`? super T`） |
| 函数型变 | 参数逆变，返回值协变 | 参数逆变，返回值协变 |
| 可变性与型变 | 可变引用不变，不可变引用协变 | 所有引用协变（不安全） |

### 3.4.7.2 与C++的比较

| 特征 | Rust | C++ |
|:----:|:----:|:----:|
| 泛型型变 | 自动推导 | 无内置支持（C++20前） |
| 指针型变 | 原始指针协变，可变指针不变 | 所有指针协变（不安全） |
| 安全保证 | 编译时强制执行型变规则 | 无型变安全保证 |

### 3.4.7.3 与Scala的比较

| 特征 | Rust | Scala |
|:----:|:----:|:----:|
| 型变声明 | 自动推导 | 显式声明（`+T` 协变，`-T` 逆变） |
| 型变检查 | 编译时强制执行 | 编译时强制执行 |
| 型变位置 | 基于使用位置自动推导 | 基于声明位置 |

## 3.4.8 型变的实际应用模式

### 3.4.8.1 容器型变模式

设计容器类型时，根据容器的用途选择合适的型变性质。

**模式**：

- 只读容器通常对其元素类型是协变的
- 可写容器通常对其元素类型是不变的
- 消费者容器（如回调注册器）对其元素类型可能是逆变的

**Rust示例**：

```rust
// 只读容器：协变
struct ReadOnly<T>(Vec<T>);

// 读写容器：不变
struct ReadWrite<T> {
    data: Vec<T>,
}

// 消费者容器：逆变（通过函数类型）
struct Consumer<T> {
    callback: fn(T),
}
```

### 3.4.8.2 型变与API设计

在设计API时，理解型变可以帮助创建更灵活、更安全的接口。

**设计原则**：

1. 返回值位置倾向于使用协变类型参数
2. 参数位置倾向于使用逆变类型参数
3. 可变状态应使用不变类型参数

**Rust示例**：

```rust
// 灵活的API设计，利用型变规则
trait Repository<T> {
    // 返回值位置：协变
    fn get(&self, id: usize) -> Option<&T>;
    
    // 参数位置：逆变（实际上Rust中参数不支持子类型多态，这里仅作概念说明）
    fn save(&mut self, item: T);
}
```

### 3.4.8.3 型变与错误处理

型变在错误处理模式中也有应用。

**Rust示例**：

```rust
// 利用 Result<T, E> 对 E 的协变性
trait Error {}

#[derive(Debug)]
struct NetworkError;
impl Error for NetworkError {}

#[derive(Debug)]
struct DatabaseError;
impl Error for DatabaseError {}

fn fallible_operation() -> Result<(), Box<dyn Error>> {
    // 可以返回任何实现了 Error 的错误类型
    Err(Box::new(NetworkError))
}
```

## 3.4.9 总结

Rust的型变系统是其类型系统的重要组成部分，通过精心设计的型变规则确保了类型安全和内存安全。型变规则决定了泛型类型之间的子类型关系，这对于设计灵活且安全的API至关重要。

型变系统的形式化基础建立在子类型理论上，通过协变、逆变和不变三种基本关系描述了复合类型之间的子类型关系。Rust编译器能够自动推导类型的型变性质，并在编译时强制执行型变规则，确保程序的安全。

理解型变对于Rust程序员来说是至关重要的，它不仅有助于理解编译器错误，还能指导API设计和泛型抽象的实现。通过合理利用型变规则，可以创建既灵活又安全的代码。

## 3.4.10 参考文献

1. Pierce, B. C. (2002). Types and Programming Languages. MIT Press.

2. Cardelli, L. (1988). Structural subtyping and the notion of power type. In Proceedings of the 15th ACM SIGPLAN-SIGACT symposium on Principles of programming languages.

3. Liskov, B. H., & Wing, J. M. (1994). A behavioral notion of subtyping. ACM Transactions on Programming Languages and Systems, 16(6), 1811-1841.

4. Matsakis, N. D., & Klock, F. S. (2014). The Rust language. ACM SIGAda Ada Letters, 34(3), 103-104.

5. Tate, R., Leung, A., & Lerner, S. (2011). Taming wildcards in Java's type system. In Proceedings of the 32nd ACM SIGPLAN conference on Programming language design and implementation.

6. Igarashi, A., & Viroli, M. (2002). On variance-based subtyping for parametric types. In ECOOP 2002—Object-Oriented Programming.
