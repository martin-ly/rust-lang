# 05. 高级泛型主题 (Advanced Generic Topics)


## 📊 目录

- [5.1. Rust 中的多态 (Polymorphism)](#51-rust-中的多态-polymorphism)
  - [5.1.1. 静态多态 (Static Polymorphism)](#511-静态多态-static-polymorphism)
  - [5.1.2. 动态多态 (Dynamic Polymorphism)](#512-动态多态-dynamic-polymorphism)
- [5.2. 类型构造器 (Type Constructors)](#52-类型构造器-type-constructors)
- [5.3. A Note on Higher-Kinded Types (HKT)](#53-a-note-on-higher-kinded-types-hkt)


本章探讨由 Rust 泛型系统引申出的一些更深入、更具理论性的主题，包括多态的两种主要形式，以及在类型级别进行抽象的更高层次的概念。

## 5.1. Rust 中的多态 (Polymorphism)

多态是指代码能够以统一的方式处理不同类型值的能力。Rust 主要通过两种机制实现多态，它们在性能和灵活性之间做出了不同的权衡。

### 5.1.1. 静态多态 (Static Polymorphism)

静态多态在**编译时**解析。这是 Rust 中最主要、最常用的多态形式，其核心实现就是**泛型**。

* **机制**: 通过泛型和 Trait 约束，我们编写的代码可以适用于任何满足约束的类型。编译器通过**单态化**过程，为每个用到的具体类型生成一份专门的代码。
* **性能**: 由于在编译时就已经确定了所有调用的具体函数，因此没有任何运行时开销。其性能与手写针对具体类型的代码完全相同。这是一种**零成本抽象**。
* **示例**:

    ```rust
    // 这是一个静态多态的例子
    fn print_displayable<T: std::fmt::Display>(item: T) {
        println!("{}", item);
    }
    // 编译器会为 print_displayable(5) 和 print_displayable("hello") 生成两份不同的机器码
    ```

### 5.1.2. 动态多态 (Dynamic Polymorphism)

动态多态在**运行时**解析。它允许我们在无法预知所有可能类型的情况下编写代码，例如处理一个由用户加载的插件系统。其核心实现是 **Trait 对象 (Trait Objects)**。

* **机制**: 通过 `&dyn MyTrait` 或 `Box<dyn MyTrait>` 的形式创建一个 Trait 对象。Trait 对象是一个"胖指针"，它包含两部分：
    1. 一个指向具体类型实例数据的指针。
    2. 一个指向**虚方法表 (vtable)** 的指针。vtable 是一个函数指针数组，记录了该具体类型对 Trait 中每个方法的实现地址。
* **性能**: 当通过 Trait 对象调用方法时，程序需要在运行时查询 vtable 以找到正确的函数地址。这个额外的间接查询会带来微小的运行时开销，与静态分派相比略慢。
* **灵活性**: 它的优势在于可以在一个集合（如 `Vec<&dyn Shape>`）中存放多种不同的、但都实现了同一 Trait 的具体类型实例。这是静态多态无法做到的。
* **示例**:

    ```rust
    trait Shape {
        fn area(&self) -> f64;
    }
    struct Circle { radius: f64 }
    impl Shape for Circle { /* ... */ }
    struct Square { side: f64 }
    impl Shape for Square { /* ... */ }

    // 这是一个动态多态的例子
    // `shapes` 可以持有任何实现了 `Shape` Trait 的类型的引用
    let shapes: Vec<&dyn Shape> = vec![&Circle{..}, &Square{..}];

    for shape in shapes {
        // 调用 `area()` 需要在运行时通过 vtable 查找
        println!("Area: {}", shape.area());
    }
    ```

| 特征 | 静态多态 (泛型) | 动态多态 (Trait 对象) |
| :--- | :--- | :--- |
| **解析时机** | 编译时 | 运行时 |
| **性能开销** | 无 (零成本) | 微小 (vtable 查询) |
| **实现方式** | 单态化 | 胖指针 (数据 + vtable) |
| **灵活性** | 类型必须在编译时确定 | 允许异构集合 |

## 5.2. 类型构造器 (Type Constructors)

从类型理论的视角看，一个泛型类型（如 `Vec<T>`, `Option<T>`, `Result<T, E>`）可以被理解为一个**类型构造器**。

**定义**: 类型构造器是一个"函数"，它在**类型级别**上运作。它接受一个或多个类型作为参数，并"返回"一个新的、具体的类型。

* `Vec` 是一个类型构造器，它接受 `i32` 作为参数，构造出新类型 `Vec<i32>`。
* `Result` 是一个接受两个参数的类型构造器，它接受 `String` 和 `io::Error`，构造出新类型 `Result<String, io::Error>`。

这个概念帮助我们将泛型从"一个可以装任何东西的容器"提升到"一种定义类型之间稳定转换关系"的更高层次的抽象。

## 5.3. A Note on Higher-Kinded Types (HKT)

**高阶类型 (Higher-Kinded Types, HKT)** 是类型系统中的一个高级概念，它将类型构造器的思想又推进了一步。

**定义**: HKT 是**泛化类型构造器本身**的能力。换句话说，它允许我们编写一个不关心具体容器类型（如 `Vec` 或 `Option`），只关心容器"形状"的代码。

在一种假想的、支持 HKT 的 Rust 语法中，我们或许可以这样写：

```rust
// 伪代码: Rust 目前不支持这种语法
trait Functor<F<_>> { // F<_> 表示一个接受一个类型参数的类型构造器
    fn map<A, B, Func>(f: Func, fa: F<A>) -> F<B>
        where Func: Fn(A) -> B;
}

// 我们可以为 Vec 实现 Functor
impl<T> Functor<Vec<_>> for ... { ... }

// 也可以为 Option 实现 Functor
impl<T> Functor<Option<_>> for ... { ... }
```

`Functor` Trait 本身是泛型的，它泛化的不是一个具体的类型 `T`，而是一个类型构造器 `F`。

**当前状态**:
目前，**Rust 稳定版不直接支持 HKT**。这是 Rust 类型系统中最受期待也最复杂的待实现特征之一。虽然社区通过一些复杂的编码模式（如 a-la-carte 模式）进行模拟，但原生支持仍在探索中。类似 `generic_const_exprs` 等特征的发展，标志着 Rust 的类型系统正逐步变得更强大，为未来值值值可能支持 HKT 等高级概念奠定基础。

---

**章节导航:**

* **上一章 ->** `04_associated_types.md`
* **返回目录 ->** `_index.md`
