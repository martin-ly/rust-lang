/*
多态（Polymorphism）
是指在不同上下文中，使用相同的接口或方法来处理不同类型的对象或数据的能力。
它是面向对象编程和类型系统中的一个重要概念，
允许程序在运行时或编译时根据对象的实际类型来决定调用哪个方法或执行哪个操作。

多态的主要特点包括：
1. **接口统一**：
    不同类型的对象可以通过相同的接口进行操作，简化了代码的复杂性。
2. **动态性**：
    在动态多态中，程序可以在运行时决定调用哪个具体的实现，这通常通过虚函数或特征对象实现。
3. **静态性**：
    在静态多态中，编译器在编译时确定具体的类型和方法调用，通常通过泛型实现。

多态的常见形式包括：
- **方法重载（Overloading）**：同一方法名可以根据参数类型或数量的不同而有不同的实现。
- **方法重写（Overriding）**：子类可以重写父类的方法，以提供特定的实现。
- **泛型（Generics）**：允许函数或数据结构在不同类型上工作，而不需要在每种类型上重复代码。
总之，多态使得程序更加灵活和可扩展，能够处理不同类型的对象而无需关心其具体实现。


在Rust中，多态（polymorphism）主要可以分为以下几类：

1. **静态多态（Static Polymorphism）**：
   - **泛型（Generics）**：
   Rust的泛型允许在编译时定义函数和数据结构，使其能够处理不同类型的数据。
   通过使用泛型，Rust能够在编译时生成特定类型的代码，从而实现静态多态。
    
     ```rust
     fn print_value<T: std::fmt::Display>(value: T) {
         println!("{}", value);
     }
     ```

2. **动态多态（Dynamic Polymorphism）**：
   - **特征（Traits）**：
   Rust的特征提供了一种动态多态的机制。
   特征定义了一组方法的接口，任何实现了该特征的类型都可以被视为该特征的类型。
   通过使用特征对象（trait objects），可以在运行时实现动态分发。
   
     ```rust
     trait Shape {
         fn area(&self) -> f64;
     }

     struct Circle {
         radius: f64,
     }

     impl Shape for Circle {
         fn area(&self) -> f64 {
             std::f64::consts::PI * self.radius * self.radius
         }
     }

     fn print_area(shape: &dyn Shape) {
         println!("Area: {}", shape.area());
     }
     ```

3. **类型别名（Type Aliases）**：
   - Rust允许使用类型别名来创建更具可读性的类型，
   这在某种程度上也可以被视为一种多态性，尽管它并不直接涉及到方法的动态分发。
     ```rust
     type IntVec = Vec<i32>;
     ```

4. **枚举（Enums）**：
   - Rust的枚举类型可以包含不同类型的值，这也可以被视为一种多态。
   通过模式匹配，可以在运行时处理不同的枚举变体。
   
     ```rust
     enum Shape {
         Circle(f64),
         Rectangle(f64, f64),
     }

     fn area(shape: Shape) -> f64 {
         match shape {
             Shape::Circle(radius) => std::f64::consts::PI * radius * radius,
             Shape::Rectangle(width, height) => width * height,
         }
     }
     ```

这些多态的分类使得Rust在处理不同类型和实现时具有灵活性和强大的表达能力。
*/

pub mod trait_object;
pub mod generic_trait;
