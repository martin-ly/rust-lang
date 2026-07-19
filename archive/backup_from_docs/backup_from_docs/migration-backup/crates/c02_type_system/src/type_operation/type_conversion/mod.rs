/*
在Rust中，**类型转换（type conversion）**
是指将一种数据类型转换为另一种数据类型的过程。
这种转换可以是显式的（需要开发者手动进行）或隐式的（由编译器自动处理）。
Rust提供了多种方式来进行类型转换，以确保类型安全和避免潜在的错误。

## 定义

- **类型转换**：
类型转换是将一个值从一种类型转换为另一种类型的过程。
在Rust中，类型转换通常涉及基本数据类型（如整数、浮点数、布尔值等）之间的转换，
或者在自定义类型之间进行转换。

## 解释

在Rust中，类型转换主要有以下几种方式：

1. **显式转换**：使用`as`关键字进行类型转换，通常用于基本数据类型之间的转换。
2. **从字符串转换**：使用标准库中的方法将字符串转换为其他类型。
3. **实现`From`和`Into`特征**：通过实现这些特征，可以自定义类型之间的转换。

## 示例

以下是一个使用类型转换的示例：

```rust
fn main() {
    // 显式转换：整数到浮点数
    let int_value: i32 = 42;
    let float_value: f64 = int_value as f64; // 使用as进行显式转换
    println!("Integer: {}, Float: {}", int_value, float_value);

    // 从字符串转换为整数
    let str_value = "123";
    let parsed_value: i32 = str_value.parse().unwrap(); // 使用parse方法
    println!("Parsed integer from string: {}", parsed_value);

    // 自定义类型转换
    struct Celsius(f64);
    struct Fahrenheit(f64);

    impl From<Celsius> for Fahrenheit {
        fn from(c: Celsius) -> Self {
            Fahrenheit(c.0 * 9.0 / 5.0 + 32.0)
        }
    }

    let celsius = Celsius(25.0);
    let fahrenheit: Fahrenheit = Fahrenheit::from(celsius); // 使用From特征进行转换
    println!("Celsius: {}, Fahrenheit: {}", celsius.0, fahrenheit.0);
}
```

## 解释示例

1. **显式转换**：
在示例中，我们首先定义了一个`i32`类型的整数`int_value`，
然后使用`as`关键字将其转换为`f64`类型的浮点数`float_value`。
这种显式转换确保了类型安全。

2. **从字符串转换**：
我们定义了一个字符串`str_value`，并使用`parse`方法将其转换为`i32`类型的整数。
`parse`方法返回一个`Result`类型，因此我们使用`unwrap`来处理可能的错误。

3. **自定义类型转换**：
我们定义了两个结构体`Celsius`和`Fahrenheit`，分别表示摄氏度和华氏度。
通过实现`From<Celsius>`特征，我们定义了如何将`Celsius`类型转换为`Fahrenheit`类型。
在`main`函数中，我们创建了一个`Celsius`实例，并使用`From`特征进行转换，得到相应的`Fahrenheit`实例。

## 总结

类型转换在Rust中是一个重要的概念，允许开发者在不同类型之间进行安全的转换。
通过显式转换、字符串解析和实现`From`和`Into`特征，Rust提供了灵活的方式来处理类型转换。
这种机制确保了类型安全，并减少了潜在的错误。

*/
