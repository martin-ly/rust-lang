/*
在Rust中，**类型变异（type variance）**
是指在泛型类型和特征中，类型参数的变化如何影响类型的兼容性。
类型变异主要涉及到**协变（covariance）**、
**逆变（contravariance）**和**不变（invariance）**的概念。
这些概念在处理泛型和特征时非常重要，尤其是在涉及到生命周期和类型安全时。

## 定义

- **类型变异**：
类型变异是指在泛型类型或特征中，类型参数的变化如何影响类型的兼容性。
具体来说，类型变异可以分为以下几种情况：
  - **协变（Covariance）**：
  如果类型`A`是类型`B`的子类型，那么`Box<A>`是`Box<B>`的子类型。
  - **逆变（Contravariance）**：
  如果类型`A`是类型`B`的子类型，那么`Fn(B)`是`Fn(A)`的子类型。
  - **不变（Invariance）**：
  如果类型`A`和类型`B`是不同的类型，那么`Vec<A>`和`Vec<B>`是不同的类型，即使`A`是`B`的子类型。

## 解释
1. **协变**：
在Rust中，协变通常出现在返回值中。
例如，如果一个函数返回一个类型`A`，而`A`是`B`的子类型，那么这个函数也可以被视为返回类型`B`的函数。

2. **逆变**：
逆变通常出现在函数参数中。
如果一个函数接受一个类型`A`作为参数，而`A`是`B`的子类型，那么这个函数也可以接受类型`B`作为参数。

3. **不变**：
不变意味着即使存在子类型关系，类型参数也不会自动转换。
例如，`Vec<A>`和`Vec<B>`是完全不同的类型，即使`A`是`B`的子类型。

## 示例

以下是一个关于类型变异的示例：

```rust
// 定义一个协变的结构体
struct Wrapper<T>(T);

// 定义一个函数，接受一个Wrapper类型的参数
fn print_wrapper(wrapper: Wrapper<&str>) {
    println!("{}", wrapper.0);
}

fn main() {
    let s: String = String::from("Hello, world!");
    let r: &str = &s; // &str是String的子类型

    // 使用协变
    let wrapped: Wrapper<&str> = Wrapper(r);
    print_wrapper(wrapped); // 输出: Hello, world!

    // 逆变示例
    let fn_str: fn(&str) = |s| println!("{}", s);
    let fn_string: fn(String) = fn_str; // 逆变，fn(&str)可以被视为fn(String)

    fn_string(String::from("Hello, Rust!")); // 输出: Hello, Rust!

    // 不变示例
    let vec_a: Vec<i32> = vec![1, 2, 3];
    // let vec_b: Vec<u32> = vec_a; // 编译错误，Vec<i32>和Vec<u32>不兼容
}
```

## 解释示例

1. **协变**：
我们定义了一个`Wrapper<T>`结构体，它是一个简单的包装器。
我们定义了一个函数`print_wrapper`，接受一个`Wrapper<&str>`类型的参数。
在`main`函数中，我们创建了一个`String`并将其转换为`&str`，
然后将其包装在`Wrapper`中并传递给`print_wrapper`。
由于`&str`是`String`的子类型，这里展示了协变的特性。

2. **逆变**：
我们定义了一个函数指针`fn_str`，它接受一个`&str`类型的参数。
由于`fn(&str)`可以被视为`fn(String)`的子类型，
因此我们可以将`fn_str`赋值给`fn_string`。
这展示了逆变的特性。

3. **不变**：
我们创建了一个`Vec<i32>`类型的向量`vec_a`。
尝试将其赋值给`Vec<u32>`会导致编译错误，
因为`Vec<i32>`和`Vec<u32>`是完全不同的类型，展示了不变的特性。

## 总结

类型变异在Rust中是一个重要的概念，影响着泛型和特征的使用。
通过理解协变、逆变和不变的定义和实现，开发者可以更好地利用Rust的类型系统，
确保代码的安全性和可维护性。
类型变异的概念在处理生命周期、泛型和函数类型时尤为重要。
*/

pub mod contravariance;
pub mod covariance;
pub mod invariance;
