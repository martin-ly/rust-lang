/*
在Rust中，**类型组合（type composition）**是指通过组合已有类型来创建新类型的过程。
这种组合可以通过结构体、枚举、元组等方式实现。
类型组合允许开发者构建复杂的数据结构，同时保持代码的可读性和可维护性。

## 定义

- **类型组合**：
类型组合是将多个类型组合在一起，形成一个新的复合类型。
这种方式使得我们能够创建更复杂的数据结构，能够更好地表达程序的逻辑和数据模型。

## 解释

在Rust中，类型组合的主要方式包括：

1. **结构体（Structs）**：通过定义结构体，可以将多个字段组合在一起，形成一个新的类型。
2. **枚举（Enums）**：通过定义枚举，可以组合不同的变体，每个变体可以包含不同类型的数据。
3. **元组（Tuples）**：元组允许将多个值组合在一起，形成一个单一的复合类型。

类型组合使得我们能够创建更复杂的数据结构，同时保持类型安全。

## 示例

以下是一个使用类型组合的示例：

```rust
// 定义一个结构体来表示一个点
struct Point {
    x: f64,
    y: f64,
}

// 定义一个结构体来表示一个矩形
struct Rectangle {
    top_left: Point,
    bottom_right: Point,
}

// 定义一个函数来计算矩形的面积
fn area(rect: &Rectangle) -> f64 {
    let width = rect.bottom_right.x - rect.top_left.x;
    let height = rect.bottom_right.y - rect.top_left.y;
    width * height
}

fn main() {
    let top_left = Point { x: 0.0, y: 5.0 };
    let bottom_right = Point { x: 5.0, y: 0.0 };
    let rect = Rectangle {
        top_left,
        bottom_right,
    };

    println!("Area of the rectangle: {}", area(&rect)); // 输出: Area of the rectangle: 25
}
```

## 解释示例

1. **定义结构体**：
我们定义了一个名为`Point`的结构体，表示二维空间中的一个点，包含`x`和`y`坐标。
然后，我们定义了一个名为`Rectangle`的结构体，表示一个矩形，
包含两个`Point`类型的字段，分别表示矩形的左上角和右下角。

2. **计算面积**：
我们定义了一个函数`area`，接受一个`Rectangle`的引用作为参数，并计算矩形的面积。
通过访问`Rectangle`中的`Point`字段，我们可以计算矩形的宽度和高度。

3. **使用组合类型**：
在`main`函数中，我们创建了`Point`和`Rectangle`的实例，并调用`area`函数来计算矩形的面积。
通过类型组合，我们能够清晰地表示矩形的结构和计算逻辑。

## 总结

类型组合在Rust中是一种强大的工具，允许开发者通过组合已有类型来创建新的复合类型。
这种方式使得代码更加清晰、可读，并且能够更好地表达数据模型和程序逻辑。
通过使用结构体、枚举和元组，Rust提供了灵活的方式来实现类型组合。

*/
