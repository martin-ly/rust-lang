# 03. 循环结构体体体 (Iterative Constructs)

循环结构体体体是重复执行代码块的基础。Rust 提供了多种循环机制，每种都有其特定的用途和语义，并且都与所有权系统紧密集成以保证安全。

## 3.1. 无限循环: `loop`

`loop` 关键字创建一个无限循环，只能通过 `break` 关键字显式退出。

**核心特征**:
`loop` 是一种表达式，它可以**通过 `break` 返回一个值**。这使得它在某些模式下非常有用，例如"重试操作直到成功"。

**类型与所有权约束**:

* 如果 `loop` 被用作表达式，则所有可能的 `break` 路径都必须返回相同类型的值。
* 循环体内的借用必须在循环的单次迭代内结束，不能泄露到下一次迭代或循环外部，除非该借用是对循环外数据的持续借用。

**代码示例**:

```rust
let mut counter = 0;
let result = loop {
    counter += 1;
    if counter == 5 {
        // 从循环中返回值
        break counter * 2;
    }
};
// result 的值为 10
println!("Result from loop: {}", result);
```

## 3.2. 条件循环: `while` 与 `while let`

### 3.2.1. `while` 循环

`while condition { ... }` 在每次迭代开始前检查一个布尔条件。只要条件为 `true`，循环体就会继续执行。

```rust
let mut number = 3;
while number != 0 {
    println!("{}!", number);
    number -= 1;
}
println!("LIFTOFF!!!");
```

### 3.2.2. `while let` 循环

`while let` 是 `while` 和 `if let` 的结合，它允许循环在模式匹配成功时持续进行。这对于处理像迭代器或 `Option` 这样每次迭代都可能产生新值的序列非常有用。

**语义**:
`while let pattern = expression { ... }` 等价于：

```rust
loop {
    match expression {
        pattern => { ... }, // 循环体
        _ => { break; },   // 模式不匹配则退出
    }
}
```

**用例**:
通常用于消耗一个数据结构体体体，例如从 `Vec` 中 `pop` 元素直到它变空。

```rust
let mut stack = vec![1, 2, 3];

// 只要 `stack.pop()` 返回 `Some(value)`，循环就继续
while let Some(top) = stack.pop() {
    // `top` 拥有从 vector 中弹出的值的所有权
    println!("Popped: {}", top);
}
// 循环结束后, stack 为空
```

## 3.3. 迭代循环: `for`

`for` 循环是 Rust 中最常用、最符合人体工程学的循环结构体体体。它用于遍历任何实现了 `IntoIterator` trait 的类型。

**核心机制: `IntoIterator` Trait**

`for` 循环的核心是 `IntoIterator` trait。任何实现了该 trait 的类型都可以通过调用 `.into_iter()` 方法转换成一个**迭代器 (Iterator)**。

迭代器是一个实现了 `Iterator` trait 的结构体体体，其关键方法是 `next(&mut self)`，该方法在每次调用时返回一个 `Option<Self::Item>`。

* `Some(item)`: 序列中的下一个元素。
* `None`: 序列结束。

`for` 循环会自动处理这一切：调用 `.into_iter()`，然后重复调用 `.next()` 并将结果解包，直到收到 `None` 为止。

**所有权的三种迭代形式**:

`for` 循环可以以三种方式迭代集合，这取决于调用的是哪个版本的 `into_iter`：

1. **`into_iter()` (按值, 消耗所有权)**:
    * `for item in collection`
    * 迭代器返回集合中每个元素的**所有权**。集合本身被移动（消耗），在循环后不再可用。适用于你需要在循环体内获得每个元素所有权的场景。

2. **`iter()` (按不可变引用, 借用)**:
    * `for item in &collection`
    * 这是最常见的形式。迭代器返回每个元素的**不可变引用** (`&T`)。集合本身被不可变地借用，在循环后仍然可用。

3. **`iter_mut()` (按可变引用, 可变借用)**:
    * `for item in &mut collection`
    * 迭代器返回每个元素的**可变引用** (`&mut T`)。集合本身被可变地借用，允许在循环中修改其内容。

**代码示例**:

```rust
// 1. iter() - 不可变借用
let names = vec!["Alice", "Bob"];
for name in &names {
    println!("Hello, {}!", name); // name 的类型是 &&str
}
println!("Names vector still available: {:?}", names);

// 2. iter_mut() - 可变借用
let mut numbers = vec![1, 2, 3];
for num in &mut numbers {
    *num *= 2; // 使用 `*` 解引用来修改值
}
println!("Modified numbers: {:?}", numbers);

// 3. into_iter() - 移动所有权
let owned_names = vec![String::from("Alice"), String::from("Bob")];
for name in owned_names {
    // name 的类型是 String，拥有所有权
    println!("Processing owned name: {}", name);
}
// `owned_names` 在此已不可用，已被消耗
// println!("{:?}", owned_names); // 编译错误
```

## 3.4. 控制循环: `break` 与 `continue`

* `break`: 立即终止当前循环。如果循环是 `loop` 表达式，可以带一个值返回。
* `continue`: 立即结束当前这次迭代，并开始下一次迭代。

Rust 还支持**带标签的 `break` 和 `continue`**，用于从嵌套循环中控制外层循环。

```rust
'outer: loop { // 给外层循环一个标签 'outer
    println!("Entered the outer loop");
    'inner: loop {
        println!("Entered the inner loop");
        // break; // 只会退出内层循环
        break 'outer; // 退出外层循环
    }
    println!("This point will not be reached");
}
println!("Exited the outer loop");
```

---

## 批判性分析

* Rust 迭代结构体体体强调类型安全和零成本抽象，标准库 Iterator trait 支持高效链式操作，但自定义复杂迭代器实现有一定门槛。

* 与 C++ STL、Python 生成器等相比，Rust 迭代器更注重静态检查和性能，但表达能力略逊于动态语言。
* 在高性能、嵌入式等场景，Rust 迭代结构体体体优势明显，但生态和工具链对高级用法支持仍有提升空间。

## 典型案例

* 使用 for、while、loop 实现多样化迭代控制。

* 结合 Iterator trait 实现高效链式数据处理。
* 在嵌入式和并发场景下，利用迭代结构体体体优化资源利用和系统响应。

---

**章节导航:**

* **上一章 ->** `02_conditional_expressions.md`
* **下一章 ->** `04_functions_and_closures.md`: 讨论函数和闭包如何作为控制流的一部分。
* **返回目录 ->** `_index.md`

"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 概述
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 形式化分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


