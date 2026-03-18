# 声明宏 (Declarative Macros)

> **预计学习时间**: 45-60 分钟
> **难度**: 中级 → 高级
> **版本**: Rust 1.70+

声明宏（`macro_rules!`）是 Rust 中一种强大的元编程工具，允许你创建自定义的 DSL（领域特定语言），减少样板代码，并构建直观的 API。与过程宏不同，声明宏完全在编译器的宏扩展阶段执行，无需额外的 crate。

---

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 理解声明宏的工作原理和适用场景
- [ ] 编写基础的 `macro_rules!` 宏定义
- [ ] 使用模式匹配创建灵活的宏接口
- [ ] 掌握重复模式（`*`, `+`, `?`）处理变长参数
- [ ] 正确选择和使用捕获类型（`expr`, `ty`, `ident` 等）
- [ ] 理解宏卫生性（Hygiene）及其影响
- [ ] 编写递归宏处理嵌套结构
- [ ] 创建实用的工具宏（如 `vec!`, `hashmap!`）

---

## 📋 先决条件

- 熟悉 Rust 基本语法和所有权系统
- 理解模式匹配（`match` 表达式）
- 了解 Rust 模块系统和可见性
- 有使用标准库宏（`vec!`, `println!` 等）的经验

---

## 🧠 核心概念

### 1. 什么是宏？

宏（Macro）是一种**代码生成代码**的机制。与函数不同：

| 特性 | 函数 | 宏 |
|------|------|-----|
| 执行时机 | 运行时 | 编译时 |
| 参数求值 | 立即求值 | 延迟求值（按代码片段处理）|
| 返回值 | 单个值 | 任意代码片段 |
| 类型检查 | 严格的类型系统 | 基于模式匹配 |

**为什么使用宏？**

```rust
// 没有宏：重复的样板代码
let mut v = Vec::new();
v.push(1);
v.push(2);
v.push(3);

// 使用宏：简洁、可读
let v = vec![1, 2, 3];
```

### 2. macro_rules! 基础语法

声明宏使用 `macro_rules!` 关键字定义，遵循模式匹配规则：

```rust
macro_rules! macro_name {
    // 模式1 => 展开代码
    (pattern1) => { expansion1 };

    // 模式2 => 展开代码
    (pattern2) => { expansion2 };
}
```

**最简单的宏：**

```rust
macro_rules! say_hello {
    () => {
        println!("Hello, Macro!");
    };
}

fn main() {
    say_hello!();  // 展开为 println!("Hello, Macro!");
}
```

### 3. 模式匹配

宏的核心是**模式匹配**，类似于 `match` 表达式，但在编译时进行。

```rust
macro_rules! greet {
    // 模式1：无参数
    () => {
        println!("Hello!");
    };

    // 模式2：一个字符串字面量
    ($name:literal) => {
        println!("Hello, {}!", $name);
    };

    // 模式3：两个表达式
    ($greeting:literal, $name:literal) => {
        println!("{}, {}!", $greeting, $name);
    };
}

fn main() {
    greet!();                    // Hello!
    greet!("World");             // Hello, World!
    greet!("Good morning", "Rust");  // Good morning, Rust!
}
```

**重要规则**：宏模式是**贪婪匹配**的，从上到下依次尝试，使用第一个匹配的模式。

### 4. 捕获类型（Captures）

宏使用 `$name:kind` 语法捕获输入的代码片段：

| 捕获类型 | 说明 | 示例 |
|---------|------|------|
| `block` | 代码块 `{ ... }` | `{ let x = 1; x }` |
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `ident` | 标识符（变量名、函数名） | `foo`, `Bar` |
| `item` | 模块级条目 | `fn foo() {}`, `struct Bar;` |
| `literal` | 字面量 | `"hello"`, `42`, `'a'` |
| `pat` | 模式 | `Some(x)`, `(a, b)` |
| `path` | 路径 | `std::option::Option` |
| `stmt` | 语句（不包含分号） | `let x = 1` |
| `tt` | Token Tree（最灵活） | 任意标记 |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `vis` | 可见性修饰符 | `pub`, `pub(crate)` |

**示例：不同类型的捕获**

```rust
macro_rules! create_function {
    // 捕获标识符和表达式
    ($func_name:ident, $body:expr) => {
        fn $func_name() -> i32 {
            $body
        }
    };
}

create_function!(foo, 42);
create_function!(bar, 1 + 2 + 3);

fn main() {
    println!("foo() = {}", foo());  // foo() = 42
    println!("bar() = {}", bar());  // bar() = 6
}
```

### 5. 重复模式

使用重复运算符处理变长参数：

| 运算符 | 含义 | 最少次数 | 最多次数 |
|--------|------|---------|---------|
| `*` | 零次或多次 | 0 | ∞ |
| `+` | 一次或多次 | 1 | ∞ |
| `?` | 零次或一次 | 0 | 1 |

**基本语法**：`$($name:kind),*` （逗号分隔的重复）

```rust
macro_rules! sum {
    // 零个或多个表达式，用逗号分隔
    ($($x:expr),*) => {
        {
            let mut total = 0;
            $(
                total += $x;
            )*
            total
        }
    };
}

fn main() {
    println!("{}", sum!());             // 0
    println!("{}", sum!(1));            // 1
    println!("{}", sum!(1, 2));         // 3
    println!("{}", sum!(1, 2, 3, 4, 5)); // 15
}
```

**处理可选尾随逗号**：

```rust
macro_rules! vec_alt {
    // $(,)? 表示可选的尾随逗号
    ($($x:expr),* $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

fn main() {
    let v1 = vec_alt![1, 2, 3];
    let v2 = vec_alt![1, 2, 3,];  // 尾随逗号也有效
}
```

### 6. 宏卫生性（Macro Hygiene）

Rust 的宏系统具有**卫生性**，意味着宏内部定义的标识符不会与外部冲突。

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42;  // 宏内部定义的 a
            $e
        }
    };
}

fn main() {
    let a = "hello";  // 外部的 a
    let result = using_a!(a);  // 这里的 a 指向外部的 a
    println!("{}", result);  // 输出 "hello"
}
```

**卫生性的好处**：宏不会意外捕获或污染外部作用域的变量。

### 7. 递归宏

宏可以递归调用自身，用于处理嵌套结构。

```rust
macro_rules! my_vec {
    // 基本情况：空列表
    () => {
        Vec::new()
    };

    // 递归情况：至少一个元素
    ($first:expr $(, $rest:expr)*) => {
        {
            let mut v = my_vec!($($rest),*);  // 递归调用
            v.push($first);
            v
        }
    };
}

fn main() {
    let v = my_vec![1, 2, 3];
    println!("{:?}", v);  // [3, 1, 2] - 注意顺序（递归导致）
}
```

**实际应用：hashmap! 宏**

```rust
macro_rules! hashmap {
    // 空 map
    () => {{
        ::std::collections::HashMap::new()
    }};

    // 多个键值对
    ($($key:expr => $value:expr),* $(,)?) => {{
        let mut map = ::std::collections::HashMap::new();
        $(
            map.insert($key, $value);
        )*
        map
    }};
}

fn main() {
    let map = hashmap! {
        "name" => "Alice",
        "age" => 30,
        "city" => "Beijing",
    };
    println!("{:?}", map);
}
```

---

## 💡 最佳实践

### 1. 使用完全限定路径

在宏中使用 `::std::` 或 `::core::` 前缀，避免命名冲突。

```rust
macro_rules! my_vec {
    () => {
        ::std::vec::Vec::new()  // ✅ 完全限定路径
    };
}
```

### 2. 处理多次求值问题

避免在宏中多次使用同一个表达式参数。

```rust
// ❌ 问题：$a 和 $b 可能被求值多次
macro_rules! max {
    ($a:expr, $b:expr) => {
        if $a > $b { $a } else { $b }
    };
}

// ✅ 修复：先绑定到局部变量
macro_rules! max {
    ($a:expr, $b:expr) => {{
        let a = $a;
        let b = $b;
        if a > b { a } else { b }
    }};
}
```

### 3. 处理表达式优先级

在宏中使用括号确保运算优先级。

```rust
// ❌ double!(1 + 2) 展开为 1 + 2 * 2 = 5
macro_rules! double {
    ($x:expr) => { $x * 2 }
}

// ✅ 添加括号
macro_rules! double {
    ($x:expr) => { ($x) * 2 }
}
```

### 4. 接受尾随逗号

在重复模式后添加 `$(,)?` 以接受可选的尾随逗号。

```rust
macro_rules! my_macro {
    ($($x:expr),* $(,)?) => { ... }  // ✅ 接受尾随逗号
}
```

---

## ⚠️ 常见陷阱

### 1. 混淆捕获类型

选择错误的捕获类型会导致解析错误。

```rust
// ❌ 错误：expr 不能匹配模式
macro_rules! bad_match {
    ($pat:expr) => {
        match Some(1) {
            $pat => println!("matched"),  // 错误！
            _ => {}
        }
    };
}

// ✅ 正确：使用 pat 捕获模式
macro_rules! good_match {
    ($pat:pat) => {
        match Some(1) {
            $pat => println!("matched"),
            _ => {}
        }
    };
}
```

### 2. 忘记分号

宏定义中每个规则后需要分号分隔。

```rust
macro_rules! example {
    () => { 1 };  // ✅ 这里有分号
    ($x:expr) => { $x }  // ✅ 最后一个也需要
}
```

### 3. 模式重叠

如果多个模式可以匹配同一输入，只有第一个会被使用。

```rust
macro_rules! ambiguous {
    ($x:expr) => { "expression" };
    ($x:literal) => { "literal" };  // 这行永远不会被匹配
}
```

### 4. 卫生性误解

宏无法直接访问外部作用域的局部变量（除非通过参数传递）。

```rust
fn main() {
    let x = 42;

    // 无法在宏内部直接使用 x
    // 除非通过参数传递
    some_macro!(x);  // ✅ 正确方式
}
```

---

## 🎮 动手练习

### 练习 1：实现 `hashmap!` 宏

创建一个类似 `vec!` 的 `hashmap!` 宏，支持以下用法：

```rust
let map = hashmap! {
    "one" => 1,
    "two" => 2,
    "three" => 3,
};
```

<details>
<summary>参考答案</summary>

```rust
macro_rules! hashmap {
    () => {
        ::std::collections::HashMap::new()
    };
    ($($key:expr => $value:expr),* $(,)?) => {
        {
            let mut map = ::std::collections::HashMap::new();
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
}
```

</details>

### 练习 2：实现 `time!` 宏

创建一个宏，用于测量代码块的执行时间：

```rust
let result = time! {
    std::thread::sleep(std::time::Duration::from_millis(100));
    42
};
```

<details>
<summary>参考答案</summary>

```rust
macro_rules! time {
    ($block:block) => {{
        let start = std::time::Instant::now();
        let result = $block;
        let duration = start.elapsed();
        println!("Time elapsed: {:?}", duration);
        result
    }};
}
```

</details>

### 练习 3：实现 `unwrap_or_return!` 宏

创建一个宏，如果表达式是 `None`，则提前返回：

```rust
fn process_data(data: Option<&str>) -> Result<String, ()> {
    let data = unwrap_or_return!(data, Err(()));
    Ok(data.to_string())
}
```

<details>
<summary>参考答案</summary>

```rust
macro_rules! unwrap_or_return {
    ($opt:expr, $ret:expr) => {
        match $opt {
            Some(v) => v,
            None => return $ret,
        }
    };
}
```

</details>

---

## 📖 延伸阅读

- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) - 最全面的 Rust 宏教程
- [Rust Reference: Macros](https://doc.rust-lang.org/reference/macros.html) - 官方参考文档
- [Rust by Example: Macros](https://doc.rust-lang.org/rust-by-example/macros.html) - 交互式示例
- [Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) - 过程宏（进阶主题）

---

> 💡 **提示**：宏是强大的工具，但正如常说的，"强大的力量伴随着巨大的责任"。在使用宏之前，先考虑是否可以用函数或泛型实现。当确实需要宏的灵活性时，遵循本指南的最佳实践，写出可维护的代码。
