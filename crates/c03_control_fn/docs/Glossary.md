# C03 控制流与函数: 术语表 (Glossary)

> **文档定位**: 控制流与函数核心术语快速参考  
> **使用方式**: 通过术语索引快速查找定义，理解核心概念  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](../README.md) | [FAQ](./FAQ.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[C](#控制流-control-flow) | [E](#表达式-expression) | [F](#函数-function) | [I](#迭代器-iterator) | [M](#match-表达式) | [N](#never-类型-) | [P](#模式匹配-pattern-matching)

---

## 控制流 (Control Flow)

**定义**: 程序指令执行的顺序和规则。

**Rust特性**:

- 与类型系统深度集成
- 大多数控制结构是表达式
- 编译时保证安全性

**常见结构**:

- `if`/`else`: 条件分支
- `match`: 模式匹配
- `loop`/`while`/`for`: 循环
- `break`/`continue`: 控制跳转

**示例**:

```rust
// if 是表达式
let x = if condition { 1 } else { 0 };

// match 是表达式
let result = match value {
    Some(x) => x,
    None => 0,
};
```

**相关**: [02_basics/01_control_flow_fundamentals.md](./02_basics/01_control_flow_fundamentals.md)

---

## 表达式 (Expression)

**定义**: 能计算并返回一个值的代码片段。

**与语句的区别**:

- **表达式**: 返回值
- **语句**: 执行动作，不返回值（或返回 `()`）

**Rust特性**:

- 大部分控制结构都是表达式
- 不以分号结尾（分号会将表达式转为语句）
- 可组合、可嵌套

**示例**:

```rust
// 表达式
let x = {
    let a = 1;
    let b = 2;
    a + b  // 无分号，返回值
};

// 语句
let y = {
    let a = 1;
    let b = 2;
    a + b; // 有分号，返回 ()
};
```

**相关**: [02_basics/02_conditional_expressions.md](./02_basics/02_conditional_expressions.md)

---

## 函数 (Function)

**定义**: 可复用的代码块，接受参数并可能返回值。

**语法**:

```rust
fn function_name(param: Type) -> ReturnType {
    // 函数体
}
```

**特性**:

- 参数必须显式标注类型
- 返回类型可推导（简单情况）
- 最后一个表达式是返回值

**示例**:

```rust
fn add(x: i32, y: i32) -> i32 {
    x + y  // 返回值
}

fn print_message(msg: &str) {
    println!("{}", msg);
    // 隐式返回 ()
}
```

**相关**: [02_basics/04_functions_and_closures.md](./02_basics/04_functions_and_closures.md)

---

## 闭包 (Closure)

**定义**: 可以捕获其周围环境的匿名函数。

**语法**:

```rust
|param1, param2| expression
|param1, param2| { statements }
```

**捕获方式**:

- **不可变借用**: `Fn`
- **可变借用**: `FnMut`
- **获取所有权**: `FnOnce`

**示例**:

```rust
let x = 5;

// 捕获 x
let add_x = |y| x + y;
println!("{}", add_x(3)); // 8

// 可变捕获
let mut count = 0;
let mut increment = || count += 1;
increment();
```

**相关**: [03_advanced/06_closures_and_fn_traits_1_90.md](./03_advanced/06_closures_and_fn_traits_1_90.md)

---

## Match 表达式

**定义**: 强大的模式匹配控制流结构。

**特性**:

- **穷尽性**: 必须覆盖所有可能的值
- **类型安全**: 所有分支返回相同类型
- **模式**: 支持复杂模式匹配

**示例**:

```rust
match value {
    0 => println!("zero"),
    1 | 2 => println!("one or two"),
    3..=9 => println!("three to nine"),
    _ => println!("other"),
}

// 解构
match point {
    Point { x: 0, y } => println!("on y-axis at {}", y),
    Point { x, y: 0 } => println!("on x-axis at {}", x),
    Point { x, y } => println!("at ({}, {})", x, y),
}
```

**相关**: [03_advanced/02_pattern_matching_advanced_1_90.md](./03_advanced/02_pattern_matching_advanced_1_90.md)

---

## 模式匹配 (Pattern Matching)

**定义**: 检查值的结构并提取其中的数据。

**模式类型**:

- **字面量**: `1`, `"hello"`
- **变量**: `x`, `name`
- **通配符**: `_`
- **范围**: `1..=10`
- **结构体**: `Point { x, y }`
- **枚举**: `Some(x)`, `None`
- **引用**: `&x`
- **守卫**: `if condition`

**示例**:

```rust
// if let
if let Some(x) = option {
    println!("{}", x);
}

// while let
while let Some(x) = stack.pop() {
    println!("{}", x);
}

// let-else
let Some(x) = option else {
    return;
};
```

**相关**: [03_advanced/02_pattern_matching_advanced_1_90.md](./03_advanced/02_pattern_matching_advanced_1_90.md)

---

## 穷尽性 (Exhaustiveness)

**定义**: match 表达式的模式必须覆盖所有可能的输入值。

**编译时检查**: 编译器静态强制执行

**示例**:

```rust
// ✅ 正确：穷尽所有情况
match option {
    Some(x) => println!("{}", x),
    None => println!("none"),
}

// ❌ 错误：缺少 None 分支
match option {
    Some(x) => println!("{}", x),
    // 编译错误：non-exhaustive patterns
}

// ✅ 使用通配符
match value {
    1 => println!("one"),
    2 => println!("two"),
    _ => println!("other"),
}
```

**相关**: [03_advanced/02_pattern_matching_advanced_1_90.md](./03_advanced/02_pattern_matching_advanced_1_90.md)

---

## 迭代器 (Iterator)

**定义**: 实现了 `Iterator` trait 的类型，提供顺序访问元素的方式。

**核心方法**:

```rust
pub trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

**常用方法**:

- `map`: 转换元素
- `filter`: 过滤元素
- `fold`: 累积计算
- `collect`: 收集为集合

**示例**:

```rust
let numbers = vec![1, 2, 3, 4, 5];

let sum: i32 = numbers
    .iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * 2)
    .sum();

println!("{}", sum); // 12
```

**相关**: [03_advanced/07_loops_and_iterators_control_1_90.md](./03_advanced/07_loops_and_iterators_control_1_90.md)

---

## Never 类型 (!)

**定义**: 表示永不返回的类型。

**用途**:

- 发散函数（diverging functions）
- panic、exit、无限循环
- 类型推导的底类型

**示例**:

```rust
// 发散函数
fn exit_program() -> ! {
    std::process::exit(0);
}

// match 中使用
let x: i32 = match value {
    Some(n) => n,
    None => panic!("No value!"), // panic! 返回 !
};

// 无限循环
fn forever() -> ! {
    loop {
        println!("Running...");
    }
}
```

**相关**: [03_advanced/08_never_type_practices_1_90.md](./03_advanced/08_never_type_practices_1_90.md)

---

## ? 运算符 (Question Mark Operator)

**定义**: 用于错误传播的语法糖。

**行为**:

- `Result::Ok(val)` → 解包 `val`
- `Result::Err(e)` → 提前返回 `Err(e)`
- `Option::Some(val)` → 解包 `val`
- `Option::None` → 提前返回 `None`

**自动转换**: 调用 `From::from` 进行类型转换

**示例**:

```rust
fn read_file(path: &str) -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string(path)?;
    Ok(content)
}

// 等价于
fn read_file(path: &str) -> Result<String, std::io::Error> {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => return Err(e),
    };
    Ok(content)
}
```

**相关**: [02_basics/05_error_handling_as_control_flow.md](./02_basics/05_error_handling_as_control_flow.md)

---

## Fn Traits

**定义**: 由编译器自动为闭包实现的 trait。

**三种 trait**:

| Trait | 捕获方式 | 可调用次数 |
|-------|---------|-----------|
| `Fn` | `&self` | 多次 |
| `FnMut` | `&mut self` | 多次 |
| `FnOnce` | `self` | 一次 |

**示例**:

```rust
// Fn
fn call_fn<F>(f: F) where F: Fn() {
    f();
    f(); // 可多次调用
}

// FnMut
fn call_fn_mut<F>(mut f: F) where F: FnMut() {
    f();
    f(); // 可多次调用
}

// FnOnce
fn call_fn_once<F>(f: F) where F: FnOnce() {
    f(); // 只能调用一次
}
```

**相关**: [03_advanced/06_closures_and_fn_traits_1_90.md](./03_advanced/06_closures_and_fn_traits_1_90.md)

---

## 高阶函数 (Higher-Order Function)

**定义**: 接受函数作为参数或返回函数的函数。

**示例**:

```rust
// 接受函数作为参数
fn apply<F>(f: F, x: i32) -> i32 
where 
    F: Fn(i32) -> i32 
{
    f(x)
}

let double = |x| x * 2;
println!("{}", apply(double, 5)); // 10

// 返回函数
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

let add5 = make_adder(5);
println!("{}", add5(3)); // 8
```

**相关**: [02_basics/04_functions_and_closures.md](./02_basics/04_functions_and_closures.md)

---

## Let-Else 模式

**定义**: Rust 1.65+ 引入的模式，用于解包和提前返回。

**语法**:

```rust
let pattern = expression else {
    // 匹配失败时执行
};
```

**示例**:

```rust
fn process(data: Option<String>) -> Result<usize, &'static str> {
    let Some(text) = data else {
        return Err("No data");
    };
    
    Ok(text.len())
}

// 等价于
fn process(data: Option<String>) -> Result<usize, &'static str> {
    match data {
        Some(text) => Ok(text.len()),
        None => Err("No data"),
    }
}
```

**相关**: [03_advanced/04_let_else_patterns_handbook_1_90.md](./03_advanced/04_let_else_patterns_handbook_1_90.md)

---

## 标签块 (Labeled Block)

**定义**: 带有标签的代码块，可用于精确控制 break/continue。

**语法**:

```rust
'label: loop {
    // ...
}
```

**示例**:

```rust
'outer: for i in 0..5 {
    'inner: for j in 0..5 {
        if i * j > 10 {
            break 'outer; // 跳出外层循环
        }
        println!("{} * {} = {}", i, j, i * j);
    }
}

// 带值的 break
let result = 'block: {
    if condition {
        break 'block 42;
    }
    0
};
```

**相关**: [03_advanced/05_labeled_blocks_and_break_values_1_90.md](./03_advanced/05_labeled_blocks_and_break_values_1_90.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](../README.md) - 项目概述
- [理论基础](./01_theory/) - 深入学习
- [核心概念](./02_basics/) - 基础知识
- [高级主题](./03_advanced/) - 进阶内容
- [实践应用](./04_practice/) - 最佳实践

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [完整文档索引](./DOCUMENTATION_INDEX.md)
