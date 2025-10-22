# C03 控制流与函数: 常见问题解答 (FAQ)

> **文档定位**: 控制流与函数实践中的常见问题快速解答  
> **使用方式**: 遇到问题时快速查找解决方案和最佳实践  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](../README.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 问题解答

---

## 📋 问题索引

**快速跳转**:

- [控制流基础](#控制流基础)
- [模式匹配](#模式匹配)
- [函数与闭包](#函数与闭包)
- [错误处理](#错误处理)
- [性能优化](#性能优化)

---

## 控制流基础

### Q1: 为什么 Rust 的 if 和 match 是表达式而不是语句？

**A**: 将它们设计成表达式有两大好处：

**1. 组合性**:

可以直接在 `let` 语句或其他表达式中使用，使代码更简洁：

```rust
let value = if condition { 
    42 
} else { 
    0 
};

let result = match option {
    Some(x) => x * 2,
    None => 0,
};
```

**2. 类型安全**:

编译器强制所有分支返回相同类型：

```rust
// ✅ 正确：类型一致
let x = if condition { 1 } else { 0 };

// ❌ 错误：类型不一致
let x = if condition { 1 } else { "zero" };
```

**相关**: [02_basics/02_conditional_expressions.md](./02_basics/02_conditional_expressions.md)

---

### Q2: 为什么 for 循环比 while 循环更受推荐？

**A**: for 循环围绕迭代器构建，提供更高安全性和抽象性：

**优势**:

- **自动管理**: 自动处理 `next()`、`None` 检查
- **避免错误**: 消除 "差一错误" (off-by-one errors)
- **通用性**: 统一处理任何可迭代集合
- **性能**: 编译器优化更好

**示例**:

```rust
// ✅ 推荐：for 循环
let numbers = vec![1, 2, 3, 4, 5];
for num in &numbers {
    println!("{}", num);
}

// ⚠️ 不推荐：手动管理索引
let mut i = 0;
while i < numbers.len() {
    println!("{}", numbers[i]);
    i += 1;
}
```

**相关**: [02_basics/03_iterative_constructs.md](./02_basics/03_iterative_constructs.md)

---

## 模式匹配

### Q3: 既然有 match，为什么还需要 if let 和 while let？

**A**: if let 和 while let 是 match 的"人体工程学"语法糖：

**问题**:

当只关心一种模式时，match 显得冗长：

```rust
// 冗长的 match
match some_option {
    Some(value) => println!("Got: {}", value),
    None => {} // 必须处理
}
```

**解决方案**:

```rust
// ✅ 简洁的 if let
if let Some(value) = some_option {
    println!("Got: {}", value);
}

// ✅ while let 用于循环
while let Some(value) = iterator.next() {
    println!("Got: {}", value);
}
```

**相关**: [03_advanced/02_pattern_matching_advanced_1_90.md](./03_advanced/02_pattern_matching_advanced_1_90.md)

---

### Q4: 什么是 let-else 模式？何时使用？

**A**: let-else 是 Rust 1.65+ 的特性，用于模式匹配失败时提前返回：

**语法**:

```rust
let Some(value) = some_option else {
    // 匹配失败时执行
    return Err("No value");
};
// value 在这里可用
```

**适用场景**:

- 需要解包 Option/Result
- 匹配失败需要提前返回
- 避免深层嵌套

**示例**:

```rust
fn process(data: Option<String>) -> Result<usize, String> {
    let Some(text) = data else {
        return Err("No data provided".to_string());
    };
    
    Ok(text.len())
}
```

**相关**: [03_advanced/04_let_else_patterns_handbook_1_90.md](./03_advanced/04_let_else_patterns_handbook_1_90.md)

---

## 函数与闭包

### Q5: Fn、FnMut、FnOnce 三个 trait 有什么区别？

**A**: 它们表示闭包如何捕获环境：

| Trait | 捕获方式 | 可调用次数 | 使用场景 |
|-------|---------|-----------|---------|
| `Fn` | 不可变借用 `&T` | 多次 | 只读访问 |
| `FnMut` | 可变借用 `&mut T` | 多次 | 修改捕获变量 |
| `FnOnce` | 获取所有权 `T` | 一次 | 消耗捕获变量 |

**示例**:

```rust
let x = vec![1, 2, 3];

// Fn: 不可变借用
let print_fn = || println!("{:?}", x);
print_fn(); // 可多次调用

// FnMut: 可变借用
let mut y = vec![1, 2, 3];
let mut push_fn = || y.push(4);
push_fn(); // 可多次调用

// FnOnce: 获取所有权
let z = vec![1, 2, 3];
let consume_fn = || drop(z);
consume_fn(); // 只能调用一次
```

**相关**: [03_advanced/06_closures_and_fn_traits_1_90.md](./03_advanced/06_closures_and_fn_traits_1_90.md)

---

### Q6: 如何返回闭包？

**A**: 闭包大小未知，需要使用 Box 或 impl Trait：

**方案1: `Box<dyn Fn>`**:

```rust
fn make_adder(x: i32) -> Box<dyn Fn(i32) -> i32> {
    Box::new(move |y| x + y)
}

let add5 = make_adder(5);
println!("{}", add5(3)); // 8
```

**方案2: impl Fn** (推荐):

```rust
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

let add5 = make_adder(5);
println!("{}", add5(3)); // 8
```

**区别**:

- `Box<dyn Fn>`: 运行时多态，堆分配
- `impl Fn`: 编译时单态化，零成本

**相关**: [02_basics/04_functions_and_closures.md](./02_basics/04_functions_and_closures.md)

---

## 错误处理

### Q7: 什么时候用 Result，什么时候用 panic！？

**A**: 这是 Rust 错误处理哲学的核心：

**使用 Result**:

- ✅ 错误可预期且可恢复
- ✅ 调用者应该处理错误
- ✅ 库代码的公共 API

**示例**:

```rust
fn read_file(path: &str) -> Result<String, std::io::Error> {
    std::fs::read_to_string(path)
}

match read_file("config.txt") {
    Ok(content) => println!("{}", content),
    Err(e) => eprintln!("Error: {}", e),
}
```

**使用 panic！**:

- ✅ 编程错误（bug）
- ✅ 违反不变量
- ✅ 无法安全继续

**示例**:

```rust
fn divide(a: i32, b: i32) -> i32 {
    if b == 0 {
        panic!("Division by zero!");
    }
    a / b
}

// 或使用 assert
assert!(b != 0, "Division by zero!");
```

**相关**: [02_basics/05_error_handling_as_control_flow.md](./02_basics/05_error_handling_as_control_flow.md)

---

### Q8: ? 运算符如何工作？

**A**: `?` 是错误传播的语法糖：

**展开前**:

```rust
fn process() -> Result<String, Error> {
    let file = File::open("data.txt")?;
    let content = read_content(file)?;
    Ok(content)
}
```

**展开后**:

```rust
fn process() -> Result<String, Error> {
    let file = match File::open("data.txt") {
        Ok(f) => f,
        Err(e) => return Err(e.into()),
    };
    
    let content = match read_content(file) {
        Ok(c) => c,
        Err(e) => return Err(e.into()),
    };
    
    Ok(content)
}
```

**注意**: `?` 会自动调用 `From::from` 进行类型转换

**相关**: [02_basics/05_error_handling_as_control_flow.md](./02_basics/05_error_handling_as_control_flow.md)

---

## 性能优化

### Q9: match vs if let vs if-else，性能有差异吗？

**A**: 在大多数情况下性能相同，选择基于可读性：

**性能分析**:

- **编译后**: 三者生成相同的机器码
- **优化**: 编译器会优化为相同形式
- **差异**: 仅在代码生成阶段可能有微小差异

**选择建议**:

```rust
// ✅ match: 多个模式
match value {
    1 => println!("one"),
    2 => println!("two"),
    _ => println!("other"),
}

// ✅ if let: 只关心一个模式
if let Some(x) = option {
    println!("{}", x);
}

// ✅ if-else: 简单布尔条件
if condition {
    do_something();
} else {
    do_other();
}
```

**相关**: [04_practice/03_control_flow_performance_practices_1_90.md](./04_practice/03_control_flow_performance_practices_1_90.md)

---

### Q10: 如何避免闭包的性能开销？

**A**: 使用以下策略优化：

**策略1: 避免不必要的捕获**:

```rust
// ❌ 捕获整个结构
let data = LargeStruct::new();
let closure = || data.field;

// ✅ 只捕获需要的字段
let field = data.field;
let closure = || field;
```

**策略2: 使用 impl Fn 而非 `Box<dyn Fn>`**:

```rust
// ❌ 动态分发
fn make_fn() -> Box<dyn Fn(i32) -> i32> {
    Box::new(|x| x * 2)
}

// ✅ 静态分发
fn make_fn() -> impl Fn(i32) -> i32 {
    |x| x * 2
}
```

**策略3: 内联**:

```rust
#[inline]
fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}
```

**相关**: [04_practice/03_control_flow_performance_practices_1_90.md](./04_practice/03_control_flow_performance_practices_1_90.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [README](../README.md) - 项目概述
- [Glossary](./Glossary.md) - 核心术语表
- [基础知识](./02_basics/) - 基础学习路径
- [高级主题](./03_advanced/) - 进阶内容
- [实践指南](./04_practice/) - 最佳实践

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [完整文档索引](./DOCUMENTATION_INDEX.md)
