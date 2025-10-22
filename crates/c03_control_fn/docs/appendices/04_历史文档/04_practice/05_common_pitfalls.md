# 05. 常见陷阱与解决方案

本文档总结在使用 Rust 控制流时常见的错误、陷阱以及相应的解决方案。

## 目录

- [05. 常见陷阱与解决方案](#05-常见陷阱与解决方案)
  - [目录](#目录)
  - [借用检查器相关](#借用检查器相关)
    - [陷阱1：跨分支的可变借用](#陷阱1跨分支的可变借用)
    - [陷阱2：循环中的借用](#陷阱2循环中的借用)
    - [陷阱3：if let 与可变借用](#陷阱3if-let-与可变借用)
  - [闭包捕获问题](#闭包捕获问题)
    - [陷阱4：意外的移动捕获](#陷阱4意外的移动捕获)
    - [陷阱5：闭包生命周期问题](#陷阱5闭包生命周期问题)
  - [模式匹配常见错误](#模式匹配常见错误)
    - [陷阱6：不穷尽的 match](#陷阱6不穷尽的-match)
    - [陷阱7：过度使用 unwrap](#陷阱7过度使用-unwrap)
    - [陷阱8：忘记处理 None 的情况](#陷阱8忘记处理-none-的情况)
  - [生命周期与控制流](#生命周期与控制流)
    - [陷阱9：返回局部变量的引用](#陷阱9返回局部变量的引用)
    - [陷阱10：if let 中的生命周期](#陷阱10if-let-中的生命周期)
  - [性能陷阱](#性能陷阱)
    - [陷阱11：不必要的克隆](#陷阱11不必要的克隆)
    - [陷阱12：循环中的分配](#陷阱12循环中的分配)
    - [陷阱13：过度使用 match](#陷阱13过度使用-match)
  - [最佳实践总结](#最佳实践总结)
    - [借用检查器](#借用检查器)
    - [闭包](#闭包)
    - [模式匹配](#模式匹配)
    - [性能](#性能)
  - [调试技巧](#调试技巧)
    - [1. 使用编译器错误消息](#1-使用编译器错误消息)
    - [2. 使用 `cargo expand` 查看宏展开](#2-使用-cargo-expand-查看宏展开)
    - [3. 使用 `dbg!` 宏调试](#3-使用-dbg-宏调试)
  - [总结](#总结)

## 借用检查器相关

### 陷阱1：跨分支的可变借用

**问题描述**：

```rust
fn problematic_borrow(flag: bool, data: &mut Vec<i32>) {
    let reference = if flag {
        &mut data[0]  // 可变借用
    } else {
        &mut data[1]  // 另一个可变借用
    };
    
    *reference = 42;
    data.push(100);  // ❌ 错误：data 已被借用
}
```

**解决方案**：

```rust
// 方案 1：限制借用的作用域
fn fixed_borrow_v1(flag: bool, data: &mut Vec<i32>) {
    {
        let reference = if flag {
            &mut data[0]
        } else {
            &mut data[1]
        };
        *reference = 42;
    }  // 借用在这里结束
    
    data.push(100);  // ✅ 正确
}

// 方案 2：使用索引而非引用
fn fixed_borrow_v2(flag: bool, data: &mut Vec<i32>) {
    let index = if flag { 0 } else { 1 };
    data[index] = 42;
    data.push(100);  // ✅ 正确
}

// 方案 3：使用 get_mut
fn fixed_borrow_v3(flag: bool, data: &mut Vec<i32>) {
    let index = if flag { 0 } else { 1 };
    if let Some(elem) = data.get_mut(index) {
        *elem = 42;
    }
    data.push(100);  // ✅ 正确
}
```

### 陷阱2：循环中的借用

**问题描述**：

```rust
fn problematic_loop(items: &mut Vec<String>) {
    for item in items.iter() {
        if item.is_empty() {
            items.push("default".to_string());  // ❌ 错误：同时借用
        }
    }
}
```

**解决方案**：

```rust
// 方案 1：收集索引
fn fixed_loop_v1(items: &mut Vec<String>) {
    let empty_indices: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, item)| item.is_empty())
        .map(|(i, _)| i)
        .collect();
    
    for _ in empty_indices {
        items.push("default".to_string());
    }
}

// 方案 2：克隆后修改
fn fixed_loop_v2(items: &mut Vec<String>) {
    let to_add = items.iter().filter(|s| s.is_empty()).count();
    for _ in 0..to_add {
        items.push("default".to_string());
    }
}

// 方案 3：使用 retain + extend
fn fixed_loop_v3(items: &mut Vec<String>) {
    let empty_count = items.iter().filter(|s| s.is_empty()).count();
    items.extend(std::iter::repeat("default".to_string()).take(empty_count));
}
```

### 陷阱3：if let 与可变借用

**问题描述**：

```rust
fn problematic_if_let(opt: &mut Option<String>, backup: &String) {
    if let Some(ref mut s) = opt {
        *s = backup.clone();  // 可变借用 opt
    }
    
    *opt = None;  // ❌ 错误：opt 已被借用
}
```

**解决方案**：

```rust
// 方案 1：使用 as_mut
fn fixed_if_let_v1(opt: &mut Option<String>, backup: &String) {
    if let Some(s) = opt.as_mut() {
        *s = backup.clone();
    }  // 借用结束
    
    *opt = None;  // ✅ 正确
}

// 方案 2：使用 match
fn fixed_if_let_v2(opt: &mut Option<String>, backup: &String) {
    match opt {
        Some(s) => *s = backup.clone(),
        None => {}
    }
    
    *opt = None;  // ✅ 正确
}

// 方案 3：使用 replace
fn fixed_if_let_v3(opt: &mut Option<String>, backup: &String) {
    if opt.is_some() {
        *opt = Some(backup.clone());
    }
    *opt = None;  // ✅ 正确
}
```

## 闭包捕获问题

### 陷阱4：意外的移动捕获

**问题描述**：

```rust
fn problematic_closure() {
    let data = vec![1, 2, 3];
    
    let closure = || {
        println!("{:?}", data);  // 移动捕获 data
    };
    
    closure();
    println!("{:?}", data);  // ❌ 错误：data 已被移动
}
```

**解决方案**：

```rust
// 方案 1：显式借用
fn fixed_closure_v1() {
    let data = vec![1, 2, 3];
    
    let closure = || {
        println!("{:?}", &data);  // 借用而非移动
    };
    
    closure();
    println!("{:?}", data);  // ✅ 正确
}

// 方案 2：使用 move 并克隆
fn fixed_closure_v2() {
    let data = vec![1, 2, 3];
    let data_clone = data.clone();
    
    let closure = move || {
        println!("{:?}", data_clone);
    };
    
    closure();
    println!("{:?}", data);  // ✅ 正确
}

// 方案 3：使用引用
fn fixed_closure_v3() {
    let data = vec![1, 2, 3];
    
    let closure = |d: &Vec<i32>| {
        println!("{:?}", d);
    };
    
    closure(&data);
    println!("{:?}", data);  // ✅ 正确
}
```

### 陷阱5：闭包生命周期问题

**问题描述**：

```rust
fn problematic_lifetime() -> impl Fn() -> &'static str {
    let local = String::from("hello");
    
    move || {
        local.as_str()  // ❌ 错误：返回局部变量的引用
    }
}
```

**解决方案**：

```rust
// 方案 1：返回所有权
fn fixed_lifetime_v1() -> impl Fn() -> String {
    let local = String::from("hello");
    
    move || {
        local.clone()  // ✅ 返回克隆
    }
}

// 方案 2：使用静态生命周期
fn fixed_lifetime_v2() -> impl Fn() -> &'static str {
    || "hello"  // ✅ 使用字符串字面量
}

// 方案 3：使用 Arc
use std::sync::Arc;

fn fixed_lifetime_v3() -> impl Fn() -> Arc<str> {
    let local = Arc::from("hello");
    
    move || {
        Arc::clone(&local)  // ✅ 使用引用计数
    }
}
```

## 模式匹配常见错误

### 陷阱6：不穷尽的 match

**问题描述**：

```rust
enum Status {
    Active,
    Inactive,
    Pending,
}

fn problematic_match(status: Status) -> &'static str {
    match status {
        Status::Active => "运行中",
        Status::Inactive => "已停止",
        // ❌ 错误：未处理 Status::Pending
    }
}
```

**解决方案**：

```rust
// 方案 1：添加所有分支
fn fixed_match_v1(status: Status) -> &'static str {
    match status {
        Status::Active => "运行中",
        Status::Inactive => "已停止",
        Status::Pending => "等待中",  // ✅ 处理所有情况
    }
}

// 方案 2：使用通配符
fn fixed_match_v2(status: Status) -> &'static str {
    match status {
        Status::Active => "运行中",
        _ => "其他状态",  // ✅ 处理剩余情况
    }
}
```

### 陷阱7：过度使用 unwrap

**问题描述**：

```rust
fn problematic_unwrap(s: &str) -> i32 {
    s.parse::<i32>().unwrap()  // ❌ 可能 panic
}
```

**解决方案**：

```rust
// 方案 1：使用 match
fn fixed_unwrap_v1(s: &str) -> Option<i32> {
    match s.parse::<i32>() {
        Ok(n) => Some(n),
        Err(_) => None,
    }
}

// 方案 2：使用 ? 操作符
fn fixed_unwrap_v2(s: &str) -> Result<i32, std::num::ParseIntError> {
    let n = s.parse::<i32>()?;
    Ok(n)
}

// 方案 3：使用 unwrap_or
fn fixed_unwrap_v3(s: &str) -> i32 {
    s.parse::<i32>().unwrap_or(0)
}

// 方案 4：使用 expect 提供更好的错误消息
fn fixed_unwrap_v4(s: &str) -> i32 {
    s.parse::<i32>()
        .expect(&format!("无法解析 '{}' 为整数", s))
}
```

### 陷阱8：忘记处理 None 的情况

**问题描述**：

```rust
fn problematic_option(opt: Option<i32>) -> i32 {
    match opt {
        Some(n) => n * 2,
        // ❌ 忘记处理 None
    }
}
```

**解决方案**：

```rust
// 方案 1：完整 match
fn fixed_option_v1(opt: Option<i32>) -> i32 {
    match opt {
        Some(n) => n * 2,
        None => 0,  // ✅ 处理 None
    }
}

// 方案 2：使用 unwrap_or
fn fixed_option_v2(opt: Option<i32>) -> i32 {
    opt.map(|n| n * 2).unwrap_or(0)
}

// 方案 3：使用 unwrap_or_else
fn fixed_option_v3(opt: Option<i32>) -> i32 {
    opt.map(|n| n * 2).unwrap_or_else(|| {
        eprintln!("警告：使用默认值");
        0
    })
}
```

## 生命周期与控制流

### 陷阱9：返回局部变量的引用

**问题描述**：

```rust
fn problematic_reference() -> &'static str {
    let local = String::from("hello");
    &local  // ❌ 错误：返回局部变量的引用
}
```

**解决方案**：

```rust
// 方案 1：返回所有权
fn fixed_reference_v1() -> String {
    let local = String::from("hello");
    local  // ✅ 移动所有权
}

// 方案 2：使用静态生命周期
fn fixed_reference_v2() -> &'static str {
    "hello"  // ✅ 字符串字面量
}

// 方案 3：使用 Box
fn fixed_reference_v3() -> Box<str> {
    Box::from("hello")
}
```

### 陷阱10：if let 中的生命周期

**问题描述**：

```rust
fn problematic_if_let_lifetime<'a>(opt: &'a Option<String>) -> &'a str {
    if let Some(ref s) = opt {
        s  // ❌ 生命周期不匹配
    } else {
        "default"
    }
}
```

**解决方案**：

```rust
// 方案 1：使用 as_ref
fn fixed_if_let_lifetime_v1<'a>(opt: &'a Option<String>) -> &'a str {
    match opt.as_ref() {
        Some(s) => s.as_str(),
        None => "default",
    }
}

// 方案 2：使用 match
fn fixed_if_let_lifetime_v2<'a>(opt: &'a Option<String>) -> &'a str {
    match opt {
        Some(s) => s.as_str(),
        None => "default",
    }
}

// 方案 3：使用 map_or
fn fixed_if_let_lifetime_v3<'a>(opt: &'a Option<String>) -> &'a str {
    opt.as_ref().map_or("default", |s| s.as_str())
}
```

## 性能陷阱

### 陷阱11：不必要的克隆

**问题描述**：

```rust
fn problematic_clone(data: &Vec<String>) -> Vec<String> {
    let mut result = Vec::new();
    
    for item in data {
        result.push(item.clone());  // ⚠️ 可能不必要的克隆
    }
    
    result
}
```

**解决方案**：

```rust
// 方案 1：使用引用
fn fixed_clone_v1(data: &Vec<String>) -> Vec<&String> {
    data.iter().collect()
}

// 方案 2：仅在必要时克隆
fn fixed_clone_v2(data: &Vec<String>, filter: fn(&String) -> bool) -> Vec<String> {
    data.iter()
        .filter(|s| filter(s))
        .cloned()
        .collect()
}

// 方案 3：使用 Cow（写时复制）
use std::borrow::Cow;

fn fixed_clone_v3<'a>(data: &'a Vec<String>, modify: bool) -> Vec<Cow<'a, str>> {
    data.iter()
        .map(|s| {
            if modify {
                Cow::Owned(s.to_uppercase())
            } else {
                Cow::Borrowed(s.as_str())
            }
        })
        .collect()
}
```

### 陷阱12：循环中的分配

**问题描述**：

```rust
fn problematic_allocation(n: usize) -> Vec<Vec<i32>> {
    let mut result = Vec::new();
    
    for i in 0..n {
        let mut inner = Vec::new();  // ⚠️ 每次迭代都分配
        inner.push(i as i32);
        result.push(inner);
    }
    
    result
}
```

**解决方案**：

```rust
// 方案 1：预分配容量
fn fixed_allocation_v1(n: usize) -> Vec<Vec<i32>> {
    let mut result = Vec::with_capacity(n);  // ✅ 预分配
    
    for i in 0..n {
        let mut inner = Vec::with_capacity(1);
        inner.push(i as i32);
        result.push(inner);
    }
    
    result
}

// 方案 2：使用迭代器
fn fixed_allocation_v2(n: usize) -> Vec<Vec<i32>> {
    (0..n)
        .map(|i| vec![i as i32])
        .collect()
}
```

### 陷阱13：过度使用 match

**问题描述**：

```rust
fn problematic_match_perf(opt: Option<i32>) -> i32 {
    match opt {
        Some(n) => n,
        None => 0,
    }
}

// 在热循环中反复调用
fn hot_loop(opts: &[Option<i32>]) -> i32 {
    let mut sum = 0;
    for opt in opts {
        sum += problematic_match_perf(*opt);  // ⚠️ 重复 match
    }
    sum
}
```

**解决方案**：

```rust
// 方案 1：使用 unwrap_or
fn fixed_match_perf_v1(opt: Option<i32>) -> i32 {
    opt.unwrap_or(0)  // ✅ 内联更好
}

// 方案 2：在循环中直接处理
fn fixed_hot_loop(opts: &[Option<i32>]) -> i32 {
    opts.iter()
        .map(|opt| opt.unwrap_or(0))
        .sum()
}

// 方案 3：使用 filter_map 跳过 None
fn fixed_hot_loop_v2(opts: &[Option<i32>]) -> i32 {
    opts.iter()
        .filter_map(|&opt| opt)
        .sum()
}
```

## 最佳实践总结

### 借用检查器

1. ✅ 限制借用的作用域
2. ✅ 使用索引而非多重引用
3. ✅ 先借用后修改，避免交错

### 闭包

1. ✅ 明确指定捕获方式（`move` 或借用）
2. ✅ 避免捕获不必要的变量
3. ✅ 注意闭包的生命周期

### 模式匹配

1. ✅ 始终处理所有情况
2. ✅ 避免使用 `unwrap`，使用 `?` 或 `match`
3. ✅ 使用 `let-else` 简化提前返回

### 性能

1. ✅ 预分配集合容量
2. ✅ 避免不必要的克隆
3. ✅ 使用迭代器替代循环
4. ✅ 在热路径上使用简单的控制流

## 调试技巧

### 1. 使用编译器错误消息

```bash
# 编译器会提供详细的错误信息
cargo check
cargo clippy
```

### 2. 使用 `cargo expand` 查看宏展开

```bash
cargo install cargo-expand
cargo expand
```

### 3. 使用 `dbg!` 宏调试

```rust
fn debug_example(x: i32) -> i32 {
    dbg!(&x);  // 打印变量及其值
    let result = x * 2;
    dbg!(result)  // 返回并打印结果
}
```

## 总结

避免这些常见陷阱的关键：

1. **理解所有权系统**：掌握移动、借用、生命周期
2. **利用编译器**：仔细阅读错误消息
3. **使用标准库**：优先使用标准方法而非手写逻辑
4. **性能意识**：在热路径上关注性能
5. **测试验证**：编写测试确保正确性

---

**相关章节**：

- [函数与闭包实践](./01_functions_closures_practice.md)
- [错误处理实践](./02_error_handling_practice.md)
- [控制流性能实践](./03_control_flow_performance_practices_1_90.md)

---

*最后更新：2025年1月*  
*文档版本：v1.0*  
*Rust 版本：1.90+*
