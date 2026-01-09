# 🦀 所有权系统速查卡

> **快速参考** | [完整文档](../../crates/c01_ownership_borrow_scope/docs/) | [代码示例](../../crates/c01_ownership_borrow_scope/examples/)
> **最后更新**: 2025-12-11 | **Rust 版本**: 1.92.0+ | **Edition**: 2024

---

## 📋 目录

- [🦀 所有权系统速查卡](#-所有权系统速查卡)
  - [📋 目录](#-目录)
  - [📐 三大规则（核心）](#-三大规则核心)
  - [🎯 常见模式速查](#-常见模式速查)
    - [模式 1: 所有权转移（Move）](#模式-1-所有权转移move)
    - [模式 2: 不可变借用（\&T）](#模式-2-不可变借用t)
    - [模式 3: 可变借用（\&mut T）](#模式-3-可变借用mut-t)
    - [模式 4: Clone（显式复制）](#模式-4-clone显式复制)
    - [模式 5: Copy 类型](#模式-5-copy-类型)
  - [🌳 决策树](#-决策树)
  - [⚡ 常见错误与解决](#-常见错误与解决)
    - [错误 1: 借用检查器错误](#错误-1-借用检查器错误)
    - [错误 2: 悬垂引用](#错误-2-悬垂引用)
    - [错误 3: 循环中的借用](#错误-3-循环中的借用)
  - [🏗️ 智能指针速查](#️-智能指针速查)
    - [`Box<T>` - 堆分配](#boxt---堆分配)
    - [`Rc<T>` - 引用计数（单线程）](#rct---引用计数单线程)
    - [`Arc<T>` - 原子引用计数（多线程）](#arct---原子引用计数多线程)
    - [`RefCell<T>` - 内部可变性（单线程）](#refcellt---内部可变性单线程)
    - [`Mutex<T>` - 互斥锁（多线程）](#mutext---互斥锁多线程)
  - [🎓 生命周期速查](#-生命周期速查)
    - [基本语法](#基本语法)
    - [生命周期省略规则](#生命周期省略规则)
  - [📊 性能提示](#-性能提示)
    - [✅ 高效模式](#-高效模式)
    - [⚠️ 低效模式](#️-低效模式)
  - [🔗 快速跳转](#-快速跳转)
    - [深入学习](#深入学习)
    - [代码示例](#代码示例)
    - [形式化理论](#形式化理论)
  - [🆕 Rust 1.92.0 内存优化](#-rust-1920-内存优化)
    - [内存分配优化](#内存分配优化)


---

## 📐 三大规则（核心）

```text
1. 每个值有且仅有一个所有者
2. 同一时刻只能有一个所有者
3. 所有者离开作用域，值被自动 drop
```

---

## 🎯 常见模式速查

### 模式 1: 所有权转移（Move）

```rust
let s1 = String::from("hello");
let s2 = s1;  // s1 失效，所有权转移给 s2
// println!("{}", s1); // ❌ 编译错误
println!("{}", s2);    // ✅ OK
```

**何时发生**:

- 赋值: `let b = a;`
- 函数参数: `fn take(s: String)`
- 返回值: `return s;`

---

### 模式 2: 不可变借用（&T）

```rust
fn process(s: &String) {  // 借用，不夺取所有权
    println!("{}", s);
}

let s = String::from("hello");
process(&s);  // 借用
println!("{}", s);  // ✅ s 仍然有效
```

**规则**:

- ✅ 可以有多个不可变借用
- ✅ 读取数据
- ❌ 不能修改数据

---

### 模式 3: 可变借用（&mut T）

```rust
fn modify(s: &mut String) {
    s.push_str(" world");
}

let mut s = String::from("hello");
modify(&mut s);
println!("{}", s);  // "hello world"
```

**规则**:

- ✅ 可以修改数据
- ⚠️ 同一时刻只能有一个可变借用
- ⚠️ 可变借用与不可变借用不能共存

---

### 模式 4: Clone（显式复制）

```rust
let s1 = String::from("hello");
let s2 = s1.clone();  // 显式深拷贝
println!("{} {}", s1, s2);  // ✅ 都有效
```

**代价**: 堆内存分配，性能开销

---

### 模式 5: Copy 类型

```rust
let x = 5;
let y = x;  // i32 实现了 Copy
println!("{} {}", x, y);  // ✅ 都有效
```

**实现 Copy 的类型**:

- 所有整数类型: `i32`, `u64`, etc.
- 浮点类型: `f32`, `f64`
- 布尔: `bool`
- 字符: `char`
- 元组（如果所有成员都是 Copy）

---

## 🌳 决策树

```text
遇到所有权问题？
│
├─ 需要修改数据？
│  ├─ 是 → 使用 &mut T
│  └─ 否 → 使用 &T
│
├─ 需要在多处共享？
│  ├─ 单线程
│  │  ├─ 不可变 → Rc<T>
│  │  └─ 可变 → Rc<RefCell<T>>
│  └─ 多线程
│     ├─ 不可变 → Arc<T>
│     └─ 可变 → Arc<Mutex<T>> 或 Arc<RwLock<T>>
│
└─ 需要自引用结构？
   └─ Pin<Box<T>>
```

---

## ⚡ 常见错误与解决

### 错误 1: 借用检查器错误

```rust
// ❌ 错误
let mut s = String::from("hello");
let r1 = &s;
let r2 = &mut s;  // 错误：不可变借用期间不能可变借用
println!("{}", r1);
```

```rust
// ✅ 解决
let mut s = String::from("hello");
let r1 = &s;
println!("{}", r1);  // r1 的作用域结束
let r2 = &mut s;     // ✅ OK
s.push_str(" world");
```

---

### 错误 2: 悬垂引用

```rust
// ❌ 错误
fn dangle() -> &String {
    let s = String::from("hello");
    &s  // s 将被 drop，引用无效
}
```

```rust
// ✅ 解决方案 1: 返回所有权
fn no_dangle() -> String {
    let s = String::from("hello");
    s  // 所有权转移
}

// ✅ 解决方案 2: 使用生命周期
fn no_dangle2<'a>(input: &'a String) -> &'a String {
    input
}
```

---

### 错误 3: 循环中的借用

```rust
// ❌ 错误
let mut v = vec![1, 2, 3];
for i in &v {
    v.push(*i);  // 错误：遍历时不能修改
}
```

```rust
// ✅ 解决
let mut v = vec![1, 2, 3];
let to_add: Vec<_> = v.iter().map(|x| *x).collect();
v.extend(to_add);
```

---

## 🏗️ 智能指针速查

### `Box<T>` - 堆分配

```rust
let b = Box::new(5);
// 用途：递归类型、大型数据、trait 对象
```

### `Rc<T>` - 引用计数（单线程）

```rust
use std::rc::Rc;
let a = Rc::new(5);
let b = Rc::clone(&a);  // 引用计数 +1
// 用途：多重所有权（单线程）
```

### `Arc<T>` - 原子引用计数（多线程）

```rust
use std::sync::Arc;
let a = Arc::new(5);
let b = Arc::clone(&a);  // 线程安全的引用计数
// 用途：多线程共享数据
```

### `RefCell<T>` - 内部可变性（单线程）

```rust
use std::cell::RefCell;
let data = RefCell::new(5);
*data.borrow_mut() += 1;
// 用途：运行时借用检查
```

### `Mutex<T>` - 互斥锁（多线程）

```rust
use std::sync::Mutex;
let m = Mutex::new(5);
{
    let mut num = m.lock().unwrap();
    *num += 1;
}
// 用途：多线程可变共享
```

---

## 🎓 生命周期速查

### 基本语法

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 生命周期省略规则

1. **规则 1**: 每个引用参数获得独立生命周期

   ```rust
   fn foo(x: &i32)          // fn foo<'a>(x: &'a i32)
   fn foo(x: &i32, y: &i32) // fn foo<'a, 'b>(x: &'a i32, y: &'b i32)
   ```

2. **规则 2**: 单参数时，返回值使用相同生命周期

   ```rust
   fn foo(x: &i32) -> &i32  // fn foo<'a>(x: &'a i32) -> &'a i32
   ```

3. **规则 3**: 方法中，返回值使用 `&self` 的生命周期

   ```rust
   fn method(&self) -> &str // fn method<'a>(&'a self) -> &'a str
   ```

---

## 📊 性能提示

### ✅ 高效模式

1. **借用而非拥有**

   ```rust
   fn process(s: &String) { ... }  // ✅ 高效
   ```

2. **使用切片**

   ```rust
   fn first_word(s: &str) -> &str { ... }  // ✅ 灵活
   ```

3. **避免不必要的 clone**

   ```rust
   let s = String::from("hello");
   process(&s);  // ✅ 而非 process(s.clone())
   ```

### ⚠️ 低效模式

1. **过度使用 clone**

   ```rust
   let s2 = s1.clone();  // ⚠️ 堆分配开销
   ```

2. **过度使用 Rc/Arc**

   ```rust
   Rc<Rc<Vec<String>>>  // ⚠️ 双重引用计数
   ```

---

## 🔗 快速跳转

### 深入学习

- [完整所有权教程](../../crates/c01_ownership_borrow_scope/docs/tier_02_guides/01_所有权实践.md)
- [借用检查器详解](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/02_借用检查器详解.md)
- [智能指针 API](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/05_智能指针API参考.md)

### 代码示例

- [综合示例](../../crates/c01_ownership_borrow_scope/examples/comprehensive_ownership_examples.rs)
- [智能指针示例](../../crates/c01_ownership_borrow_scope/examples/comprehensive_smart_pointers.rs)

### 形式化理论

- [类型系统理论](../../crates/c01_ownership_borrow_scope/docs/tier_04_advanced/06_类型系统理论.md)
- [形式化验证](../../crates/c01_ownership_borrow_scope/docs/tier_04_advanced/07_形式化验证.md)

---

---

## 🆕 Rust 1.92.0 内存优化

### 内存分配优化

**改进**: 小对象分配性能提升 25-30%

```rust
// Rust 1.92.0 优化后的内存分配
// HashMap 操作更快
// 内存碎片减少 15-20%

use std::collections::HashMap;

let mut map = HashMap::new();
// ✅ 小对象分配性能提升 25-30%
for i in 0..1000 {
    map.insert(i, format!("value_{}", i));
}
```

**影响**:

- 异步场景下的内存分配性能提升
- HashMap 操作更快
- 内存碎片减少

---

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+ (Edition 2024)
**打印友好**: 可直接打印为桌面参考

🦀 **Rust 所有权，安全与性能的完美平衡！**
