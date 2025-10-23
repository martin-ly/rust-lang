# C01 所有权与借用: 术语表 (Glossary)

> **文档定位**: 所有权、借用、作用域核心术语快速参考  
> **使用方式**: 通过术语索引快速查找定义，理解核心概念  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 参考资料

---

## 目录

- [C01 所有权与借用: 术语表 (Glossary)](#c01-所有权与借用-术语表-glossary)
  - [目录](#目录)
  - [📋 术语索引](#-术语索引)
  - [所有权 (Ownership)](#所有权-ownership)
  - [借用 (Borrowing)](#借用-borrowing)
  - [引用 (Reference)](#引用-reference)
  - [生命周期 (Lifetime)](#生命周期-lifetime)
  - [Move 语义](#move-语义)
  - [Copy Trait](#copy-trait)
  - [Clone Trait](#clone-trait)
  - [作用域 (Scope)](#作用域-scope)
  - [Drop](#drop)
  - [智能指针 (Smart Pointer)](#智能指针-smart-pointer)
  - [内部可变性 (Interior Mutability)](#内部可变性-interior-mutability)
  - [Deref Trait](#deref-trait)
  - [悬垂指针 (Dangling Pointer)](#悬垂指针-dangling-pointer)
  - [RAII](#raii)
  - [📚 延伸阅读](#-延伸阅读)

## 📋 术语索引

[B](#借用-borrowing) | [C](#copy-trait) | [D](#drop) | [L](#生命周期-lifetime) | [M](#move-语义) | [O](#所有权-ownership) | [R](#引用-reference) | [S](#作用域-scope)

---

## 所有权 (Ownership)

**定义**: Rust内存管理的核心机制，每个值都有唯一的所有者。

**三原则**:

1. 每个值都有一个所有者
2. 值在任意时刻只能有一个所有者
3. 当所有者离开作用域，值将被丢弃

**示例**:

```rust
let s1 = String::from("hello");
let s2 = s1; // 所有权转移
// s1 不再有效
```

**相关**: [01_theory/01_ownership_theory.md](./01_theory/01_ownership_theory.md)

---

## 借用 (Borrowing)

**定义**: 获取值的引用而不取得所有权。

**规则**:

- 任意数量的不可变引用 **或** 一个可变引用
- 引用必须总是有效

**示例**:

```rust
let s = String::from("hello");
let r1 = &s; // 不可变借用
let r2 = &s; // 可以有多个

let mut s = String::from("hello");
let r = &mut s; // 可变借用（唯一）
```

**相关**: [02_core/02_borrowing_system.md](./02_core/02_borrowing_system.md)

---

## 引用 (Reference)

**定义**: 指向值的指针，但不拥有该值。

**类型**:

- **不可变引用** `&T`: 只读访问
- **可变引用** `&mut T`: 读写访问

**示例**:

```rust
let x = 5;
let r = &x; // 不可变引用
println!("{}", *r); // 解引用

let mut y = 5;
let r = &mut y; // 可变引用
*r += 1;
```

**相关**: [02_core/02_borrowing_system.md](./02_core/02_borrowing_system.md)

---

## 生命周期 (Lifetime)

**定义**: 引用有效性的作用域，确保引用不会悬垂。

**标注语法**: `'a`, `'b`, `'static`

**示例**:

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

struct ImportantExcerpt<'a> {
    part: &'a str,
}
```

**生命周期省略规则**: 编译器在某些情况下自动推导

**相关**: [02_core/03_lifetime_annotations.md](./02_core/03_lifetime_annotations.md)

---

## Move 语义

**定义**: 值的所有权从一个位置转移到另一个位置。

**特点**:

- 默认语义（对于非Copy类型）
- 原变量失效
- 无运行时开销

**示例**:

```rust
let s1 = String::from("hello");
let s2 = s1; // Move
// s1 不再有效

let v1 = vec![1, 2, 3];
let v2 = v1; // Move
// v1 不再有效
```

**相关**: [02_core/01_ownership_fundamentals.md](./02_core/01_ownership_fundamentals.md)

---

## Copy Trait

**定义**: 标记类型可以通过简单的位复制来复制。

**实现条件**:

- 类型所有成员都实现了Copy
- 类型未实现Drop

**Copy类型**:

- 所有整数类型: `i32`, `u64`, etc.
- 浮点类型: `f32`, `f64`
- 布尔类型: `bool`
- 字符类型: `char`
- 元组（元素都是Copy）

**示例**:

```rust
let x = 5;
let y = x; // Copy
// x 仍然有效

#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}
```

**相关**: [02_core/01_ownership_fundamentals.md](./02_core/01_ownership_fundamentals.md)

---

## Clone Trait

**定义**: 显式地深拷贝值。

**与Copy的区别**:

- Clone可能很昂贵（堆分配）
- Copy是隐式的，Clone需要显式调用
- Copy是浅拷贝，Clone可以是深拷贝

**示例**:

```rust
let s1 = String::from("hello");
let s2 = s1.clone(); // 显式克隆
// s1 和 s2 都有效

let v1 = vec![1, 2, 3];
let v2 = v1.clone();
// v1 和 v2 都有效
```

**相关**: [02_core/01_ownership_fundamentals.md](./02_core/01_ownership_fundamentals.md)

---

## 作用域 (Scope)

**定义**: 变量有效的代码区域。

**规则**:

- 变量从声明点开始有效
- 离开作用域时自动清理

**示例**:

```rust
{
    let s = String::from("hello"); // s有效
    // 使用s
} // s离开作用域，自动调用drop

// s不再有效
```

**相关**: [02_core/04_scope_management.md](./02_core/04_scope_management.md)

---

## Drop

**定义**: 值离开作用域时自动调用的清理代码。

**Drop Trait**:

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

**示例**:

```rust
struct CustomSmartPointer {
    data: String,
}

impl Drop for CustomSmartPointer {
    fn drop(&mut self) {
        println!("Dropping with data: {}", self.data);
    }
}

{
    let c = CustomSmartPointer {
        data: String::from("data"),
    };
} // drop自动调用
```

**相关**: [02_core/04_scope_management.md](./02_core/04_scope_management.md)

---

## 智能指针 (Smart Pointer)

**定义**: 实现了`Deref`和`Drop` trait的结构，行为类似指针但有额外功能。

**常见类型**:

- **`Box<T>`**: 堆分配
- **`Rc<T>`**: 引用计数（单线程）
- **`Arc<T>`**: 原子引用计数（多线程）
- **`RefCell<T>`**: 运行时借用检查
- **`Mutex<T>`**: 互斥锁
- **`RwLock<T>`**: 读写锁

**示例**:

```rust
use std::rc::Rc;

let a = Rc::new(5);
let b = Rc::clone(&a); // 引用计数+1
println!("count: {}", Rc::strong_count(&a)); // 2
```

**相关**: [03_advanced/04_smart_pointers.md](./03_advanced/04_smart_pointers.md)

---

## 内部可变性 (Interior Mutability)

**定义**: 在拥有不可变引用的情况下修改数据。

**实现**:

- **`Cell<T>`**: 单线程，Copy类型
- **`RefCell<T>`**: 单线程，运行时借用检查
- **`Mutex<T>`**: 多线程
- **`RwLock<T>`**: 多线程，读写分离

**示例**:

```rust
use std::cell::RefCell;

let data = RefCell::new(5);
*data.borrow_mut() += 1; // 运行时借用检查
```

**相关**: [03_advanced/01_advanced_ownership.md](./03_advanced/01_advanced_ownership.md)

---

## Deref Trait

**定义**: 解引用运算符 `*` 的行为。

**自动解引用强制转换**: 编译器自动插入解引用

**示例**:

```rust
use std::ops::Deref;

impl<T> Deref for Box<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        &**self
    }
}

let x = Box::new(5);
assert_eq!(*x, 5);
```

**相关**: [03_advanced/04_smart_pointers.md](./03_advanced/04_smart_pointers.md)

---

## 悬垂指针 (Dangling Pointer)

**定义**: 指向已释放内存的指针。

**Rust防护**: 编译器保证不会产生悬垂引用

**示例**:

```rust
// ❌ 编译错误
fn dangle() -> &String {
    let s = String::from("hello");
    &s // 错误：返回局部变量的引用
}

// ✅ 正确
fn no_dangle() -> String {
    let s = String::from("hello");
    s // 转移所有权
}
```

**相关**: [04_safety/01_memory_safety.md](./04_safety/01_memory_safety.md)

---

## RAII

**定义**: Resource Acquisition Is Initialization，资源获取即初始化。

**Rust实现**: 通过Drop trait自动清理资源

**优点**:

- 自动资源管理
- 异常安全
- 零开销

**示例**:

```rust
{
    let file = File::open("file.txt")?;
    // 使用file
} // file自动关闭
```

**相关**: [04_safety/01_memory_safety.md](./04_safety/01_memory_safety.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](./README.md) - 项目概述
- [理论基础](./01_theory/) - 深入学习
- [核心概念](./02_core/) - 基础知识
- [高级主题](./03_advanced/) - 进阶内容

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [最佳实践](./05_practice/02_best_practices.md)
