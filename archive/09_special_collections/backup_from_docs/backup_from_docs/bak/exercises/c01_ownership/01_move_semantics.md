# 练习: 理解移动语义

---
**元数据**_

```yaml
id: c01_01
module: c01_ownership
title: "理解移动语义"
difficulty: beginner
estimated_time: 15
tags: [ownership, move-semantics, clone]
```

---

## 📝 问题描述

在Rust中，当一个值被赋值给另一个变量时，所有权会发生转移（移动）。你的任务是理解并正确处理移动语义。

## 🎯 学习目标

- 理解Rust的移动语义
- 掌握所有权转移规则
- 学会使用`clone()`方法
- 区分移动和复制

## 💻 起始代码

[🚀 在 Playground 中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&code=fn%20main()%20%7B%0A%20%20%20%20let%20s1%20%3D%20String%3A%3Afrom(%22hello%22)%3B%0A%20%20%20%20let%20s2%20%3D%20s1%3B%0A%20%20%20%20%0A%20%20%20%20%2F%2F%20TODO%3A%20%E4%BF%AE%E5%A4%8D%E7%BC%96%E8%AF%91%E9%94%99%E8%AF%AF%0A%20%20%20%20%2F%2F%20println!(%22%7B%7D%22%2C%20s1)%3B%0A%7D)

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;
    
    // TODO: 修复编译错误
    // println!("{}", s1);
}
```

## ❓ 问题

1. 为什么上面的代码无法编译？
2. 如何修复这个问题？
3. `clone()`和直接赋值有什么区别？

## 💡 提示

提示 1

当`s1`赋值给`s2`时，`String`的所有权从`s1`转移到了`s2`。之后`s1`不再有效。

提示 2

你可以使用`clone()`方法创建一个深拷贝，这样两个变量都拥有各自的数据。

提示 3

对于实现了`Copy` trait的类型（如整数），赋值会进行复制而不是移动。

## ✅ 测试用例

```rust
#[test]
fn test_move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1.clone();
    
    assert_eq!(s1, "hello");
    assert_eq!(s2, "hello");
}

#[test]
fn test_copy_types() {
    let x = 5;
    let y = x;  // Copy, not move
    
    assert_eq!(x, 5);
    assert_eq!(y, 5);
}
```

## 📚 参考答案

点击查看答案 - 方案1: 使用clone()

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 创建s1的深拷贝
    
    println!("s1 = {}", s1);  // 现在可以使用s1了
    println!("s2 = {}", s2);
}
```

**解释**:

- `clone()`方法创建了`s1`的完整副本
- 现在`s1`和`s2`各自拥有独立的数据
- 两个变量都可以使用

**性能考虑**: `clone()`会进行深拷贝，对于大型数据结构可能开销较大。

点击查看答案 - 方案2: 使用引用

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = &s1;  // 借用s1而不是移动
    
    println!("s1 = {}", s1);
    println!("s2 = {}", s2);
}
```

**解释**:

- 使用引用`&s1`而不是移动所有权
- `s2`只是借用`s1`的内容
- 两个变量都可以读取数据
- 这种方式更高效，因为不需要复制数据

**何时使用**: 当你只需要读取数据而不需要拥有它时，使用借用。

## 🎓 扩展学习

### Copy vs Clone

```rust
// Copy: 自动复制（栈上的简单类型）
let x = 5;
let y = x;  // x仍然有效

// Clone: 显式深拷贝（堆上的复杂类型）
let s1 = String::from("hello");
let s2 = s1.clone();  // s1仍然有效
```

### 移动语义的好处

1. **内存安全**: 防止双重释放
2. **性能优化**: 避免不必要的复制
3. **清晰的所有权**: 明确谁负责释放内存

## 🔗 相关资源

- [Rust Book - 所有权](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)
- [Rust By Example - 移动](https://doc.rust-lang.org/rust-by-example/scope/move.html)
- 下一个练习: [02_borrowing.md](./02_borrowing.md)

---

**难度**: 🟢 初级  
**预计时间**: 15 分钟  
**创建日期**: 2025-10-20
