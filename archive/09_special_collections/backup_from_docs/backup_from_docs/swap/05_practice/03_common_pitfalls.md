# 常见陷阱 - Common Pitfalls

**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 完整版  

## 📋 目录

- [常见陷阱 - Common Pitfalls](#常见陷阱---common-pitfalls)
  - [📋 目录](#-目录)
  - [1. 借用检查器错误](#1-借用检查器错误)
  - [2. 生命周期错误](#2-生命周期错误)
  - [3. 所有权错误](#3-所有权错误)

## 1. 借用检查器错误

```rust
// 错误：借用冲突
fn borrow_conflict_bad() {
    let mut data = vec![1, 2, 3];
    let first = &data[0];
    // data.push(4); // 错误：不能在不可变借用时可变借用
    println!("{}", first);
}

// 正确：限制借用范围
fn borrow_conflict_good() {
    let mut data = vec![1, 2, 3];
    {
        let first = &data[0];
        println!("{}", first);
    }
    data.push(4);
}
```

## 2. 生命周期错误

```rust
// 错误：返回悬垂引用
fn dangling_reference_bad() -> &'static str {
    let s = String::from("hello");
    // &s // 错误
    "hello" // 正确：使用静态字符串
}
```

## 3. 所有权错误

```rust
// 错误：移动后使用
fn use_after_move_bad() {
    let s = String::from("hello");
    let s2 = s;
    // println!("{}", s); // 错误：s 已被移动
    println!("{}", s2);
}
```

---

**相关文档**：

- [最佳实践](./02_best_practices.md)

**最后更新**: 2025年1月27日
