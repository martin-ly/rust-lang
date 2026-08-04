# 性能调优 - Performance Tuning

**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 完整版  

## 📋 目录

- [性能调优 - Performance Tuning](#性能调优---performance-tuning)
  - [📋 目录](#-目录)
  - [1. 避免克隆](#1-避免克隆)
  - [2. 使用迭代器](#2-使用迭代器)
  - [3. 内联优化](#3-内联优化)

## 1. 避免克隆

```rust
// 不好：不必要的克隆
fn bad_clone(data: Vec<i32>) -> i32 {
    let copy = data.clone();
    copy.iter().sum()
}

// 好：使用借用
fn good_borrow(data: &[i32]) -> i32 {
    data.iter().sum()
}
```

## 2. 使用迭代器

```rust
// 高效的迭代器链
fn process_data(data: &[i32]) -> Vec<i32> {
    data.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .collect()
}
```

## 3. 内联优化

```rust
#[inline]
fn small_function(x: i32) -> i32 {
    x * 2
}

#[inline(always)]
fn critical_function(x: i32) -> i32 {
    x + 1
}
```

---

**相关文档**：

- [性能优化](../04_safety/03_performance_optimization.md)

**最后更新**: 2025年1月27日
