# 07. 循环与迭代器的控制流 (Loops & Iterators - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐⭐  
> **预计阅读时间**：1.5小时  
> **前置知识**：循环基础、迭代器基础、trait 系统

## 📖 内容概述

本文档全面覆盖 loop/while/for 的高级用法、标签跳转、多层 break/continue，以及 Iterator 组合子（map/filter/flat_map/try_fold 等）的控制流应用与性能优化。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 使用循环标签处理复杂嵌套
- [ ] 掌握 loop 返回值的高级用法
- [ ] 使用迭代器组合子简化控制流
- [ ] 理解 try_fold 的错误传播机制
- [ ] 优化迭代器性能
- [ ] 选择合适的迭代方式

## 📚 目录

- [07. 循环与迭代器的控制流 (Loops \& Iterators - Rust 1.90)](#07-循环与迭代器的控制流-loops--iterators---rust-190)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [7.1. 基本循环与标签](#71-基本循环与标签)
  - [在 `loop` 中返回值](#在-loop-中返回值)
  - [迭代器控制与 `try_fold`](#迭代器控制与-try_fold)
  - [性能与可读性建议](#性能与可读性建议)

---

## 7.1. 基本循环与标签

```rust
fn search_2d(grid: &[Vec<i32>], target: i32) -> Option<(usize, usize)> {
    'rows: for (r, row) in grid.iter().enumerate() {
        for (c, &val) in row.iter().enumerate() {
            if val == target { break 'rows Some((r, c)); }
        }
    }
}
```

## 在 `loop` 中返回值

```rust
fn first_positive(nums: &[i32]) -> Option<i32> {
    let res = loop {
        for &n in nums { if n > 0 { break Some(n); } }
        break None;
    };
    res
}
```

## 迭代器控制与 `try_fold`

`try_fold` 可在出现错误时提前短路，常用于聚合 + 失败传播。

```rust
fn sum_even_u32<I: IntoIterator<Item = u32>>(iter: I) -> Result<u64, &'static str> {
    iter.into_iter().try_fold(0u64, |acc, x| {
        if x % 2 == 0 { Ok(acc + x as u64) } else { Err("odd") }
    })
}
```

## 性能与可读性建议

- `for` 优先用于迭代器场景；
- 链式组合子便于表达数据流，但注意过长链条影响可读性；
- 在热路径考虑避免分配，选择惰性适配器而非中间 `collect`。
