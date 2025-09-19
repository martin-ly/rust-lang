# 标记块与带值 break（覆盖至 Rust 1.90）

本篇阐述标签（循环/块）与带值 `break` 的表达式威力：以更直观方式实现“求值并提前返回”。

## 循环与标签

```rust
fn find_first_even(nums: &[i32]) -> Option<i32> {
    'out: for &n in nums {
        if n % 2 == 0 { break 'out Some(n); }
    }
}
```

## 带值 break 作为表达式

```rust
fn index_of(hay: &[i32], needle: i32) -> Option<usize> {
    let res = 'search: loop {
        for (i, &x) in hay.iter().enumerate() {
            if x == needle { break 'search Some(i); }
        }
        break 'search None;
    };
    res
}
```

## 标记块（模拟“局部求值”）

```rust
fn compute() -> i32 {
    'blk: {
        if 1 + 1 == 2 { break 'blk 10; }
        0
    }
}
```

---

工程建议：

- 多层控制流用标签提升可读性；
- 带值 `break` 让“循环即表达式”的意图清晰；
- 标记块可替代临时变量/跳转实现局部求值。
