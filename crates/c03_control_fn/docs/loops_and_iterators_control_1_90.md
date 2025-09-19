# 循环与迭代器的控制流（覆盖至 Rust 1.90）

本篇覆盖 `loop/while/for`、标签跳转、多层 break/continue、`Iterator` 组合子（`map/filter/flat_map/try_fold` 等）与性能要点。

## 基本循环与标签

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
