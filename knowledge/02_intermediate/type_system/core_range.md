# `core::range` 模块与 `RangeInclusive`（Rust 1.95.0）

> **稳定版本**: Rust 1.95.0 (2026-04-16)
> **Edition**: 2024
> **RFC**: [RFC 3550](https://rust-lang.github.io/rfcs/3550-rangeful.html)

---

## 一、概念定义

Rust 1.95.0 引入了 `core::range` 模块，新增 `RangeInclusive` 和 `RangeInclusiveIter` 类型。这是对 `std::ops::RangeInclusive` 的模块级补充，旨在为未来统一所有 range 类型提供命名空间。

### 关键区分

| 类型 | 表示法 | 包含端点 | 模块 |
|------|--------|---------|------|
| `std::ops::Range` | `a..b` | 半开 `[a, b)` | `core::ops` |
| `std::ops::RangeInclusive` | `a..=b` | 闭区间 `[a, b]` | `core::ops` |
| **`core::range::RangeInclusive`** (1.95+) | `RangeInclusive::new(a, b)` | 闭区间 `[a, b]` | `core::range` |

> ⚠️ **注意**: `core::range::RangeInclusive` 目前**不是** `std::ops::RangeInclusive` 的替代，两者共存。

---

## 二、基本用法

### 2.1 创建区间

```rust
use core::range::RangeInclusive;

let r = RangeInclusive::new(1, 10);
// 等价于 std::ops 的 1..=10
```

### 2.2 遍历区间

```rust
use core::range::RangeInclusive;

let r = RangeInclusive::new(1, 5);
for i in r {
    println!("{}", i);  // 1, 2, 3, 4, 5
}
```

### 2.3 区间运算

```rust
use core::range::RangeInclusive;

fn overlap(a: &RangeInclusive<i32>, b: &RangeInclusive<i32>) -> bool {
    a.contains(b.start()) || b.contains(a.start())
}
```

---

## 三、应用场景

### 3.1 分页计算

```rust
use core::range::RangeInclusive;

fn page_range(total: u32, per_page: u32, page: u32) -> RangeInclusive<u32> {
    let start = page * per_page;
    let end = (start + per_page).min(total);
    RangeInclusive::new(start, end)
}
```

### 3.2 区间树

```rust
use core::range::RangeInclusive;

struct IntervalTree<T> {
    intervals: Vec<RangeInclusive<T>>,
}

impl<T: Ord + Clone> IntervalTree<T> {
    fn query(&self, point: &T) -> Vec<&RangeInclusive<T>> {
        self.intervals.iter()
            .filter(|r| r.contains(point))
            .collect()
    }
}
```

---

## 四、限制与反例

### ❌ 空区间行为

```rust
let r = RangeInclusive::new(5, 3);  // start > end
// 有效但迭代时为空
```

### ❌ 与旧 Range 的混淆

```rust
// RangeInclusive 包含两端点，共 6 个元素
let r = RangeInclusive::new(0, 5);
assert_eq!(r.into_iter().count(), 6);  // 不是 5！
```

---

## 五、迁移指南

```rust
// 旧方式
use std::ops::RangeInclusive;
let old: RangeInclusive<i32> = 1..=10;

// 新方式（1.95+）
use core::range::RangeInclusive;
let new = RangeInclusive::new(1, 10);

// 互转
let from_old = core::range::RangeInclusive { start: *old.start(), last: *old.end() };
```

---

## 六、参考

- [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)
- [RFC 3550](https://rust-lang.github.io/rfcs/3550-rangeful.html)
- [rust-lang/rust#136431](https://github.com/rust-lang/rust/pull/136431)
