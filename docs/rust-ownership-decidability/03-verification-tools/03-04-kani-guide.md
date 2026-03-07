# Kani 模型检测指南

> **工具类型**: 模型检测
> **难度**: 🔴 高级
> **应用场景**: 验证状态空间、证明属性

---

## 概念

Kani 是 Rust 的**模型检测器**，使用 CBMC (C Bounded Model Checker) 来验证代码属性。它可以穷举所有可能的执行路径。

---

## 安装

```bash
# 安装 Kani
cargo install --locked kani-verifier

# 设置
cargo kani setup
```

---

## 基本用法

### 验证函数

```rust
// 使用 kani 属性
#[kani::proof]
fn test_addition() {
    let a: u32 = kani::any();  // 任意值
    let b: u32 = kani::any();

    // 假设前提条件
    kani::assume(a < 1000 && b < 1000);

    let result = a + b;

    // 验证后置条件
    assert!(result >= a);  // 溢出检查
}
```

运行:

```bash
cargo kani
```

### 假设与断言

```rust
#[kani::proof]
fn test_division() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();

    // 假设除数不为零
    kani::assume(y != 0);

    let result = x / y;

    // 验证: x = (x / y) * y + (x % y)
    assert_eq!(x, result * y + x % y);
}
```

---

## 验证 Unsafe 代码

```rust
#[kani::proof]
fn test_raw_pointer() {
    let mut x: i32 = kani::any();
    let ptr: *mut i32 = &mut x;

    unsafe {
        *ptr = 42;
        assert_eq!(*ptr, 42);
    }
}
```

---

## 功能属性验证

```rust
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}

#[kani::proof]
fn verify_binary_search() {
    // 固定大小数组 (Kani 需要有限状态空间)
    let arr: [i32; 5] = kani::any();
    let target: i32 = kani::any();

    // 假设数组已排序
    kani::assume(arr[0] <= arr[1]);
    kani::assume(arr[1] <= arr[2]);
    kani::assume(arr[2] <= arr[3]);
    kani::assume(arr[3] <= arr[4]);

    if let Some(idx) = binary_search(&arr, target) {
        // 验证: 如果返回 Some(idx)，则 arr[idx] == target
        assert_eq!(arr[idx], target);
    }
}
```

---

## 限制与注意事项

1. **状态空间爆炸**: 复杂函数可能无法完成验证
2. **循环**: 需要循环展开限制
3. **不支持所有 Rust 特性**: 某些标准库函数不支持

```bash
# 增加循环展开上限
cargo kani --unwind 10
```

---

*文档版本: 1.0.0*
