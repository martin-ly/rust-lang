# C08 算法练习 - 排序算法

> 难度: 中级 | 预计时间: 60 分钟

---

## 🎯 练习目标

- 理解常见排序算法的原理
- 分析时间复杂度和空间复杂度
- 掌握 Rust 实现的技巧

---

## 练习 1: 实现冒泡排序

```rust
fn bubble_sort(arr: &mut [i32]) {
    // TODO: 实现冒泡排序
}

fn main() {
    let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
    bubble_sort(&mut arr);
    assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    println!("排序成功: {:?}", arr);
}
```

### 提示

1. 使用双重循环
2. 比较相邻元素
3. 如果顺序错误则交换

<details>
<summary>答案</summary>

```rust
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();
    for i in 0..n {
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}
```

**时间复杂度**: O(n²)
**空间复杂度**: O(1)

</details>

---

## 练习 2: 实现快速排序

```rust
fn quick_sort(arr: &mut [i32]) {
    // TODO: 实现快速排序
}

fn main() {
    let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
    quick_sort(&mut arr);
    assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    println!("排序成功: {:?}", arr);
}
```

### 提示

1. 选择基准元素 (pivot)
2. 分区: 小于 pivot 的在左，大于的在右
3. 递归排序左右两部分

<details>
<summary>答案</summary>

```rust
fn quick_sort(arr: &mut [i32]) {
    let len = arr.len();
    if len < 2 {
        return;
    }

    let pivot_index = partition(arr);
    quick_sort(&mut arr[0..pivot_index]);
    quick_sort(&mut arr[pivot_index + 1..]);
}

fn partition(arr: &mut [i32]) -> usize {
    let len = arr.len();
    let pivot = arr[len - 1];
    let mut i = 0;

    for j in 0..len - 1 {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }

    arr.swap(i, len - 1);
    i
}
```

**时间复杂度**: 平均 O(n log n), 最坏 O(n²)
**空间复杂度**: O(log n)

</details>

---

## 📊 算法对比

| 算法 | 平均时间 | 最坏时间 | 空间 | 稳定性 |
|------|----------|----------|------|--------|
| 冒泡排序 | O(n²) | O(n²) | O(1) | 稳定 |
| 快速排序 | O(n log n) | O(n²) | O(log n) | 不稳定 |
| 归并排序 | O(n log n) | O(n log n) | O(n) | 稳定 |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
