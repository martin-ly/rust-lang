# Tree Borrows 模型权威指南

> **定位**: Rust 内存模型前沿 — Tree Borrows
> **作者**: Neven Villani (RustBelt / Miri 团队)
> **状态**: 实验性 (Miri `-Zmiri-tree-borrows`)
> **适用**: 理解 `unsafe` Rust 的别名规则、Miri 诊断解释

---

## 📋 目录

- [Tree Borrows 模型权威指南](#tree-borrows-模型权威指南)
  - [📋 目录](#-目录)
  - [🎯 为什么需要 Tree Borrows](#-为什么需要-tree-borrows)
  - [🌳 核心概念](#-核心概念)
    - [1. 权限树 (Permission Tree)](#1-权限树-permission-tree)
    - [2. 指针状态机](#2-指针状态机)
    - [3. 转换规则](#3-转换规则)
  - [📊 Tree Borrows vs Stacked Borrows](#-tree-borrows-vs-stacked-borrows)
  - [🔧 Miri 中使用 Tree Borrows](#-miri-中使用-tree-borrows)
  - [⚠️ 常见模式与陷阱](#️-常见模式与陷阱)
    - [模式 1: 手动迭代器 (safe under TB)](#模式-1-手动迭代器-safe-under-tb)
    - [模式 2: 双指针技巧](#模式-2-双指针技巧)
    - [陷阱: 父指针在子指针活跃时被使用](#陷阱-父指针在子指针活跃时被使用)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 为什么需要 Tree Borrows

Stacked Borrows (SB) 是 Rust 的第一个正式内存模型，但它对以下场景过于严格：

```rust
// 在 Stacked Borrows 下这是 UB！
let mut data = [0u8; 16];
let ptr1: *mut u8 = data.as_mut_ptr();
let ptr2: *mut u8 = ptr1.wrapping_add(1);

unsafe {
    *ptr1 = 1;  // 使用 ptr1
    *ptr2 = 2;  // 使用 ptr2 — SB 认为这是 UB
}
```

**原因**: SB 将指针视为一个栈，任何使用都需要重新验证整个栈。当 `ptr1` 被使用后，`ptr2`（从 ptr1 派生）被视为无效。

**Tree Borrows 的解决思路**: 将指针关系建模为**树结构**，兄弟节点之间不互相影响。

---

## 🌳 核心概念

### 1. 权限树 (Permission Tree)

当创建一个指针时，它成为树的根节点。派生指针成为子节点：

```
&mut data (根 — 独占写权限)
    ├── ptr1 = as_mut_ptr() (子 — 原始指针，无别名约束)
    │       └── ptr2 = ptr1.wrapping_add(1) (孙 — 不重叠区域)
    └── ptr3 = data.as_mut_ptr().add(8) (子 — 后半部分)
```

**关键规则**: 兄弟节点（同一父节点的不同子节点）在访问不重叠内存时是独立的。

---

### 2. 指针状态机

每个指针有四种权限状态：

| 状态 | 读 | 写 | 说明 |
|------|----|----|------|
| **Reserved** | ✅ | ✅ (延迟) | 新派生的共享/原始指针 |
| **Active** | ✅ | ✅ | 当前正在使用的独占指针 |
| **Frozen** | ✅ | ❌ | 冻结的共享指针 (&T) |
| **Disabled** | ❌ | ❌ | 已失效的指针 |

```
Reserved ──写访问──→ Active
   │                    │
   ├──读访问──→ Frozen ←─┤
   │              │      │
   └──子指针写──→ Disabled
```

---

### 3. 转换规则

**规则 1: 子指针写操作不影响兄弟指针**

```rust
let mut data = [0u8; 16];
let ptr1 = data.as_mut_ptr();
let ptr2 = ptr1.wrapping_add(1);

unsafe {
    *ptr1 = 1;  // ptr1 变为 Active
    *ptr2 = 2;  // ptr2 也是 Active — 兄弟关系，互不干扰 ✅
}
```

**规则 2: 共享引用 (&T) 冻结子树**

```rust
let mut data = 42;
let raw = &mut data as *mut i32;

unsafe {
    let shared = &*raw;      // 创建共享引用，raw 的子树被 Frozen
    let _ = *shared;         // ✅ 可以读
    // *raw = 0;              // ❌ UB: raw 已被 Frozen，不能写
}
```

**规则 3: 重新借用保持父子关系**

```rust
let mut data = 0;
let r1 = &mut data;
let r2 = &mut *r1;  // r2 是 r1 的子节点

*r2 = 1;  // r2 Active，r1 暂时挂起
*r1 = 2;  // r1 重新 Active，r2 必须不再使用
```

---

## 📊 Tree Borrows vs Stacked Borrows

| 场景 | Stacked Borrows | Tree Borrows | 结果 |
|------|----------------|--------------|------|
| 相邻字段通过不同指针写入 | ❌ UB | ✅ 允许 | TB 更宽松 |
| `&mut T` 转 `*mut T` 再转 `&mut T` | ❌ UB | ✅ 允许 | TB 更实用 |
| 内联汇编后使用指针 | ❌ UB | ⚠️ 谨慎 | 两者都困难 |
| 严格别名分析精度 | ⭐⭐⭐ | ⭐⭐ | SB 更精确 |
| 与 LLVM `noalias` 兼容 | 好 | 更好 | TB 更贴近编译器 |

**选择建议**:

- 新项目使用 Tree Borrows (`-Zmiri-tree-borrows`)
- 需要与 SB 行为对比时使用双重验证
- 最终 Rust 官方内存模型可能融合两者优点

---

## 🔧 Miri 中使用 Tree Borrows

```bash
# 使用 Tree Borrows 运行 Miri
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 对比 Stacked Borrows
cargo miri test  # 默认 SB
```

**项目中的 Miri 测试**: `crates/*/src/miri_tests.rs`

---

## ⚠️ 常见模式与陷阱

### 模式 1: 手动迭代器 (safe under TB)

```rust
let mut arr = [1, 2, 3, 4];
let ptr = arr.as_mut_ptr();

unsafe {
    for i in 0..4 {
        *ptr.add(i) *= 2;  // TB: 同一指针的连续访问 ✅
    }
}
```

### 模式 2: 双指针技巧

```rust
fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let ptr = arr.as_mut_ptr();
    let len = arr.len();
    unsafe {
        let mut left = ptr;
        let mut right = ptr.add(len - 1);
        // left 和 right 是兄弟节点，访问不重叠区域 ✅ (TB)
        while left < right {
            while *left < pivot { left = left.add(1); }
            while *right > pivot { right = right.sub(1); }
            std::ptr::swap(left, right);
        }
    }
}
```

### 陷阱: 父指针在子指针活跃时被使用

```rust
let mut data = [0u8; 16];
let parent = data.as_mut_ptr();
let child = parent.wrapping_add(1);

unsafe {
    *child = 1;      // child Active
    *parent = 2;     // ❌ TB: parent 重新 Active，child 变为 Disabled！
    *child = 3;      // UB: child 已 Disabled
}
```

**修复**: 确保父子指针的使用不交叉，或全部使用原始指针（无 &mut 中间层）。

---

## 🔗 参考资源

- [Tree Borrows 论文 (Neven Villani, 2023)](https://hal.science/hal-04196935/document)
- [Miri Tree Borrows 文档](https://github.com/rust-lang/miri#tree-borrows)
- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/)
- [项目 Miri 测试集](../../crates/c01_ownership_borrow_scope/src/miri_tests.rs)
- [Stacked Borrows 论文](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
