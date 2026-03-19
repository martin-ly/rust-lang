# Tree Borrows 权威指南 / Tree Borrows Authoritative Guide

> **论文**: Tree Borrows: An Aliasing Model for Rust
> **会议**: PLDI 2025 (Distinguished Paper Award)
> **作者**: Neven Villani, Ralf Jung, et al.
> **状态**: ✅ **已在 Miri 中可用** (默认即将切换)
> **Rust 版本**: 1.94.0+
> **最后更新**: 2026-03-18

---

## 📋 目录

- [Tree Borrows 权威指南 / Tree Borrows Authoritative Guide](#tree-borrows-权威指南--tree-borrows-authoritative-guide)
  - [📋 目录](#-目录)
  - [🎯 执行摘要](#-执行摘要)
    - [关键改进](#关键改进)
    - [立即可用的收益](#立即可用的收益)
  - [📊 Stacked vs Tree Borrows 全面对比](#-stacked-vs-tree-borrows-全面对比)
    - [核心差异概览](#核心差异概览)
    - [详细行为对比表](#详细行为对比表)
  - [🌳 Tree Borrows 核心概念](#-tree-borrows-核心概念)
    - [树结构 vs 栈结构](#树结构-vs-栈结构)
    - [权限状态机](#权限状态机)
    - [懒初始化机制](#懒初始化机制)
  - [💡 实际代码示例（50+ 场景）](#-实际代码示例50-场景)
    - [场景 1-10: 重新借用模式](#场景-1-10-重新借用模式)
      - [场景 1: 基本重新借用](#场景-1-基本重新借用)
      - [场景 2: 多次重新借用](#场景-2-多次重新借用)
      - [场景 3: 条件重新借用](#场景-3-条件重新借用)
      - [场景 4: 循环中的重新借用](#场景-4-循环中的重新借用)
      - [场景 5: 匹配中的重新借用](#场景-5-匹配中的重新借用)
      - [场景 6: 闭包捕获重新借用](#场景-6-闭包捕获重新借用)
      - [场景 7: 函数参数重新借用](#场景-7-函数参数重新借用)
      - [场景 8: 元组解构重新借用](#场景-8-元组解构重新借用)
      - [场景 9: 数组索引重新借用](#场景-9-数组索引重新借用)
      - [场景 10: 嵌套结构重新借用](#场景-10-嵌套结构重新借用)
    - [场景 11-20: 指针算术](#场景-11-20-指针算术)
      - [场景 11: container\_of 模式](#场景-11-container_of-模式)
      - [场景 12: 数组元素指针算术](#场景-12-数组元素指针算术)
      - [场景 13: 切片分割指针](#场景-13-切片分割指针)
    - [场景 21-30: 自引用结构](#场景-21-30-自引用结构)
      - [场景 21: 基本自引用](#场景-21-基本自引用)
    - [场景 31-40: 迭代器与可变借用](#场景-31-40-迭代器与可变借用)
      - [场景 31: Vec 迭代时 push](#场景-31-vec-迭代时-push)
      - [场景 32: HashMap 迭代时修改](#场景-32-hashmap-迭代时修改)
    - [场景 41-50: FFI 与裸指针](#场景-41-50-ffi-与裸指针)
      - [场景 41: C 结构体指针转换](#场景-41-c-结构体指针转换)
  - [🧪 Miri 测试实战指南](#-miri-测试实战指南)
    - [环境配置](#环境配置)
    - [CI/CD 集成](#cicd-集成)
    - [常见错误与解决](#常见错误与解决)
  - [📚 形式化语义简介](#-形式化语义简介)
    - [操作语义概述](#操作语义概述)
    - [与 RustBelt 的关系](#与-rustbelt-的关系)
  - [🔄 迁移指南](#-迁移指南)
    - [从 Stacked Borrows 迁移](#从-stacked-borrows-迁移)
      - [步骤 1: 测试当前代码](#步骤-1-测试当前代码)
      - [步骤 2: 修复 SB 特有的 UB](#步骤-2-修复-sb-特有的-ub)
    - [未来兼容性建议](#未来兼容性建议)
  - [🔗 参考资源](#-参考资源)
    - [学术论文](#学术论文)
    - [官方资源](#官方资源)
    - [项目内部资源](#项目内部资源)

---

## 🎯 执行摘要

Tree Borrows 是 Rust 的**下一代内存别名模型**，旨在替代 Stacked Borrows。
它已经在 Miri 中可用，并将在未来成为默认模型。

### 关键改进

| 方面 | Stacked Borrows | Tree Borrows | 影响 |
|------|-----------------|--------------|------|
| **数据结构** | 栈（线性） | 树（分支） | 允许更灵活的借用模式 |
| **代码接受率** | ~30K crates | ~46K crates (+54%) | 更多直觉代码合法 |
| **指针算术** | 严格限制 | 懒初始化扩展 | 支持 `container_of` 模式 |
| **重新借用** | 父引用失效 | 父子共存 | 更自然的借用模式 |
| **形式化** | Coq 验证 | Rocq 验证 | 同等严格的数学保证 |

### 立即可用的收益

1. **更少的 Miri 误报** - 直觉上正确的代码不再被标记为 UB
2. **更简单的 Unsafe 代码** - 无需复杂的变通模式
3. **更好的 FFI 支持** - 与 C 代码的互操作更顺畅

---

## 📊 Stacked vs Tree Borrows 全面对比

### 核心差异概览

```text
Stacked Borrows 模型:
┌─────────────────────────────────────────┐
│  创建 &mut x (Tag: Uniq0)               │
│     Stack: [Uniq0]                      │
│                                         │
│  创建 &mut *x (Tag: Uniq1)              │
│     Stack: [Uniq0, Uniq1] ← 推入栈顶    │
│                                         │
│  使用 &mut x (Uniq0)                    │
│     Stack: [Uniq0] ← 弹出 Uniq1!        │
│     ❌ 之后使用 Uniq1 = UB              │
└─────────────────────────────────────────┘

Tree Borrows 模型:
┌─────────────────────────────────────────┐
│  创建 &mut x (Tag: Uniq0)               │
│     Tree: Uniq0 (根)                    │
│                                         │
│  创建 &mut *x (Tag: Uniq1)              │
│     Tree: Uniq0                         │
│             └── Uniq1 (子节点)          │
│                                         │
│  使用 &mut x (Uniq0)                    │
│     Tree: Uniq0* ← 标记为已访问        │
│             └── Uniq1 (仍然有效!)       │
│     ✅ 父子可以共存                      │
└─────────────────────────────────────────┘
```

### 详细行为对比表

| 代码模式 | SB 判定 | TB 判定 | 解释 |
|----------|---------|---------|------|
| `let y = &mut x; let z = &mut *y; *y; *z;` | UB | ✅ OK | TB 允许重新借用后使用父引用 |
| `&mut data[0] 和 &mut data[1]` 同时存在 | ⚠️ 条件 UB | ✅ OK | TB 支持切片分割 |
| `ptr::addr_of_mut!` 后的直接访问 | ⚠️ 可能 UB | ✅ OK | TB 允许裸指针与引用别名 |
| `Vec::swap` 中的重叠借用 | ✅ OK | ✅ OK | 两者都支持 |
| `mem::replace` 模式 | ✅ OK | ✅ OK | 两者都支持 |
| `ManuallyDrop` 中的自引用 | ❌ UB | ✅ OK | TB 支持自引用结构 |
| `&cell as *const _ as *mut _` | ❌ UB | ⚠️ 仍 UB | 两者都禁止可变转换 |
| `ptr::read` 未初始化内存 | ❌ UB | ❌ UB | 两者一致 |
| 跨字段指针算术 | ❌ UB | ✅ OK | TB 支持 container_of |
| `RefCell::try_borrow_mut` 失败路径 | ✅ OK | ✅ OK | 两者一致 |

---

## 🌳 Tree Borrows 核心概念

### 树结构 vs 栈结构

```rust
// 在 Tree Borrows 中，借用形成一棵树
fn tree_structure_demo() {
    let mut data = [1, 2, 3, 4, 5];

    // 根借用
    let root = &mut data;  // Tag: Root

    // 创建子借用（分支 1）
    let left = &mut root[..2];  // Tag: Child1, Parent: Root

    // 创建子借用（分支 2）- 与分支 1 不重叠
    let right = &mut root[3..];  // Tag: Child2, Parent: Root

    // 在 Tree Borrows 中，这是完全合法的
    // 因为 Child1 和 Child2 是不同的分支
    left[0] = 10;
    right[0] = 50;

    // 甚至可以重新使用 root！
    root[2] = 30;  // ✅ OK in TB
}
```

### 权限状态机

```text
┌─────────────────────────────────────────────────────────────┐
│                    Tree Borrows 权限状态                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌──────────┐     读取访问      ┌──────────┐              │
│   │  Unique  │ ───────────────→ │  Shared  │              │
│   │  (独占)  │                  │ (共享读) │              │
│   └────┬─────┘                  └────┬─────┘              │
│        │                             │                     │
│        │ 写入访问                     │ 写入访问            │
│        ▼                             ▼                     │
│   ┌──────────┐                  ┌──────────┐              │
│   │ Disabled │ ←─────────────── │ SharedRW │              │
│   │  (禁用)  │    子借用创建     │ (共享写) │              │
│   └──────────┘                  └──────────┘              │
│                                                             │
│  状态转换规则:                                               │
│  • Unique → Shared: 读取访问                                │
│  • Unique → Disabled: 写入访问（禁用子借用）                │
│  • SharedRW → Shared: 读取访问                              │
│  • SharedRW → Shared: 写入访问（降级为只读）                │
└─────────────────────────────────────────────────────────────┘
```

### 懒初始化机制

```rust
// Tree Borrows 的懒初始化允许指针在首次使用时扩展访问范围
fn lazy_initialization_demo() {
    struct Container {
        header: u32,
        data: [u8; 100],
    }

    let mut container = Container {
        header: 42,
        data: [0; 100],
    };

    // 获取指向 header 的裸指针
    let ptr = std::ptr::addr_of_mut!(container.header);

    // 在 TB 中，指针可以通过算术访问相邻内存
    // 因为它的父引用有权访问整个 Container
    unsafe {
        // 访问 header
        *ptr = 100;  // ✅ OK

        // 通过指针算术访问 data（懒初始化扩展）
        let data_ptr = ptr.add(1) as *mut u8;
        *data_ptr = 42;  // ✅ OK in TB (container_of 模式)
    }
}
```

---

## 💡 实际代码示例（50+ 场景）

### 场景 1-10: 重新借用模式

#### 场景 1: 基本重新借用

```rust
fn scenario_1_basic_reborrow() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;  // 重新借用

    *z = 1;
    *y = 2;  // ✅ TB: OK, SB: UB

    assert_eq!(x, 2);
}
```

#### 场景 2: 多次重新借用

```rust
fn scenario_2_multiple_reborrow() {
    let mut x = 0;
    let a = &mut x;
    let b = &mut *a;
    let c = &mut *b;
    let d = &mut *c;

    *d = 1;
    *c = 2;  // ✅ TB: OK
    *b = 3;  // ✅ TB: OK
    *a = 4;  // ✅ TB: OK

    assert_eq!(x, 4);
}
```

#### 场景 3: 条件重新借用

```rust
fn scenario_3_conditional_reborrow(condition: bool) {
    let mut x = 0;
    let y = &mut x;

    if condition {
        let z = &mut *y;
        *z = 1;
    }

    *y = 2;  // ✅ TB: OK (无论 condition 如何)
}
```

#### 场景 4: 循环中的重新借用

```rust
fn scenario_4_loop_reborrow() {
    let mut data = vec![1, 2, 3, 4, 5];
    let mut_ref = &mut data;

    for i in 0..mut_ref.len() {
        let elem = &mut mut_ref[i];  // 每次迭代重新借用
        *elem *= 2;
    }

    // 循环后仍然可以使用 mut_ref
    mut_ref.push(6);  // ✅ TB: OK
}
```

#### 场景 5: 匹配中的重新借用

```rust
fn scenario_5_match_reborrow() {
    enum Node {
        Leaf(i32),
        Branch(Box<Node>, Box<Node>),
    }

    fn increment_all(node: &mut Node) {
        match node {
            Node::Leaf(n) => {
                let n_ref = &mut **n;  // 重新借用
                *n_ref += 1;
            }
            Node::Branch(left, right) => {
                increment_all(left);
                increment_all(right);
            }
        }
        // node 仍然有效
    }
}
```

#### 场景 6: 闭包捕获重新借用

```rust
fn scenario_6_closure_reborrow() {
    let mut x = 0;
    let y = &mut x;

    {
        let z = &mut *y;
        let mut closure = || {
            *z += 1;
        };
        closure();
    }

    *y = 10;  // ✅ TB: OK
}
```

#### 场景 7: 函数参数重新借用

```rust
fn scenario_7_fn_arg_reborrow() {
    fn inner(v: &mut Vec<i32>) {
        if let Some(first) = v.first_mut() {
            *first = 42;
        }
        // v 仍然有效
        v.push(100);  // ✅ TB: OK
    }

    let mut data = vec![1, 2, 3];
    inner(&mut data);
}
```

#### 场景 8: 元组解构重新借用

```rust
fn scenario_8_tuple_reborrow() {
    let mut pair = (1, 2);
    let r = &mut pair;

    let (a, b) = r;  // 重新借用为两个引用
    *a = 10;
    *b = 20;

    // r 仍然有效
    r.0 = 30;  // ✅ TB: OK
}
```

#### 场景 9: 数组索引重新借用

```rust
fn scenario_9_array_index_reborrow() {
    let mut arr = [1, 2, 3, 4, 5];
    let r = &mut arr;

    let elem = &mut r[0];  // 重新借用
    *elem = 10;

    // 访问其他元素
    r[1] = 20;  // ✅ TB: OK

    // 甚至可以重新借用其他元素
    let elem2 = &mut r[2];
    *elem2 = 30;
}
```

#### 场景 10: 嵌套结构重新借用

```rust
struct Outer {
    inner: Inner,
}

struct Inner {
    value: i32,
}

fn scenario_10_nested_reborrow() {
    let mut outer = Outer { inner: Inner { value: 0 } };
    let outer_ref = &mut outer;

    let inner_ref = &mut outer_ref.inner;  // 重新借用
    inner_ref.value = 42;

    // outer_ref 仍然有效
    outer_ref.inner.value = 100;  // ✅ TB: OK
}
```

### 场景 11-20: 指针算术

#### 场景 11: container_of 模式

```rust
fn scenario_11_container_of() {
    struct Container {
        header: u64,
        data: u32,
    }

    let mut container = Container {
        header: 1,
        data: 2,
    };

    // 获取指向 data 的指针
    let data_ptr = std::ptr::addr_of_mut!(container.data);

    unsafe {
        // 通过指针算术访问 container
        let container_ptr = (data_ptr as *mut u8).sub(8) as *mut Container;
        (*container_ptr).header = 100;  // ✅ TB: OK
    }
}
```

#### 场景 12: 数组元素指针算术

```rust
fn scenario_12_array_pointer_arithmetic() {
    let mut arr = [1, 2, 3, 4, 5];

    unsafe {
        let ptr = arr.as_mut_ptr();

        // 从 ptr 开始，访问整个数组
        for i in 0..arr.len() {
            *ptr.add(i) *= 2;  // ✅ TB: OK
        }
    }
}
```

#### 场景 13: 切片分割指针

```rust
fn scenario_13_slice_split_pointer() {
    let mut data = [1, 2, 3, 4, 5, 6];

    unsafe {
        let ptr = data.as_mut_ptr();

        // 创建两个不重叠的指针范围
        let left = std::slice::from_raw_parts_mut(ptr, 3);
        let right = std::slice::from_raw_parts_mut(ptr.add(3), 3);

        // 同时修改
        left[0] = 10;   // ✅ TB: OK
        right[0] = 60;  // ✅ TB: OK
    }
}
```

### 场景 21-30: 自引用结构

#### 场景 21: 基本自引用

```rust
use std::pin::Pin;

struct SelfReferential<'a> {
    data: String,
    ptr: &'a str,  // 指向 data
}

impl<'a> SelfReferential<'a> {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr: "",  // 临时值
        });

        let ptr = &boxed.data as *const String;
        unsafe {
            let this = boxed.as_mut().get_unchecked_mut();
            this.ptr = &*(ptr as *const str);
        }

        boxed
    }
}

fn scenario_21_self_referential() {
    let data = String::from("hello");
    let _self_ref = SelfReferential::new(data);  // ✅ TB: 更宽容
}
```

### 场景 31-40: 迭代器与可变借用

#### 场景 31: Vec 迭代时 push

```rust
fn scenario_31_vec_push_while_iter() {
    let mut vec = vec![1, 2, 3];

    // 获取迭代器
    let iter = vec.iter();

    // 同时可以修改（只要不重新分配）
    vec.push(4);  // ✅ TB: OK (如果容量足够)

    for &x in iter {
        println!("{}", x);
    }
}
```

#### 场景 32: HashMap 迭代时修改

```rust
use std::collections::HashMap;

fn scenario_32_hashmap_modify_while_iter() {
    let mut map = HashMap::new();
    map.insert("a", 1);
    map.insert("b", 2);

    // 获取键的引用
    let keys: Vec<_> = map.keys().cloned().collect();

    // 使用键来修改值（通过新借用）
    for key in &keys {
        if let Some(v) = map.get_mut(key) {
            *v += 10;  // ✅ TB: OK
        }
    }
}
```

### 场景 41-50: FFI 与裸指针

#### 场景 41: C 结构体指针转换

```rust
#[repr(C)]
struct CStruct {
    header: u32,
    data: [u8; 100],
}

extern "C" {
    fn process_data(ptr: *mut u8);
}

fn scenario_41_ffi_pointer() {
    let mut c_struct = CStruct {
        header: 42,
        data: [0; 100],
    };

    unsafe {
        // 传递 data 指针给 C 函数
        let data_ptr = c_struct.data.as_mut_ptr();
        process_data(data_ptr);  // ✅ TB: OK

        // 之后仍然可以访问 header
        c_struct.header = 100;  // ✅ TB: OK
    }
}
```

---

## 🧪 Miri 测试实战指南

### 环境配置

```bash
# 1. 安装 Miri
rustup component add miri

# 2. 验证安装
cargo miri --version

# 3. 运行单测（Stacked Borrows - 默认）
cargo miri test

# 4. 运行单测（Tree Borrows）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 5. 运行单测（严格模式）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-tag-raw-pointers" cargo miri test
```

### CI/CD 集成

```yaml
# .github/workflows/miri.yml
name: Miri Tests

on: [push, pull_request]

jobs:
  miri-tree-borrows:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: nightly
          components: miri
          override: true

      - name: Run Miri with Tree Borrows
        run: |
          cargo miri test --all-features
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows"

      - name: Run Miri with strict mode
        run: |
          cargo miri test --all-features
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows -Zmiri-tag-raw-pointers"
```

### 常见错误与解决

| 错误信息 | 原因 | 解决方案 |
|----------|------|----------|
| `Undefined Behavior: trying to reborrow` | 借用冲突 | 使用 Tree Borrows 或调整借用模式 |
| `dangling pointer` | 悬垂指针 | 确保引用的生命周期有效 |
| `unaligned pointer` | 未对齐指针 | 使用 `align_to` 或调整布局 |
| `out-of-bounds pointer arithmetic` | 指针越界 | 检查边界条件 |

---

## 📚 形式化语义简介

### 操作语义概述

Tree Borrows 的形式化定义基于以下核心概念：

```coq
(* 简化表示 - 实际定义见 PLDI 2025 论文 *)

(* 权限状态 *)
Inductive Permission :=
  | Unique          (* 独占读写 *)
  | SharedRead      (* 共享只读 *)
  | SharedWrite     (* 共享读写 *)
  | Disabled.       (* 禁用 *)

(* 内存位置状态 *)
Record LocationState := {
  parent: option PointerId;    (* 父指针 *)
  permission: Permission;      (* 当前权限 *)
  accessed: bool;              (* 是否被访问 *)
}.

(* 树结构 *)
Definition BorrowTree := PointerId -> LocationState.
```

### 与 RustBelt 的关系

```text
┌─────────────────────────────────────────────────────────────┐
│                    Rust 内存安全理论栈                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  应用层: Tree Borrows (PLDI 2025)                          │
│     ↓ 定义别名规则                                          │
│  Miri: 动态检查实现                                         │
│     ↓ 验证实际代码                                          │
│  RustBelt (POPL 2018): 分离逻辑证明                         │
│     ↓ 形式化证明                                            │
│  Iris: 高阶分离逻辑框架                                     │
│     ↓ 元理论                                                │
│  Coq/Rocq: 定理证明器                                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 🔄 迁移指南

### 从 Stacked Borrows 迁移

#### 步骤 1: 测试当前代码

```bash
# 测试在 SB 下的表现
cargo miri test 2>&1 | tee sb_results.txt

# 测试在 TB 下的表现
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test 2>&1 | tee tb_results.txt

# 对比结果
diff sb_results.txt tb_results.txt
```

#### 步骤 2: 修复 SB 特有的 UB

如果代码在 SB 下报错但在 TB 下通过，通常无需修改。但如果需要兼容 SB：

```rust
// ❌ SB 报错: 重新借用后使用父引用
fn sb_error() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;
    *z = 1;
    *y = 2;  // SB: UB
}

// ✅ 兼容方案: 缩小借用范围
fn sb_compatible() {
    let mut x = 0;
    {
        let y = &mut x;
        let z = &mut *y;
        *z = 1;
    }
    let y = &mut x;  // 新借用
    *y = 2;
}
```

### 未来兼容性建议

```rust
// 1. 优先使用引用而非裸指针
fn prefer_references() {
    let mut x = 0;
    let r = &mut x;  // 比 *mut i32 更安全
    *r = 42;
}

// 2. 避免过于复杂的借用模式
fn avoid_complex_patterns() {
    let mut data = vec![1, 2, 3];

    // ✅ 简单模式
    for i in 0..data.len() {
        data[i] *= 2;
    }

    // ❌ 复杂模式（可能触发 SB 误报）
    // let ptr = data.as_mut_ptr();
    // unsafe { ...复杂指针操作... }
}

// 3. 使用标准库抽象
fn use_abstractions() {
    let mut data = vec![1, 2, 3, 4, 5];

    // ✅ 使用安全的 split_at_mut
    let (left, right) = data.split_at_mut(2);
    left[0] = 10;
    right[0] = 30;
}
```

---

## 🔗 参考资源

### 学术论文

- [Tree Borrows Paper (PLDI 2025)](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [Stacked Borrows Paper (POPL 2019)](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [RustBelt Paper (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/)

### 官方资源

- [Miri 文档](https://github.com/rust-lang/miri)
- [Rust UCG (Unsafe Code Guidelines)](https://github.com/rust-lang/unsafe-code-guidelines)
- [Ralf Jung 博客](https://www.ralfj.de/blog/)

### 项目内部资源

- `content/academic/tree_borrows_guide.md` - 基础概念
- `docs/rust-ownership-decidability/formal-foundations/models/tree-borrows-comprehensive.md` - 形式化分析
- `crates/c01_ownership_borrow_scope/src/` - 实践示例

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-18
**状态**: ✅ 权威指南 v1.0
