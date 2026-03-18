# Stacked Borrows vs Tree Borrows：Rust别名模型深度分析

## 目录

- [Stacked Borrows vs Tree Borrows：Rust别名模型深度分析](#stacked-borrows-vs-tree-borrowsrust别名模型深度分析)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 为什么需要别名模型？](#1-为什么需要别名模型)
    - [1.1 未定义行为（UB）的边界](#11-未定义行为ub的边界)
    - [1.2 核心问题](#12-核心问题)
  - [2. Stacked Borrows 模型](#2-stacked-borrows-模型)
    - [2.1 核心概念](#21-核心概念)
    - [2.2 状态转换](#22-状态转换)
    - [2.3 示例分析](#23-示例分析)
    - [2.4 原始指针规则](#24-原始指针规则)
    - [2.5 局限性](#25-局限性)
  - [3. Tree Borrows 模型](#3-tree-borrows-模型)
    - [3.1 核心概念](#31-核心概念)
    - [3.2 权限状态](#32-权限状态)
    - [3.3 与Stacked Borrows的关键区别](#33-与stacked-borrows的关键区别)
    - [3.4 重新激活机制](#34-重新激活机制)
    - [3.5 对Self-Reference更友好](#35-对self-reference更友好)
  - [4. 模型对比](#4-模型对比)
    - [4.1 代码示例对比](#41-代码示例对比)
  - [5. 实际影响](#5-实际影响)
    - [5.1 检测使用Miri](#51-检测使用miri)
    - [5.2 迁移建议](#52-迁移建议)
  - [6. 形式化语义](#6-形式化语义)
    - [6.1 Stacked Borrows的形式化](#61-stacked-borrows的形式化)
    - [6.2 Tree Borrows的形式化](#62-tree-borrows的形式化)
  - [7. 常见UB模式](#7-常见ub模式)
    - [7.1 两种模型都拒绝的代码](#71-两种模型都拒绝的代码)
    - [7.2 Tree Borrows允许但Stacked Borrows拒绝](#72-tree-borrows允许但stacked-borrows拒绝)
  - [8. 总结](#8-总结)
  - [参考](#参考)

## 概述

Rust的别名规则（Aliasing Rules）定义了哪些指针使用模式是合法的。
**Stacked Borrows**是早期模型，**Tree Borrows**是2023年引入的改进模型，现在是Miri的默认选项。

---

## 1. 为什么需要别名模型？

### 1.1 未定义行为（UB）的边界

Rust编译器基于别名信息进行优化。
如果程序违反了别名规则，优化可能产生错误结果。

```rust
fn alias_optimization(x: &mut i32, y: &mut i32) {
    *x = 1;
    *y = 2;
    // 编译器可能假设 *x == 1，因为 y 应该与 x 不重叠
    assert_eq!(*x, 1); // 如果x和y指向同一内存，这可能失败
}
```

### 1.2 核心问题

当存在多个指针指向同一内存时：

- 哪些读写是合法的？
- 编译器可以做什么假设？
- 何时一个指针"失效"？

---

## 2. Stacked Borrows 模型

### 2.1 核心概念

**栈模型**：将内存访问权限建模为栈结构

```text
栈底 [ 唯一写权限 ] [ 共享读权限 ] [ 新唯一写权限 ] 栈顶
```

### 2.2 状态转换

| 操作 | 栈变化 | 说明 |
|------|--------|------|
| `&mut x` | Push Unique | 新唯一引用压栈 |
| `&x` | Push SharedReadOnly | 共享读引用压栈 |
| `*mut_ptr` | Pop to raw | 使用原始指针弹出到该位置 |
| 使用旧引用 | ❌ UB | 违反栈顺序 |

### 2.3 示例分析

```rust
// 示例1：基本借用栈
fn stacked_borrow_basic() {
    let mut x = 5;
    let r1 = &mut x;      // 栈: [Unique(1)]
    let r2 = &mut *r1;    // 栈: [Unique(1), Unique(2)]
    *r2 = 10;             // 使用栈顶
    // r1 现在无效！（弹出Unique(2)后）
    // println!("{}", r1); // ❌ UB
}
```

```rust
// 示例2：共享借用
fn shared_borrow() {
    let mut x = 5;
    let r1 = &x;          // 栈: [SharedReadOnly(1)]
    let r2 = &x;          // 栈: [SharedReadOnly(1), SharedReadOnly(2)]
    println!("{} {}", r1, r2); // ✅ OK
}
```

### 2.4 原始指针规则

```rust
fn raw_pointer_rules() {
    let mut x = 5;
    let r = &mut x;       // 栈: [Unique(1)]
    let ptr = r as *mut i32; // 转换，但不改变栈

    // 使用原始指针 - 弹出到第一个兼容项
    unsafe { *ptr = 10; } // 栈变为: [SharedReadWrite(ptr)]

    // 现在不能使用r！
    // *r = 20; // ❌ UB
}
```

### 2.5 局限性

Stacked Borrows过于严格，拒绝了一些合理的unsafe模式：

```rust
// 自引用结构的合法用例被拒绝
fn self_referential_pattern() {
    let mut x = [0; 10];
    let ptr = x.as_mut_ptr();

    // 使用ptr访问x的元素
    unsafe {
        *ptr.add(5) = 1; // Stacked Borrows: ✅ OK
    }

    // 但不能同时保持对数组的借用
    // 某些复杂模式会被错误标记为UB
}
```

---

## 3. Tree Borrows 模型

### 3.1 核心概念

**树模型**：将引用关系建模为树结构

```text
        根 (Allocated)
       /    \
  左分支    右分支
  /    \      \
读引用 写引用  新写引用
```

### 3.2 权限状态

每个指针位置有**权限状态**：

| 状态 | 读 | 写 | 子节点 |
|------|----|----|--------|
| Active | ✅ | ✅ | 允许 |
| Frozen | ✅ | ❌ | 允许 |
| Disabled | ❌ | ❌ | 无 |

### 3.3 与Stacked Borrows的关键区别

```rust
// 示例：父指针保持有效
fn tree_borrow_advantage() {
    let mut x = 5;
    let r1 = &mut x;      // r1: Active
    let r2 = &mut *r1;    // r2: Active, r1: Frozen（非Disabled！）

    *r2 = 10;             // 使用r2

    // Tree Borrows: r1现在可以重新激活！
    println!("{}", r1);   // ✅ OK (r1从Frozen恢复为Active)
}
```

### 3.4 重新激活机制

Tree Borrows允许"冻结"的引用在子引用结束后重新激活：

```rust
fn reactivation_demo() {
    let mut data = [1, 2, 3, 4, 5];

    // 获取数组引用
    let arr_ref = &mut data;  // Active

    {
        // 获取元素引用
        let elem_ref = &mut arr_ref[2];  // elem_ref: Active, arr_ref: Frozen
        *elem_ref = 100;
    } // elem_ref 结束，arr_ref 自动恢复为 Active

    // Tree Borrows: arr_ref 自动恢复
    arr_ref[0] = 50;  // ✅ OK
}
```

### 3.5 对Self-Reference更友好

```rust
// 更友好的自引用模式
struct Buffer {
    data: [u8; 1024],
    write_ptr: *mut u8, // 指向data内部
}

impl Buffer {
    fn new() -> Self {
        let mut b = Buffer {
            data: [0; 1024],
            write_ptr: std::ptr::null_mut(),
        };
        b.write_ptr = b.data.as_mut_ptr();
        b
    }

    fn write(&mut self, offset: usize, val: u8) {
        unsafe {
            // Tree Borrows更准确地跟踪这种关系
            *self.write_ptr.add(offset) = val;
        }
    }
}
```

---

## 4. 模型对比

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| 数据结构 | 栈 | 树 |
| 父引用失效 | 永久 | 可重新激活 |
| 原始指针 | 弹出栈 | 创建子树 |
| 复杂unsafe | 经常拒绝 | 更宽容 |
| 性能开销 | 较低 | 稍高 |
| Miri默认 | 否（旧） | 是（新） |

### 4.1 代码示例对比

```rust
fn compare_models() {
    let mut x = 0;
    let r1 = &mut x;
    let r2 = &mut *r1;
    let _ = *r2;
    *r1 = 1; // 这里的行为不同！
}
```

- **Stacked Borrows**: ❌ UB（r1已弹出）
- **Tree Borrows**: ✅ OK（r1已重新激活）

---

## 5. 实际影响

### 5.1 检测使用Miri

```bash
# Stacked Borrows（旧模型）
MIRIFLAGS="-Zmiri-stacked-borrows" cargo miri test

# Tree Borrows（默认新模型）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 同时检测数据竞争
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-data-race-detector" cargo miri test
```

### 5.2 迁移建议

1. **新项目**：直接使用Tree Borrows
2. **现有unsafe代码**：测试两种模型
3. **发现UB**：分析是真实bug还是模型差异

---

## 6. 形式化语义

### 6.1 Stacked Borrows的形式化

```text
State = Stack<Permission>
Permission = Unique(Tag) | SharedReadOnly | SharedReadWrite(Tag)

Transition:
- retag(ptr, kind): push new permission
- use(ptr): pop until compatible permission
- access(ptr, read/write): check top permission allows
```

### 6.2 Tree Borrows的形式化

```text
State = Tree<Node>
Node = { tag: Tag, permission: Perm, children: List<Node> }
Perm = Active | Frozen | Disabled

Transition:
- create_child(parent, tag): add child node
- use(node, kind): update permissions on path
- reactivate(parent): when all Active children gone
```

---

## 7. 常见UB模式

### 7.1 两种模型都拒绝的代码

```rust
fn definitely_ub() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = r1 as *mut i32;
    let r3 = &mut x; // 新唯一引用

    unsafe {
        *r2 = 10; // ❌ UB: 使用过时指针
    }
}
```

### 7.2 Tree Borrows允许但Stacked Borrows拒绝

```rust
fn tree_friendly() {
    let mut x = [1, 2, 3];
    let slice = &mut x[..];
    let elem = &mut slice[1];
    *elem = 5;
    slice[0] = 4; // Stacked: ❌ Tree: ✅
}
```

---

## 8. 总结

Tree Borrows是Rust别名模型的重大改进：

1. **更准确**：反映真实的内存使用模式
2. **更宽容**：接受更多合法的unsafe代码
3. **向后兼容**：不引入新的UB
4. **工具支持**：Miri默认使用

对于编写unsafe Rust的开发者，理解这些模型有助于：

- 编写符合规则的代码
- 使用Miri验证正确性
- 理解编译器优化的边界

---

## 参考

1. [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbis/stacked-borrows/)
2. [Tree Borrows Blog Post](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)
3. [Miri Documentation](https://github.com/rust-lang/miri)
4. [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)
