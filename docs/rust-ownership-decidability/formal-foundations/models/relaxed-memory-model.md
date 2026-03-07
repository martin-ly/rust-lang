# Rust Relaxed Memory 模型形式化

> **来源**: POPL 2020 "RustBelt Meets Relaxed Memory"
> **作者**: Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, Derek Dreyer
> **难度**: 🔴🔴 专家级
> **前置知识**: 内存模型, 释放-获取语义, Iris 分离逻辑

---

## 目录

- [Rust Relaxed Memory 模型形式化](#rust-relaxed-memory-模型形式化)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言](#1-引言)
    - [1.1 顺序一致性的局限](#11-顺序一致性的局限)
    - [1.2 Relaxed Memory 的挑战](#12-relaxed-memory-的挑战)
  - [2. 内存模型基础](#2-内存模型基础)
    - [2.1 内存排序](#21-内存排序)
    - [2.2 happens-before 关系](#22-happens-before-关系)
    - [2.3 同步操作](#23-同步操作)
  - [3. Rust 内存模型](#3-rust-内存模型)
    - [3.1 与 C++ 内存模型的关系](#31-与-c-内存模型的关系)
    - [3.2 Atomic 类型](#32-atomic-类型)
    - [3.3 Ordering 枚举](#33-ordering-枚举)
  - [4. ORC11: Operational Relaxed C11](#4-orc11-operational-relaxed-c11)
    - [4.1 事件结构](#41-事件结构)
    - [4.2 视图语义](#42-视图语义)
    - [4.3 操作语义](#43-操作语义)
  - [5. iRC11: Iris for RC11](#5-irc11-iris-for-rc11)
    - [5.1 资源代数扩展](#51-资源代数扩展)
    - [5.2 视图资源](#52-视图资源)
    - [5.3 同步幽灵状态](#53-同步幽灵状态)
  - [6. RustBelt for Relaxed Memory](#6-rustbelt-for-relaxed-memory)
    - [6.1 库验证](#61-库验证)
    - [6.2 Arc 库的数据竞争](#62-arc-库的数据竞争)
    - [6.3 资源回收](#63-资源回收)
  - [7. 形式化结果](#7-形式化结果)
    - [7.1 安全性定理](#71-安全性定理)
    - [7.2 优化正确性](#72-优化正确性)
  - [参考文献](#参考文献)

---

## 摘要

本文档介绍 RustBelt 向 Relaxed Memory 模型的扩展，核心贡献包括：

1. **ORC11**: C11/C++11 内存模型的操作语义
2. **iRC11**: 支持 Relaxed Memory 的 Iris 扩展
3. **同步幽灵状态**: 解决资源回收的新技术
4. **Arc 数据竞争**: 在 relaxed memory 下发现的实际 bug

---

## 1. 引言

### 1.1 顺序一致性的局限

原始 RustBelt 假设顺序一致性（Sequential Consistency, SC）：

```
SC 假设：所有线程看到的内存操作顺序一致
```

但真实硬件和 Rust 程序使用更弱的内存模型：

```rust
// Relaxed memory 示例
use std::sync::atomic::{AtomicUsize, Ordering};

static X: AtomicUsize = AtomicUsize::new(0);
static Y: AtomicUsize = AtomicUsize::new(0);

fn thread1() {
    X.store(1, Ordering::Relaxed);
    Y.store(1, Ordering::Release);  // Release 存储
}

fn thread2() {
    if Y.load(Ordering::Acquire) == 1 {  // Acquire 加载
        assert!(X.load(Ordering::Relaxed) == 1);  // 可能失败！
    }
}
```

### 1.2 Relaxed Memory 的挑战

**挑战 1: 状态空间爆炸**

- SC: 线性操作序列
- Relaxed: 部分顺序，多种执行可能

**挑战 2: 资源回收**

- 在 relaxed memory 下，确定何时可以安全释放内存极其困难
- 不同线程可能对同一位置有不同的"视图"

**挑战 3: 验证技术失效**

- SC 下的许多验证规则在 relaxed memory 下无效
- 需要新的程序逻辑

---

## 2. 内存模型基础

### 2.1 内存排序

Rust 提供的内存排序选项：

| Ordering | 同步保证 | 使用场景 |
|----------|----------|----------|
| `Relaxed` | 无 | 计数器，不需要同步 |
| `Acquire` | 加载同步 | 获取锁，消费数据 |
| `Release` | 存储同步 | 释放锁，发布数据 |
| `AcqRel` | 加载+存储同步 | 读-修改-写操作 |
| `SeqCst` | 全局顺序 | 需要全局一致性 |

### 2.2 happens-before 关系

**定义**：

```
 happens-before (HB) 是内存操作之间的偏序关系：

1. 程序顺序：同一线程内的操作顺序
2. 同步顺序：Acquire 加载 "看到" Release 存储

如果 A happens-before B，则 A 的效果对 B 可见。
```

**图示**：

```
Thread 1:              Thread 2:
  A (Release)            C (Acquire 看到 A)
    │                        │
    └────── happens-before ──┘
                           │
                           D

A happens-before D
```

### 2.3 同步操作

**Release-Acquire 同步**：

```rust
// Thread 1: 发布数据
DATA.store(42, Ordering::Relaxed);
READY.store(true, Ordering::Release);  // Release 屏障

// Thread 2: 获取数据
if READY.load(Ordering::Acquire) {     // Acquire 屏障
    // 保证看到 DATA = 42
    assert!(DATA.load(Ordering::Relaxed) == 42);
}
```

**内存屏障效果**：

```
Release: 阻止后续存储被重排序到屏障之前
Acquire: 阻止前序加载被重排序到屏障之后
```

---

## 3. Rust 内存模型

### 3.1 与 C++ 内存模型的关系

Rust 的内存模型基于 C++11/C11：

```
Rust Atomics ≈ C++ std::atomic
Rust Ordering ≈ C++ memory_order
```

**关键区别**：

- Rust 的 `UnsafeCell` 用于标记内部可变性
- Rust 的 `Sync` trait 标记线程安全共享

### 3.2 Atomic 类型

```rust
use std::sync::atomic::{AtomicBool, AtomicUsize, AtomicPtr};

// 标准原子类型
static FLAG: AtomicBool = AtomicBool::new(false);
static COUNTER: AtomicUsize = AtomicUsize::new(0);

// 操作
COUNTER.fetch_add(1, Ordering::Relaxed);
FLAG.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed);
```

### 3.3 Ordering 枚举

```rust
pub enum Ordering {
    Relaxed,     // 无顺序约束
    Release,     // 释放语义
    Acquire,     // 获取语义
    AcqRel,      // 释放+获取
    SeqCst,      // 顺序一致
}
```

---

## 4. ORC11: Operational Relaxed C11

### 4.1 事件结构

ORC11 使用事件结构表示程序执行：

```
事件 e ::= Read(loc, val, ord, tid)
        | Write(loc, val, ord, tid)
        | RMW(loc, old, new, ord, tid)  (* 读-修改-写 *)
        | Fence(ord, tid)

执行图 G := (E, sb, rf, mo, sc)
  E: 事件集合
  sb: sequenced-before (程序顺序)
  rf: reads-from (读看到哪个写)
  mo: modification-order (对同一位置的写顺序)
  sc: sequenced-consistency order (SeqCst 顺序)
```

### 4.2 视图语义

**每个线程维护一个视图**：

```
视图 V ::= Map<Location, Timestamp>

表示线程对各个位置最新写入的可见性
```

**读取操作**：

```
读取 loc:
1. 检查所有对 loc 的写入
2. 选择满足 rf 约束的写入
3. 更新线程视图
```

**写入操作**：

```
写入 loc:
1. 获取当前位置的最新时间戳
2. 创建新写入事件
3. 更新 mo 关系
4. 根据 Ordering 更新线程视图
```

### 4.3 操作语义

**小步语义**：

```
配置 C ::= (T, M, G)

T: 线程池 (ThreadId → ThreadState)
M: 内存状态
G: 执行图
```

**加载规则（Acquire）**：

```
T(tid).view(loc) = t    (* 线程视图 *)
G.find_write(loc, t) = (e, val)  (* 找到可读的写入 *)
e.ordering ≥ Acquire
─────────────────────────────────────────────
(T, M, G) --load(loc, Acquire)--> (T', M, G')

其中：
  T' = T[tid ↦ T(tid).update_view(loc, e.timestamp)]
  G' = G.add_read_event(tid, loc, val, Acquire, e)
```

**存储规则（Release）**：

```
fresh e                    (* 新事件 *)
e = Write(loc, val, Release, tid)
─────────────────────────────────────────────
(T, M, G) --store(loc, val, Release)--> (T', M', G')

其中：
  M' = M[loc ↦ val]
  G' = G.add_write_event(e)
       .update_mo(loc, e)
       .propagate_view(tid, loc, e)
```

---

## 5. iRC11: Iris for RC11

### 5.1 资源代数扩展

iRC11 扩展 Iris 的资源代数：

```
资源 RA ::= Own(ℓ, v, q)        (* 所有权 *)
         | View(tid, V)         (* 线程视图 *)
         | Hist(ℓ, H)           (* 写入历史 *)
         | Token(γ)             (* 幽灵令牌 *)

H ::= List<(Timestamp, Value, View)>
```

### 5.2 视图资源

**视图资源表示线程对内存的可见性**：

```
View(tid, {(ℓ₁, t₁), (ℓ₂, t₂), ...}) 表示：
- 线程 tid 看到 ℓ₁ 的时间戳至少为 t₁
- 线程 tid 看到 ℓ₂ 的时间戳至少为 t₂
```

**获取操作更新视图**：

```
{Own(ℓ, v) ∗ View(tid, V)}
acquire_load(ℓ)
{Own(ℓ, v) ∗ View(tid, V[ℓ ↦ max(V(ℓ), t)]) ∗ v = value}
```

### 5.3 同步幽灵状态

**核心创新：Synchronized Ghost State**

解决资源回收问题的技术：

```
问题：在 relaxed memory 下，如何知道所有线程都完成了对某资源的访问？

解决方案：
1. 使用幽灵状态跟踪线程同步点
2. 当所有线程都达到同步点时，安全释放资源
```

**幽灵令牌协议**：

```
Protocol(γ) ::=
  | Unused      (* 资源未使用 *)
  | Active(n)   (* n 个线程正在使用 *)
  | Reclaiming  (* 正在回收 *)
  | Reclaimed   (* 已回收 *)

转移规则：
  Unused --[acquire]--> Active(1)
  Active(n) --[acquire]--> Active(n+1)
  Active(n) --[release]--> Active(n-1)  (n > 1)
  Active(1) --[release]--> Unused
  Unused --[reclaim]--> Reclaiming
  Reclaiming --[confirm]--> Reclaimed
```

---

## 6. RustBelt for Relaxed Memory

### 6.1 库验证

在 relaxed memory 下重新验证 RustBelt 的库：

| 库 | SC 验证 | Relaxed 验证 | 挑战 |
|----|---------|--------------|------|
| `Arc` | ✅ | ✅ | 数据竞争 bug |
| `Rc` | ✅ | ✅ | 无并发，较简单 |
| `Mutex` | ✅ | ✅ | 锁语义 |
| `RwLock` | ✅ | ✅ | 读写分离 |
| `Cell` | ✅ | ✅ | 无并发 |
| `RefCell` | ✅ | ✅ | 借用检查 |

### 6.2 Arc 库的数据竞争

**发现的问题**：

在原始 Arc 实现中发现了一个数据竞争 bug：

```rust
// 简化的问题代码
impl<T> Arc<T> {
    fn clone(&self) -> Arc<T> {
        // 使用 Relaxed ordering 增加计数
        let old = self.strong.fetch_add(1, Ordering::Relaxed);

        // 问题：这里可能有数据竞争！
        // 如果另一个线程同时进行 drop...
    }

    fn drop(&mut self) {
        if self.strong.fetch_sub(1, Ordering::Release) == 1 {
            // 释放资源
        }
    }
}
```

**问题分析**：

```
使用 Relaxed ordering 导致：
1. 计数增加可能不被其他线程及时看到
2. 可能导致 use-after-free
3. 需要升级为 Acquire-Release
```

**修复**：

```rust
fn clone(&self) -> Arc<T> {
    // 使用 Acquire 确保看到之前的 Release
    let old = self.strong.fetch_add(1, Ordering::Acquire);
    // ...
}
```

### 6.3 资源回收

**挑战**：在 relaxed memory 下确定何时可以安全释放内存

**解决方案**：

```
1. 使用 Release 语义释放最后引用
2. 使用 Acquire 语义获取资源
3. 通过同步幽灵状态确保所有线程都放弃引用
```

**协议示例**：

```
资源释放协议：

Thread 1 (最后一个持有者):          Thread 2 (尝试获取):
  release_resource()                 if try_acquire():
    write(data, null, Release)         read(data, Acquire)
    set_flag(freed)                    // 保证看到 null
```

---

## 7. 形式化结果

### 7.1 安全性定理

**定理 (内存安全)**：

```
对于所有通过 Rust 类型检查的 Rust 程序 P，
在 ORC11 语义下执行时：
1. 不会发生 use-after-free
2. 不会发生数据竞争
3. 不会发生空指针解引用
```

**定理 (类型安全)**：

```
如果 Γ ⊢ e : τ，则 e 的执行不会 stuck，
除非：
- 正常终止
- 显式 panic
- 外部 I/O 阻塞
```

### 7.2 优化正确性

**编译器优化在 Relaxed Memory 下的正确性**：

```
定理：以下优化在 iRC11 下保持正确：

1. 寄存器分配
2. 公共子表达式消除
3. 死代码消除
4. 循环不变量外提

但某些优化需要额外条件：
- 指令重排序需要考虑内存屏障
```

---

## 参考文献

1. **Dang, H. H., Jourdan, J. H., Kaiser, J. O., & Dreyer, D.** (2020). RustBelt Meets Relaxed Memory. *POPL '20*.

2. **Lahav, O., Vafeiadis, V., Kang, J., Hur, C. K., & Dreyer, D.** (2017). Repairing sequential consistency in C/C++11. *PLDI '17*.

3. **Jung, R., et al.** (2018). Iris from the ground up: A modular foundation for higher-order concurrent separation logic. *JFP*.

4. **Batty, M., et al.** (2011). Mathematizing C++ concurrency. *POPL '11*.

5. **Boehm, H. J., & Adve, S. V.** (2008). Foundations of the C++ concurrency memory model. *PLDI '08*.

6. **Manson, J., Pugh, W., & Adve, S. V.** (2005). The Java memory model. *POPL '05*.

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*状态: 完成*
