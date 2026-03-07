# Miri 深度解析

> **工具类型**: 运行时 UB 检测 (Undefined Behavior Detection)
> **难度**: 🟡 中等 → 🔴 高级
> **应用场景**: 检测未定义行为、调试 Unsafe 代码、验证内存安全

---

## 目录

- [Miri 深度解析](#miri-深度解析)
  - [目录](#目录)
  - [1. 引言与概述](#1-引言与概述)
  - [2. Miri 的工作原理](#2-miri-的工作原理)
    - [2.1 解释执行模型](#21-解释执行模型)
    - [2.2 Stacked Borrows 内存模型](#22-stacked-borrows-内存模型)
    - [2.3 Tree Borrows 模型](#23-tree-borrows-模型)
  - [3. 形式化定义](#3-形式化定义)
    - [3.1 未定义行为 (UB) 的数学定义](#31-未定义行为-ub-的数学定义)
    - [3.2 别名规则的形式化](#32-别名规则的形式化)
    - [3.3 内存模型定理](#33-内存模型定理)
  - [4. 安装与配置](#4-安装与配置)
    - [4.1 安装 Miri](#41-安装-miri)
    - [4.2 环境配置](#42-环境配置)
  - [5. 核心检测能力](#5-核心检测能力)
    - [5.1 使用未初始化内存](#51-使用未初始化内存)
    - [5.2 悬垂指针解引用](#52-悬垂指针解引用)
    - [5.3 数据竞争](#53-数据竞争)
    - [5.4 违反别名规则](#54-违反别名规则)
    - [5.5 对齐违规](#55-对齐违规)
    - [5.6 整数溢出](#56-整数溢出)
  - [6. 高级使用技巧](#6-高级使用技巧)
    - [6.1 与 FFI 代码交互](#61-与-ffi-代码交互)
    - [6.2 环境变量详解](#62-环境变量详解)
    - [6.3 测试框架集成](#63-测试框架集成)
  - [7. 实战案例](#7-实战案例)
    - [7.1 自定义智能指针验证](#71-自定义智能指针验证)
    - [7.2 并发数据结构检测](#72-并发数据结构检测)
    - [7.3 Unsafe 抽象边界验证](#73-unsafe-抽象边界验证)
  - [8. Miri 与其他工具对比](#8-miri-与其他工具对比)
  - [9. 最佳实践与常见陷阱](#9-最佳实践与常见陷阱)
    - [9.1 最佳实践](#91-最佳实践)
  - [10. 限制与未来方向](#10-限制与未来方向)
    - [当前限制](#当前限制)
    - [未来方向](#未来方向)
  - [参考](#参考)

---

## 1. 引言与概述

Miri (Mid-level IR Interpreter) 是 Rust 的官方解释器，专门用于检测程序中的**未定义行为 (Undefined Behavior, UB)**。与编译器不同，Miri 在 Mid-level IR (MIR) 层面解释执行代码，能够精确跟踪内存状态和所有权变化。

```
┌─────────────────────────────────────────────────────────────┐
│                      Miri 架构概览                           │
├─────────────────────────────────────────────────────────────┤
│  Rust 源代码 → MIR → Miri 解释器 → 内存模型检查 → UB 报告   │
│                     ↓                                       │
│              Stacked Borrows / Tree Borrows                 │
│                     ↓                                       │
│              未定义行为检测与报告                              │
└─────────────────────────────────────────────────────────────┘
```

**核心能力:**

- ✅ **内存未初始化检测**: 发现使用未初始化内存的错误
- ✅ **悬垂指针检测**: 捕获使用已释放内存的行为
- ✅ **数据竞争检测**: 识别多线程中的竞争条件
- ✅ **别名规则验证**: 检查 Stacked Borrows/Tree Borrows 违规
- ✅ **对齐检查**: 验证内存对齐要求

---

## 2. Miri 的工作原理

### 2.1 解释执行模型

Miri 采用**字节码解释执行**的方式运行 Rust 程序：

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│  Rust 源码   │ ──→ │     MIR      │ ──→ │  Miri 解释器  │
└──────────────┘     └──────────────┘     └──────────────┘
                                                   ↓
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│   UB 报告    │ ←── │  内存模型    │ ←── │   执行状态   │
└──────────────┘     └──────────────┘     └──────────────┘
```

与直接编译执行相比，Miri 的优势在于：

| 特性 | 编译执行 | Miri 解释执行 |
|:---|:---|:---|
| 速度 | 快（原生代码） | 慢（10-100x） |
| UB 检测 | 无 | 全面 |
| 内存跟踪 | 无 | 精确到字节 |
| 别名规则检查 | 无 | Stacked Borrows |
| 平台依赖 | 目标平台 | 与主机无关 |

### 2.2 Stacked Borrows 内存模型

Stacked Borrows 是 Rust 的实验性内存模型，用于精确追踪指针的借用关系。

**核心概念：**

```
借用栈 (Borrow Stack):
┌─────────────────────────────────────┐
│ Unique ( &mut T )                  │ ← 栈顶：当前活跃的独占借用
├─────────────────────────────────────┤
│ SharedReadWrite ( *mut T )         │
├─────────────────────────────────────┤
│ SharedReadOnly ( &T )              │
├─────────────────────────────────────┤
│ Raw ( *const T, *mut T )           │ ← 栈底：原始指针
└─────────────────────────────────────┘
```

**形式化规则：**

```rust
// 规则 1: 创建 &mut T 时，必须在栈顶添加 Unique 标签
let mut x = 5;
let r1 = &mut x;  // 栈: [..., Raw, Unique(r1)]

// 规则 2: 使用指针时，必须找到对应的标签
*r1 = 10;  // OK: Unique(r1) 在栈顶

// 规则 3: 创建新借用时，可能需要弹出旧标签
let r2 = &mut x;  // 弹出 Unique(r1), 压入 Unique(r2)
                  // 栈: [..., Raw, Unique(r2)]

// 规则 4: 使用已弹出的标签 = UB!
*r1 = 20;  // ERROR: Unique(r1) 不在栈中!
```

### 2.3 Tree Borrows 模型

Tree Borrows 是 Stacked Borrows 的替代方案，使用**树结构**而非栈结构来追踪借用关系。

```
借用树 (Borrow Tree):
                    ┌─────────┐
                    │  Root   │ (原始指针)
                    └────┬────┘
           ┌───────────┼───────────┐
           ↓           ↓           ↓
      ┌────────┐  ┌────────┐  ┌────────┐
      │ &mut T │  │  &T    │  │ &mut T │
      └───┬────┘  └────────┘  └───┬────┘
          ↓                       ↓
     ┌─────────┐             ┌─────────┐
     │ Child   │             │ Child   │
     └─────────┘             └─────────┘
```

**启用 Tree Borrows:**

```bash
MIRI_TREE_BORROWS=1 cargo miri run
```

---

## 3. 形式化定义

### 3.1 未定义行为 (UB) 的数学定义

**定义 3.1 (未定义行为)**

设程序状态为 $S = (M, P, T)$，其中：

- $M$: 内存状态（地址到值的映射）
- $P$: 指针权限集合
- $T$: 活跃线程集合

未定义行为 UB 是程序执行中满足以下条件的状态转移：

$$\exists s \in S: \text{Exec}(s) \notin \text{DefinedBehavior}$$

其中 DefinedBehavior 包含所有 Rust 语言规范定义的有效行为。

**定理 3.1 (UB 的不可恢复性)**

若程序 $P$ 在某执行路径 $π$ 上触发了 UB，则该路径的所有后续状态都是未定义的：

$$\text{UB}(s_i) \Rightarrow \forall j > i: \neg\text{Defined}(s_j)$$

### 3.2 别名规则的形式化

**定义 3.2 (别名关系)**

给定两个指针 $p_1$ 和 $p_2$，别名关系 $A$ 定义为：

$$A(p_1, p_2) \iff \text{addr}(p_1) \cap \text{addr}(p_2) \neq \emptyset$$

**定义 3.3 (Stacked Borrows 有效性)**

设借用栈为 $B = [b_1, b_2, ..., b_n]$，指针 $p$ 的访问是有效的当且仅当：

$$\text{valid}(p, B) \iff \exists i: \text{tag}(p) = b_i \land \neg\text{disabled}(b_i)$$

**定理 3.2 (别名唯一性)**

在任意程序点，若存在独占借用 $&mut\ T$，则不存在其他活跃指针与该借用别名：

$$\text{active}(&mut\ T) \Rightarrow \neg\exists p: A(p, &mut\ T) \land \text{active}(p) \land p \neq &mut\ T$$

### 3.3 内存模型定理

**定理 3.3 (内存安全保证)**

若程序 $P$ 在 Miri 中执行不产生 UB 报告，则 $P$ 满足：

1. **无悬垂指针**: $\forall p \in P: \text{valid}(p) \Rightarrow \text{alloc}(p)\ \text{is live}$
2. **无数据竞争**: $\forall t_1, t_2 \in T: \neg\text{race}(t_1, t_2)$
3. **无未初始化读**: $\forall r \in \text{Reads}: \text{initialized}(r)$

---

## 4. 安装与配置

### 4.1 安装 Miri

```bash
# 安装 Miri 组件
rustup component add miri

# 验证安装
cargo miri --version
```

### 4.2 环境配置

```toml
# .cargo/config.toml
[build]
target = "x86_64-unknown-linux-gnu"

[miri]
# Miri 特定配置
flags = ["-Zmiri-disable-isolation"]
```

---

## 5. 核心检测能力

### 5.1 使用未初始化内存

**错误示例：**

```rust
fn main() {
    let x: i32;
    println!("{}", x);  // 使用未初始化变量 - UB!
}
```

**Miri 输出：**

```bash
$ cargo miri run
error: Undefined Behavior: memory access uses uninitialized data
   --> src/main.rs:3:20
    |
3   |     println!("{}", x);
    |                    ^ memory access uses uninitialized data
    |
```

**修复方案：**

```rust
fn main() {
    let x: i32 = 0;  // 显式初始化
    println!("{}", x);
}
```

**复杂场景 - 部分初始化：**

```rust
// 错误：部分初始化结构体
#[repr(C)]
struct Data {
    a: i32,
    b: i32,
}

fn partial_init() {
    let mut data: Data = unsafe { std::mem::zeroed() };
    data.a = 42;
    // data.b 仍然是零，但如果使用 MaybeUninit 模式...

    let data_ref = &data;  // Miri 会跟踪哪些字段已初始化
    println!("{}", data_ref.b);  // OK: zeroed 初始化了所有字段
}
```

### 5.2 悬垂指针解引用

**错误示例：**

```rust
fn main() {
    let ptr: *const i32 = {
        let x = 5;
        &x  // x 的生命周期结束
    };  // x 在这里释放

    unsafe {
        println!("{}", *ptr);  // UB! 解引用悬垂指针
    }
}
```

**Miri 输出：**

```bash
error: Undefined Behavior: pointer to alloc2733 was dereferenced
       after this allocation got freed
```

**修复方案：**

```rust
fn main() {
    let x = 5;
    let ptr: *const i32 = &x;  // 确保 x 生命周期覆盖 ptr 的使用

    unsafe {
        println!("{}", *ptr);  // OK
    }
}
```

### 5.3 数据竞争

**错误示例：**

```rust
use std::thread;

static mut COUNTER: i32 = 0;

fn main() {
    let t1 = thread::spawn(|| unsafe {
        for _ in 0..1000 {
            COUNTER += 1;  // 非原子操作，数据竞争！
        }
    });

    let t2 = thread::spawn(|| unsafe {
        for _ in 0..1000 {
            COUNTER += 1;
        }
    });

    t1.join().unwrap();
    t2.join().unwrap();

    unsafe {
        println!("Result: {}", COUNTER);
    }
}
```

**Miri 输出：**

```bash
warning: thread XXX is trying to join thread YYY, but thread YYY
        tried to modify static mut COUNTER which is also being
        accessed by another thread
```

**修复方案：**

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::thread;

static COUNTER: AtomicI32 = AtomicI32::new(0);

fn main() {
    let t1 = thread::spawn(|| {
        for _ in 0..1000 {
            COUNTER.fetch_add(1, Ordering::Relaxed);
        }
    });

    let t2 = thread::spawn(|| {
        for _ in 0..1000 {
            COUNTER.fetch_add(1, Ordering::Relaxed);
        }
    });

    t1.join().unwrap();
    t2.join().unwrap();

    println!("Result: {}", COUNTER.load(Ordering::Relaxed));
}
```

### 5.4 违反别名规则

**Stacked Borrows 违规示例：**

```rust
fn main() {
    let mut x = 5;
    let ptr1 = &mut x as *mut i32;
    let ptr2 = &mut x as *mut i32;  // 创建第二个独占借用

    unsafe {
        *ptr1 = 10;  // 使用 ptr1
        *ptr2 = 20;  // 使用 ptr2 - 违反别名规则！
    }
}
```

**Miri 输出：**

```bash
error: Undefined Behavior: no item granting read access to tag <untagged>
       at the parent location was found in the borrow stack
```

**修复方案：**

```rust
fn main() {
    let mut x = 5;
    let ptr1 = &mut x as *mut i32;

    unsafe {
        *ptr1 = 10;
    }  // 借用在这里结束

    let ptr2 = &mut x as *mut i32;  // 新的借用
    unsafe {
        *ptr2 = 20;
    }
}
```

### 5.5 对齐违规

**错误示例：**

```rust
fn main() {
    let bytes = [0u8; 8];
    let ptr = bytes.as_ptr() as *const u64;

    unsafe {
        // 假设 bytes 未按 8 字节对齐
        println!("{}", *ptr);  // 可能对齐违规！
    }
}
```

**修复方案：**

```rust
fn main() {
    let bytes = [0u8; 8];
    let ptr = bytes.as_ptr() as *const u64;

    unsafe {
        // 使用 read_unaligned 处理未对齐读取
        println!("{}", ptr.read_unaligned());
    }
}
```

### 5.6 整数溢出

**错误示例：**

```rust
fn main() {
    let x: i32 = i32::MAX;
    let y = x + 1;  // 有符号整数溢出 - UB!
}
```

**Miri 输出：**

```bash
error: Undefined Behavior: overflow executing `x + 1`
```

**修复方案：**

```rust
fn main() {
    let x: i32 = i32::MAX;
    let y = x.wrapping_add(1);  // 显式环绕
    // 或使用 checked_add
    if let Some(y) = x.checked_add(1) {
        println!("{}", y);
    }
}
```

---

## 6. 高级使用技巧

### 6.1 与 FFI 代码交互

Miri 默认在隔离模式下运行，与外部函数 (FFI) 交互需要特殊配置：

```rust
// 调用外部 C 函数
extern "C" {
    fn strlen(s: *const c_char) -> size_t;
}

fn main() {
    let s = CString::new("hello").unwrap();
    unsafe {
        let len = strlen(s.as_ptr());
        println!("Length: {}", len);
    }
}
```

**运行方式：**

```bash
# 禁用隔离以允许 FFI 调用
MIRI_DISABLE_ISOLATION=1 cargo miri run
```

### 6.2 环境变量详解

| 环境变量 | 说明 | 示例 |
|:---|:---|:---|
| `MIRI_DISABLE_ISOLATION` | 禁用隔离，允许 FFI | `MIRI_DISABLE_ISOLATION=1` |
| `MIRI_TREE_BORROWS` | 使用 Tree Borrows | `MIRI_TREE_BORROWS=1` |
| `MIRI_BACKTRACE` | 显示完整回溯 | `MIRI_BACKTRACE=1` |
| `MIRI_SEED` | 设置随机种子 | `MIRI_SEED=1234` |
| `MIRI_NUM_THREADS` | 限制线程数 | `MIRI_NUM_THREADS=4` |

### 6.3 测试框架集成

```rust
#[cfg(test)]
mod tests {
    use std::ptr;

    #[test]
    fn test_unsafe_ptr_ops() {
        let mut x = 42;
        let ptr = &mut x as *mut i32;

        unsafe {
            assert_eq!(*ptr, 42);
            *ptr = 100;
            assert_eq!(*ptr, 100);
        }
    }

    #[test]
    fn test_uninitialized_memory() {
        // 使用 MaybeUninit 安全处理未初始化内存
        use std::mem::MaybeUninit;

        let mut x: MaybeUninit<i32> = MaybeUninit::uninit();
        x.write(42);

        unsafe {
            assert_eq!(x.assume_init(), 42);
        }
    }
}
```

**运行测试：**

```bash
# 运行所有测试
cargo miri test

# 运行特定测试
cargo miri test test_unsafe_ptr_ops
```

---

## 7. 实战案例

### 7.1 自定义智能指针验证

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

pub struct MyBox<T> {
    ptr: NonNull<T>,
}

impl<T> MyBox<T> {
    pub fn new(value: T) -> Self {
        let layout = Layout::new::<T>();
        let ptr = unsafe { alloc(layout) as *mut T };

        if ptr.is_null() {
            panic!("Allocation failed");
        }

        unsafe {
            ptr.write(value);
        }

        MyBox {
            ptr: NonNull::new(ptr).unwrap(),
        }
    }

    pub fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }

    pub fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        let layout = Layout::new::<T>();
        unsafe {
            self.ptr.as_ptr().drop_in_place();
            dealloc(self.ptr.as_ptr() as *mut u8, layout);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_box() {
        let mut b = MyBox::new(42);
        assert_eq!(*b.as_ref(), 42);
        *b.as_mut() = 100;
        assert_eq!(*b.as_ref(), 100);
    }

    #[test]
    fn test_my_box_drop() {
        {
            let _b = MyBox::new(String::from("hello"));
        }  // 确保正确释放
    }
}
```

### 7.2 并发数据结构检测

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

pub struct ConcurrentCounter {
    value: AtomicUsize,
}

impl ConcurrentCounter {
    pub fn new() -> Self {
        ConcurrentCounter {
            value: AtomicUsize::new(0),
        }
    }

    pub fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }

    pub fn get(&self) -> usize {
        self.value.load(Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concurrent_counter() {
        let counter = Arc::new(ConcurrentCounter::new());
        let mut handles = vec![];

        for _ in 0..10 {
            let c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..100 {
                    c.increment();
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(counter.get(), 1000);
    }
}
```

### 7.3 Unsafe 抽象边界验证

```rust
/// 安全的字符串转换封装
pub fn safe_transmute_u32_to_bytes(value: u32) -> [u8; 4] {
    value.to_le_bytes()  // 安全、清晰
}

/// 验证手动 transmute 的正确性
pub unsafe fn manual_transmute_u32_to_bytes(value: u32) -> [u8; 4] {
    let ptr = &value as *const u32 as *const u8;
    [
        *ptr.add(0),
        *ptr.add(1),
        *ptr.add(2),
        *ptr.add(3),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transmute() {
        let value: u32 = 0x12345678;

        let safe_bytes = safe_transmute_u32_to_bytes(value);
        let unsafe_bytes = unsafe { manual_transmute_u32_to_bytes(value) };

        assert_eq!(safe_bytes, unsafe_bytes);

        // 验证字节序
        if cfg!(target_endian = "little") {
            assert_eq!(unsafe_bytes[0], 0x78);
            assert_eq!(unsafe_bytes[1], 0x56);
            assert_eq!(unsafe_bytes[2], 0x34);
            assert_eq!(unsafe_bytes[3], 0x12);
        }
    }
}
```

---

## 8. Miri 与其他工具对比

| 特性 | Miri | Kani | Prusti | Valgrind (Memcheck) | AddressSanitizer |
|:---|:---|:---|:---|:---|:---|
| **检测类型** | 运行时 UB | 模型检测 | 合约验证 | 内存错误 | 内存错误 |
| **执行方式** | 解释执行 | 符号执行 | 静态验证 | 动态插桩 | 编译时插桩 |
| **性能开销** | 10-100x | 高 | 中等 | 5-20x | 2-3x |
| **别名规则** | Stacked Borrows | 部分支持 | 支持 | 不支持 | 不支持 |
| **数据竞争** | ✅ | ✅ | ❌ | ❌ | ❌ (需要 TSan) |
| **未初始化** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **需要源码** | ✅ | ✅ | ✅ | 否 | ✅ |
| **Rust 特性** | 完整支持 | 大部分 | 大部分 | 通用 | 通用 |

**选择建议：**

- **Miri**: 开发阶段验证 unsafe 代码，检查 Rust 特定的 UB
- **Kani**: 需要形式化验证关键属性的场景
- **Prusti**: 需要验证前置/后置条件的复杂逻辑
- **Valgrind**: 生产环境部署前的内存检查
- **AddressSanitizer**: CI 中的快速内存错误检测

---

## 9. 最佳实践与常见陷阱

### 9.1 最佳实践

```markdown
1. **CI 集成**: 在持续集成中运行 Miri 测试
   ```yaml
   # .github/workflows/miri.yml
   - name: Run Miri
     run: |
       rustup component add miri
       cargo miri test
   ```

1. **unsafe 代码全覆盖**: 所有 unsafe 代码都应有 Miri 测试

   ```rust
   #[cfg(test)]
   mod miri_tests {
       // 专门的 Miri 测试模块
   }
   ```

2. **多配置测试**: 测试 Stacked Borrows 和 Tree Borrows

   ```bash
   cargo miri test  # Stacked Borrows
   MIRI_TREE_BORROWS=1 cargo miri test  # Tree Borrows
   ```

3. **定期运行**: 每次发布前和重大变更后

4. **配合其他工具**: 与 Clippy、测试、模糊测试结合

```

### 9.2 常见陷阱

**陷阱 1: 忘记 Miri 的非确定性**

```rust
// Miri 不保证检测到所有 UB 路径
fn maybe_ub(flag: bool) {
    if flag {
        let x: i32;
        println!("{}", x);  // 这条路径有 UB
    }
}

// 测试时可能不会触发 flag=true 路径
#[test]
fn test_maybe() {
    maybe_ub(false);  // 通过了，但代码仍有 UB!
}
```

**陷阱 2: 依赖特定布局**

```rust
// ❌ 错误：依赖未定义的布局
struct MyStruct {
    a: u8,
    b: u32,
}

let ptr = &my_struct.a as *const u8;
let b_ptr = unsafe { ptr.add(4) as *const u32 };  // 依赖填充位置！

// ✅ 正确：使用 repr(C) 或显式布局
#[repr(C)]
struct MyStruct {
    a: u8,
    _padding: [u8; 3],
    b: u32,
}
```

**陷阱 3: 忽略 Miri 的限制**

```rust
// Miri 不支持的代码
fn platform_specific() {
    // 内联汇编
    unsafe { asm!("nop"); }  // Miri 报错

    // 某些平台特定的系统调用
}

// 使用条件编译跳过
#[cfg(miri)]
fn platform_specific() {
    // Miri 下的 mock 实现
}

#[cfg(not(miri))]
fn platform_specific() {
    // 真实实现
}
```

---

## 10. 限制与未来方向

### 当前限制

1. **性能**: 解释执行导致 10-100 倍 slowdown
2. **平台支持**: 仅支持部分目标平台
3. **需要源码**: 不能检查闭源代码或第三方库
4. **非完备性**: 不保证检测所有可能的 UB
5. **异步支持**: async/await 支持有限

### 未来方向

- 改进 Tree Borrows 模型
- 更好的异步/并发支持
- 性能优化（JIT 编译）
- 与 Miri 的 IDE 集成

---

## 参考

- [Miri GitHub](https://github.com/rust-lang/miri)
- [Stacked Borrows 论文](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [Tree Borrows 文档](https://github.com/Vanille-N/tree-borrows)
- [Rustonomicon - 未定义行为](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)

---

*文档版本: 2.0.0* | *最后更新: 2026-03*
