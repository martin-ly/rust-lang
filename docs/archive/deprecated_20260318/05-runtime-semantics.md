# Rust 运行时行为语义

## 目录

- [Rust 运行时行为语义](#rust-运行时行为语义)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 运行时系统的定义](#11-运行时系统的定义)
    - [1.2 Rust 运行时特性（最小运行时）](#12-rust-运行时特性最小运行时)
    - [1.3 编译时 vs 运行时保证](#13-编译时-vs-运行时保证)
  - [2. 内存模型语义](#2-内存模型语义)
    - [2.1 栈内存语义](#21-栈内存语义)
      - [2.1.1 栈帧分配语义](#211-栈帧分配语义)
      - [2.1.2 局部变量生命周期](#212-局部变量生命周期)
      - [2.1.3 函数调用栈语义](#213-函数调用栈语义)
      - [2.1.4 尾调用优化](#214-尾调用优化)
    - [2.2 堆内存语义](#22-堆内存语义)
      - [2.2.1 堆分配语义（Box）](#221-堆分配语义box)
      - [2.2.2 内存布局语义](#222-内存布局语义)
      - [2.2.3 对齐和填充语义](#223-对齐和填充语义)
      - [2.2.4 内存回收语义（RAII）](#224-内存回收语义raii)
    - [2.3 内存管理语义](#23-内存管理语义)
      - [2.3.1 Drop trait 语义](#231-drop-trait-语义)
      - [2.3.2 析构顺序语义](#232-析构顺序语义)
      - [2.3.3 遗忘语义（forget/leak）](#233-遗忘语义forgetleak)
      - [2.3.4 循环引用处理](#234-循环引用处理)
  - [3. 类型系统运行时语义](#3-类型系统运行时语义)
    - [3.1 零大小类型语义](#31-零大小类型语义)
      - [3.1.1 ZST 内存布局](#311-zst-内存布局)
      - [3.1.2 幽灵数据语义](#312-幽灵数据语义)
      - [3.1.3 标记类型语义](#313-标记类型语义)
    - [3.2 DST 动态大小类型](#32-dst-动态大小类型)
      - [3.2.1 Slice 语义](#321-slice-语义)
      - [3.2.2 Trait 对象语义](#322-trait-对象语义)
      - [3.2.3 胖指针语义](#323-胖指针语义)
    - [3.3 类型擦除语义](#33-类型擦除语义)
      - [3.3.1 Any trait 语义](#331-any-trait-语义)
      - [3.3.2 向下转换语义](#332-向下转换语义)
      - [3.3.3 运行时类型信息](#333-运行时类型信息)
  - [4. 调度语义](#4-调度语义)
    - [4.1 线程调度语义](#41-线程调度语义)
      - [4.1.1 OS 调度器交互](#411-os-调度器交互)
      - [4.1.2 线程状态转换](#412-线程状态转换)
      - [4.1.3 上下文切换开销](#413-上下文切换开销)
    - [4.2 任务调度语义](#42-任务调度语义)
      - [4.2.1 异步任务调度](#421-异步任务调度)
      - [4.2.2 工作窃取调度](#422-工作窃取调度)
      - [4.2.3 优先级调度](#423-优先级调度)
    - [4.3 协作式调度语义](#43-协作式调度语义)
      - [4.3.1 yield\_now 语义](#431-yield_now-语义)
      - [4.3.2 自愿让出语义](#432-自愿让出语义)
      - [4.3.3 忙等待 vs 阻塞](#433-忙等待-vs-阻塞)
  - [5. I/O 运行时语义](#5-io-运行时语义)
    - [5.1 阻塞 I/O 语义](#51-阻塞-io-语义)
      - [5.1.1 系统调用语义](#511-系统调用语义)
      - [5.1.2 线程阻塞语义](#512-线程阻塞语义)
      - [5.1.3 唤醒语义](#513-唤醒语义)
    - [5.2 异步 I/O 语义](#52-异步-io-语义)
      - [5.2.1 反应堆模式](#521-反应堆模式)
      - [5.2.2 事件通知语义](#522-事件通知语义)
      - [5.2.3 就绪状态管理](#523-就绪状态管理)
    - [5.3 文件系统语义](#53-文件系统语义)
      - [5.3.1 打开/关闭语义](#531-打开关闭语义)
      - [5.3.2 读/写语义](#532-读写语义)
      - [5.3.3 同步语义（fsync）](#533-同步语义fsync)
  - [6. 网络运行时语义](#6-网络运行时语义)
    - [6.1 TCP 语义](#61-tcp-语义)
      - [6.1.1 连接建立语义](#611-连接建立语义)
      - [6.1.2 数据传输语义](#612-数据传输语义)
      - [6.1.3 连接关闭语义](#613-连接关闭语义)
    - [6.2 UDP 语义](#62-udp-语义)
      - [6.2.1 数据报语义](#621-数据报语义)
      - [6.2.2 无连接语义](#622-无连接语义)
      - [6.2.3 可靠性语义](#623-可靠性语义)
    - [6.3 超时和重试语义](#63-超时和重试语义)
      - [6.3.1 连接超时](#631-连接超时)
      - [6.3.2 读写超时](#632-读写超时)
      - [6.3.3 重试策略](#633-重试策略)
  - [7. 时间语义](#7-时间语义)
    - [7.1 时钟语义](#71-时钟语义)
      - [7.1.1 系统时钟](#711-系统时钟)
      - [7.1.2 单调时钟](#712-单调时钟)
      - [7.1.3 高精度计时器](#713-高精度计时器)
    - [7.2 睡眠语义](#72-睡眠语义)
      - [7.2.1 线程睡眠](#721-线程睡眠)
      - [7.2.2 异步延迟](#722-异步延迟)
      - [7.2.3 定时器语义](#723-定时器语义)
    - [7.3 超时语义](#73-超时语义)
      - [7.3.1 相对超时](#731-相对超时)
      - [7.3.2 绝对超时](#732-绝对超时)
      - [7.3.3 超时组合](#733-超时组合)
  - [8. 错误处理运行时语义](#8-错误处理运行时语义)
    - [8.1 Panic 运行时语义](#81-panic-运行时语义)
      - [8.1.1 展开调用栈](#811-展开调用栈)
      - [8.1.2 Drop 守卫调用](#812-drop-守卫调用)
      - [8.1.3 中止 vs 展开](#813-中止-vs-展开)
    - [8.2 结果传播语义](#82-结果传播语义)
      - [8.2.1 ? 运算符语义](#821--运算符语义)
      - [8.2.2 错误转换](#822-错误转换)
      - [8.2.3 回溯收集](#823-回溯收集)
    - [8.3 信号处理语义](#83-信号处理语义)
      - [8.3.1 Unix 信号语义](#831-unix-信号语义)
      - [8.3.2 Windows 异常语义](#832-windows-异常语义)
      - [8.3.3 信号安全代码](#833-信号安全代码)
  - [9. FFI 运行时语义](#9-ffi-运行时语义)
    - [9.1 C 互操作语义](#91-c-互操作语义)
      - [9.1.1 ABI 兼容性](#911-abi-兼容性)
      - [9.1.2 调用约定](#912-调用约定)
      - [9.1.3 类型转换语义](#913-类型转换语义)
    - [9.2 内存布局语义](#92-内存布局语义)
      - [9.2.1 repr(C) 语义](#921-reprc-语义)
      - [9.2.2 repr(transparent) 语义](#922-reprtransparent-语义)
      - [9.2.3 packed 语义](#923-packed-语义)
    - [9.3 回调语义](#93-回调语义)
      - [9.3.1 回调安全性](#931-回调安全性)
      - [9.3.2 线程边界](#932-线程边界)
      - [9.3.3 生命周期管理](#933-生命周期管理)
  - [10. 性能运行时语义](#10-性能运行时语义)
    - [10.1 缓存语义](#101-缓存语义)
      - [10.1.1 CPU 缓存行为](#1011-cpu-缓存行为)
      - [10.1.2 缓存一致性](#1012-缓存一致性)
      - [10.1.3 伪共享避免](#1013-伪共享避免)
    - [10.2 向量化语义](#102-向量化语义)
      - [10.2.1 SIMD 语义](#1021-simd-语义)
      - [10.2.2 自动向量化](#1022-自动向量化)
      - [10.2.3 显式向量化](#1023-显式向量化)
    - [10.3 分支预测语义](#103-分支预测语义)
      - [10.3.1 分支提示](#1031-分支提示)
      - [10.3.2 概率预测](#1032-概率预测)
      - [10.3.3 优化指导](#1033-优化指导)
  - [11. 安全运行时语义](#11-安全运行时语义)
    - [11.1 边界检查语义](#111-边界检查语义)
      - [11.1.1 数组边界检查](#1111-数组边界检查)
      - [11.1.2 切片边界检查](#1112-切片边界检查)
      - [11.1.3 优化边界检查](#1113-优化边界检查)
    - [11.2 空指针检查语义](#112-空指针检查语义)
      - [11.2.1 Option/Result 语义](#1121-optionresult-语义)
      - [11.2.2 空指针优化](#1122-空指针优化)
      - [11.2.3 可空类型](#1123-可空类型)
    - [11.3 未定义行为检测](#113-未定义行为检测)
      - [11.3.1 Miri 语义解释器](#1131-miri-语义解释器)
      - [11.3.2 Sanitizers 语义](#1132-sanitizers-语义)
      - [11.3.3 调试断言](#1133-调试断言)
  - [12. 平台抽象语义](#12-平台抽象语义)
    - [12.1 跨平台语义](#121-跨平台语义)
      - [12.1.1 平台差异抽象](#1211-平台差异抽象)
      - [12.1.2 条件编译语义](#1212-条件编译语义)
      - [12.1.3 特性门控](#1213-特性门控)
    - [12.2 标准库语义](#122-标准库语义)
      - [12.2.1 std vs core vs alloc](#1221-std-vs-core-vs-alloc)
      - [12.2.2 平台特定扩展](#1222-平台特定扩展)
      - [12.2.3 兼容性保证](#1223-兼容性保证)
  - [13. 总结](#13-总结)
    - [Rust 运行时语义的核心特点](#rust-运行时语义的核心特点)
    - [运行时与编译时的分工](#运行时与编译时的分工)
    - [Unsafe 代码的语义边界](#unsafe-代码的语义边界)
    - [性能与安全的平衡](#性能与安全的平衡)
  - [附录：符号说明](#附录符号说明)
  - [参考文献](#参考文献)

---

## 1. 引言

### 1.1 运行时系统的定义

**运行时系统（Runtime System）** 是编程语言在执行期间所依赖的基础设施。它负责管理程序执行期间的各种资源和服务，包括内存管理、线程调度、异常处理等。

形式化地说，运行时系统可以定义为：

$$
\text{Runtime} : \text{Program} \times \text{Environment} \to \text{Behavior}
$$

其中：

- **Program**：编译后的机器码
- **Environment**：操作系统和硬件环境
- **Behavior**：可观察的程序行为

```rust
// 运行时系统涉及的典型操作
fn runtime_operations() {
    // 内存分配（运行时堆分配器）
    let boxed = Box::new(42);

    // 线程创建（运行时线程管理）
    let handle = std::thread::spawn(|| { 42 });

    // 异常处理（运行时 panic 处理）
    let result = std::panic::catch_unwind(|| {
        panic!("runtime error");
    });

    // I/O 操作（运行时系统调用封装）
    let mut buffer = String::new();
    std::io::stdin().read_line(&mut buffer).unwrap();
}
```

### 1.2 Rust 运行时特性（最小运行时）

Rust 采用了**最小运行时（Minimal Runtime）** 的设计理念，将尽可能多的工作移到编译时完成。

| 特性 | Rust | C/C++ | Java/Go |
|------|------|-------|---------|
| 垃圾回收 | 无（RAII） | 无/可选 | 有 |
| 运行时线程 | 无绿色线程 | 无 | 有（M:N 调度） |
| 反射 | 有限 | 有（RTTI） | 完整 |
| 异常处理 | 无栈展开（可选） | 有 | 有 |

**形式化描述最小运行时：**

$$
\text{RustRuntime} = \text{Startup} + \text{PanicHandler} + \text{GlobalAlloc} + \text{OSAbstraction}
$$

```rust
// #![no_std] 环境：仅使用 core 和 alloc
#![no_std]
#![no_main]

use core::panic::PanicInfo;

// 自定义最小运行时入口
#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 程序入口点
    main();

    // 系统退出
    unsafe {
        libc::exit(0);
    }
}

fn main() {
    // 用户代码
}

// 必要的 panic 处理
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

### 1.3 编译时 vs 运行时保证

Rust 的核心理念是**将成本从运行时转移到编译时**：

```
┌─────────────────────────────────────────────────────────────┐
│                      程序生命周期                            │
├──────────────┬──────────────────────┬───────────────────────┤
│   编译时      │      链接时           │        运行时          │
├──────────────┼──────────────────────┼───────────────────────┤
│ • 类型检查    │ • 符号解析           │ • 内存分配             │
│ • 借用检查    │ • 静态链接           │ • 系统调用             │
│ • 生命周期    │ • 重定位             │ • 线程调度             │
│ • 泛型单态化  │ • 库加载             │ • I/O 操作             │
│ • 常量求值    │                      │ • 信号处理             │
└──────────────┴──────────────────────┴───────────────────────┘
```

**形式化对比：**

$$
\text{CompileTime} : \Gamma \vdash e : \tau \quad \text{（类型判断在编译时完成）}
$$

$$
\text{Runtime} : \langle e, \sigma \rangle \to \langle v, \sigma' \rangle \quad \text{（状态转换在运行时发生）}
$$

```rust
// 编译时保证示例
fn compile_time_guarantees() {
    // 编译时类型检查
    let x: i32 = 42;
    // let y: String = x;  // 编译错误：类型不匹配

    // 编译时借用检查
    let mut s = String::from("hello");
    let r = &s;
    // s.push_str(" world");  // 编译错误：与不可变借用冲突
    println!("{}", r);

    // 编译时生命周期检查
    let r;
    {
        let local = String::from("temp");
        // r = &local;  // 编译错误：生命周期不够长
    }
}

// 运行时行为示例
fn runtime_behavior() {
    // 运行时内存分配
    let vec = vec![1, 2, 3];  // 堆分配发生在运行时

    // 运行时数组索引检查
    let first = vec[0];  // 可能 panic（越界）

    // 运行时动态分发
    let trait_obj: &dyn std::fmt::Display = &42;
    println!("{}", trait_obj);
}
```

---

## 2. 内存模型语义

### 2.1 栈内存语义

#### 2.1.1 栈帧分配语义

**栈帧（Stack Frame）** 是函数调用时在栈上分配的内存区域，包含局部变量、参数和返回地址。

$$
\text{StackFrame}(f) = \text{Params} \cup \text{Locals} \cup \text{SavedRegs} \cup \text{RetAddr}
$$

```rust
fn stack_frame_semantics() {
    // 栈帧布局（概念上）：
    // ┌─────────────────┐ ← 高地址
    // │   返回地址       │
    // ├─────────────────┤
    // │   保存的寄存器   │
    // ├─────────────────┤
    // │   局部变量 y     │
    // ├─────────────────┤
    // │   局部变量 x     │
    // ├─────────────────┤
    // │   参数           │
    // └─────────────────┘ ← 栈指针 (RSP/ESP)

    let x = 42i32;           // 栈分配 4 字节
    let y = [1u8; 100];      // 栈分配 100 字节

    inner_function(x);
} // 栈帧在此处释放

fn inner_function(param: i32) {
    let local = param * 2;   // 新的栈帧
    println!("{}", local);
}
```

**与操作系统的交互：**

```rust
// Linux x86_64 栈帧布局
// 使用 rbp（基址指针）和 rsp（栈指针）
//
// push rbp           ; 保存旧基址指针
// mov rbp, rsp       ; 设置新基址指针
// sub rsp, N         ; 为局部变量分配 N 字节
// ... 函数体 ...
// mov rsp, rbp       ; 恢复栈指针
// pop rbp            ; 恢复基址指针
// ret                ; 返回

// Rust 默认启用栈溢出保护
fn stack_protection() {
    // 编译器会自动插入栈金丝雀（stack canary）检查
    // 在函数序言处写入随机值
    // 在函数尾声处检查该值是否被修改
    let _large_array = [0u8; 10000];
}
```

#### 2.1.2 局部变量生命周期

局部变量的生命周期与栈帧绑定：

$$
\text{Lifetime}(v) = [\text{entry}(f), \text{exit}(f)]
$$

```rust
fn local_variable_lifetime() {
    // 变量生命周期语义

    'block1: {
        let a = String::from("hello");  // ← a 在此处创建
        println!("{}", a);
    }  // ← a 在此处释放（调用 drop）

    'block2: {
        let b = vec![1, 2, 3];          // ← b 在此处创建
        let c = &b;                      // 借用开始
        println!("{:?}", c);
    }  // ← b 和 c 在此处释放

    // 早期释放（通过 drop）
    let d = Box::new(42);
    drop(d);  // 显式释放
    // d 不再可用
}
```

#### 2.1.3 函数调用栈语义

函数调用遵循**调用约定（Calling Convention）**：

```rust
// 调用栈增长方向（从高地址到低地址）
//
// ┌─────────────────┐
// │   main 的栈帧   │
// ├─────────────────┤
// │   foo 的栈帧    │ ← 当前
// ├─────────────────┤
// │   bar 的栈帧    │
// └─────────────────┘ ← 栈顶

fn call_stack_semantics() {
    let x = 1;
    let y = foo(x);
    println!("{}", y);
}

fn foo(a: i32) -> i32 {
    let b = a * 2;
    bar(b)
}

fn bar(c: i32) -> i32 {
    c + 1
}
```

**System V AMD64 ABI 调用约定：**

| 方面 | 约定 |
|------|------|
| 参数传递 | RDI, RSI, RDX, RCX, R8, R9，然后栈 |
| 返回值 | RAX, RDX |
| 被调用者保存 | RBX, RBP, R12-R15 |
| 调用者保存 | RAX, RCX, RDX, RSI, RDI, R8-R11 |

#### 2.1.4 尾调用优化

**尾调用优化（Tail Call Optimization, TCO）** 将尾递归转换为循环，避免栈溢出。

```rust
// 非尾递归（需要栈空间）
fn factorial_recursive(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial_recursive(n - 1)  // 不是尾调用：需要保存 n
    }
}

// 尾递归形式（可被优化）
fn factorial_tail(n: u64, acc: u64) -> u64 {
    if n <= 1 {
        acc
    } else {
        factorial_tail(n - 1, n * acc)  // 尾调用：当前栈帧可被重用
    }
}

// Rust 目前不保证 TCO，建议显式使用循环
fn factorial_iterative(n: u64) -> u64 {
    let mut result = 1;
    for i in 2..=n {
        result *= i;
    }
    result
}
```

### 2.2 堆内存语义

#### 2.2.1 堆分配语义（Box）

**Box<T>** 提供了在堆上分配内存的唯一所有权语义：

$$
\text{Box}(T) : \text{Own}(T) \land \text{HeapAllocated}(T)
$$

```rust
use std::alloc::{GlobalAlloc, Layout, System};

fn heap_allocation_semantics() {
    // Box 分配语义
    let boxed = Box::new([0u8; 1024]);

    // 内存布局：
    // 栈：指针（8 字节）
    // 堆：1024 字节数据

    // 底层调用（概念上）：
    // 1. layout = Layout::from_size_align(1024, 1)
    // 2. ptr = System.alloc(layout)
    // 3. 初始化内存
    // 4. 返回 Box::from_raw(ptr)

    println!("堆指针: {:p}", boxed.as_ref());

    // 离开作用域时：
    // 1. 调用 drop(boxed)
    // 2. System.dealloc(ptr, layout)
}

// 与操作系统的交互：
// Linux: malloc -> brk/mmap
// Windows: HeapAlloc -> VirtualAlloc
```

#### 2.2.2 内存布局语义

Rust 的数据布局遵循特定的对齐规则：

$$
\text{size}(T) = \sum_{i} \text{align_up}(\text{size}(f_i), \text{align}(f_i))
$$

```rust
use std::mem;

fn memory_layout_semantics() {
    // 基本类型的对齐
    println!("u8 对齐: {}", mem::align_of::<u8>());     // 1
    println!("u16 对齐: {}", mem::align_of::<u16>());   // 2
    println!("u32 对齐: {}", mem::align_of::<u32>());   // 4
    println!("u64 对齐: {}", mem::align_of::<u64>());   // 8

    // 结构体内存布局
    struct Example {
        a: u8,   // 1 字节
        b: u32,  // 4 字节，对齐到 4
        c: u16,  // 2 字节
    }

    // 内存布局：
    // Offset 0: a (1 byte)
    // Offset 1-3: padding (3 bytes)
    // Offset 4-7: b (4 bytes)
    // Offset 8-9: c (2 bytes)
    // Offset 10-11: padding (2 bytes) - 对齐到 4
    // Total: 12 bytes

    println!("Example 大小: {}", mem::size_of::<Example>());      // 12
    println!("Example 对齐: {}", mem::align_of::<Example>());      // 4
}
```

#### 2.2.3 对齐和填充语义

```rust
#[repr(C)]  // C 兼容布局
struct CLayout {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(packed)]  // 紧凑布局（无填充）
struct PackedLayout {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(align(16))]  // 自定义对齐
struct AlignedStruct {
    data: u64,
}

fn alignment_semantics() {
    println!("CLayout 大小: {}", std::mem::size_of::<CLayout>());        // 12
    println!("PackedLayout 大小: {}", std::mem::size_of::<PackedLayout>()); // 7
    println!("AlignedStruct 对齐: {}", std::mem::align_of::<AlignedStruct>()); // 16

    // packed 结构体的访问是 unsafe 的
    let packed = PackedLayout { a: 1, b: 2, c: 3 };
    // let b = packed.b;  // 警告：未对齐访问
    let b = unsafe { std::ptr::read_unaligned(&packed.b) };  // 正确方式
}
```

#### 2.2.4 内存回收语义（RAII）

**资源获取即初始化（RAII）** 是 Rust 内存管理的核心：

$$
\text{RAII} : \text{Acquire}(r) \text{ at } t_1 \implies \text{Release}(r) \text{ at } t_2 > t_1
$$

```rust
fn raii_semantics() {
    // RAII 示例
    {
        let file = std::fs::File::open("test.txt").unwrap();
        // 文件在此处打开

        let buffer = vec![0u8; 1024];
        // 堆内存在此处分配

    }  // ← 所有资源在此处自动释放

    // 栈展开时的 RAII
    fn may_panic() {
        let _guard = ScopeGuard::new(|| println!("清理"));
        panic!("出错！");  // 即使 panic，guard 也会被 drop
    }
}

// 自定义 RAII 守卫
struct ScopeGuard<F: FnOnce()> {
    f: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    fn new(f: F) -> Self {
        ScopeGuard { f: Some(f) }
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            f();
        }
    }
}
```

### 2.3 内存管理语义

#### 2.3.1 Drop trait 语义

**Drop** trait 定义了资源释放的语义：

```rust
trait Drop {
    fn drop(&mut self);
}
```

```rust
struct Resource {
    id: u32,
    data: Vec<u8>,
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("资源 {} 正在释放", self.id);
        // 清理操作：关闭文件、释放网络连接等
    }
}

fn drop_semantics() {
    let r1 = Resource { id: 1, data: vec![1, 2, 3] };
    {
        let r2 = Resource { id: 2, data: vec![4, 5, 6] };
        // r2 在此处 drop
    }
    // r1 在此处 drop
}
```

#### 2.3.2 析构顺序语义

Rust 按照**创建顺序的逆序**进行析构：

```rust
fn drop_order_semantics() {
    // 变量按逆序 drop
    let a = Resource { id: 1, data: vec![] };
    let b = Resource { id: 2, data: vec![] };
    let c = Resource { id: 3, data: vec![] };

    // drop 顺序：c → b → a
}

// 结构体字段按定义顺序的逆序 drop
struct Container {
    first: Resource,   // 第二个 drop
    second: Resource,  // 第一个 drop
}

// 元组按索引的逆序 drop
fn tuple_drop_order() {
    let tuple = (
        Resource { id: 1, data: vec![] },
        Resource { id: 2, data: vec![] },
    );
    // drop 顺序：.1 → .0
}

// Vec 按索引的逆序 drop
fn vec_drop_order() {
    let vec = vec![
        Resource { id: 1, data: vec![] },
        Resource { id: 2, data: vec![] },
    ];
    // drop 顺序：[1] → [0]
}
```

#### 2.3.3 遗忘语义（forget/leak）

**mem::forget** 阻止析构函数的调用：

```rust
use std::mem;

fn forget_semantics() {
    let resource = Resource { id: 1, data: vec![1, 2, 3] };
    mem::forget(resource);  // 资源被"遗忘"，不调用 drop

    // 这可能导致内存泄漏！
}

// 循环引用导致的内存泄漏
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    value: i32,
    next: RefCell<Option<Rc<Node>>>,
}

fn reference_cycle_leak() {
    let node1 = Rc::new(Node {
        value: 1,
        next: RefCell::new(None),
    });

    let node2 = Rc::new(Node {
        value: 2,
        next: RefCell::new(Some(Rc::clone(&node1))),
    });

    // 创建循环引用
    *node1.next.borrow_mut() = Some(Rc::clone(&node2));

    // 循环引用导致内存泄漏
    println!("Node1 引用计数: {}", Rc::strong_count(&node1));
    println!("Node2 引用计数: {}", Rc::strong_count(&node2));
}
```

#### 2.3.4 循环引用处理

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

// 使用 Weak 打破循环引用
struct SafeNode {
    value: i32,
    parent: RefCell<Weak<SafeNode>>,  // 弱引用
    children: RefCell<Vec<Rc<SafeNode>>>,
}

fn safe_tree_structure() {
    let root = Rc::new(SafeNode {
        value: 1,
        parent: RefCell::new(Weak::new()),
        children: RefCell::new(vec![]),
    });

    let child = Rc::new(SafeNode {
        value: 2,
        parent: RefCell::new(Rc::downgrade(&root)),
        children: RefCell::new(vec![]),
    });

    root.children.borrow_mut().push(Rc::clone(&child));

    // 根节点引用计数为 1
    println!("Root 强引用计数: {}", Rc::strong_count(&root));
    // 子节点引用计数为 2
    println!("Child 强引用计数: {}", Rc::strong_count(&child));

    // 当 child 变量离开作用域，整个树可以被正确释放
}
```

---

## 3. 类型系统运行时语义

### 3.1 零大小类型语义

#### 3.1.1 ZST 内存布局

**零大小类型（Zero-Sized Types, ZST）** 不占用运行时内存：

$$
\forall T. \text{ZST}(T) \implies \text{size}(T) = 0
$$

```rust
fn zst_semantics() {
    // ZST 示例
    struct Unit;              // 单元类型
    struct Phantom<T>(std::marker::PhantomData<T>);  // 幽灵数据
    enum Void {}              // 空枚举

    // 运行时特性
    println!("Unit 大小: {}", std::mem::size_of::<Unit>());      // 0
    println!("() 大小: {}", std::mem::size_of::<()>());          // 0
    println!("[(); 100] 大小: {}", std::mem::size_of::<[(); 100]>()); // 0

    // Vec<()> 不分配内存
    let vec: Vec<()> = vec![(); 1_000_000];
    println!("Vec<()> 容量: {}", vec.capacity());
    println!("Vec<()> 内存: {}", std::mem::size_of_val(&vec));  // 24
}
```

#### 3.1.2 幽灵数据语义

**PhantomData<T>** 用于在类型系统中标记未使用的泛型参数：

```rust
use std::marker::PhantomData;

// 示例：标记生命周期
struct Buffer<'a> {
    data: *const u8,
    len: usize,
    _marker: PhantomData<&'a u8>,  // 假装拥有 &'a u8
}

// 示例：标记类型参数
struct Id<T> {
    value: u64,
    _marker: PhantomData<T>,  // T 不参与数据，但影响类型系统
}

// 不同 T 的 Id 是不同类型
struct User;
struct Post;

fn id_semantics() {
    let user_id: Id<User> = Id { value: 1, _marker: PhantomData };
    let post_id: Id<Post> = Id { value: 1, _marker: PhantomData };

    // 编译错误：类型不匹配
    // let wrong: Id<User> = post_id;
}
```

#### 3.1.3 标记类型语义

```rust
use std::marker::{Copy, Send, Sync, Sized, Unpin};

// 自动 trait（标记 trait）
fn marker_traits() {
    // Send: 可以跨线程传递所有权
    // Sync: 可以跨线程共享引用
    // Copy: 按位复制而非移动
    // Sized: 编译时已知大小
    // Unpin: 可以安全移动
}

// 自定义标记 trait
unsafe auto trait MyMarker {}

// !MyMarker 为特定类型禁用
impl !MyMarker for *const () {}
```

### 3.2 DST 动态大小类型

#### 3.2.1 Slice 语义

**Slice [T]** 是 DST，运行时大小：

$$
\text{size}([T]) = n \times \text{size}(T) \quad \text{where } n \text{ is runtime value}
$$

```rust
fn slice_semantics() {
    // Slice 的内存表示
    // ┌──────────────┬──────────────┐
    // │  数据指针     │   长度       │
    // │  (usize)     │  (usize)     │
    // └──────────────┴──────────────┘
    // 胖指针（fat pointer）

    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr[1..4];

    println!("Slice 指针: {:p}", slice.as_ptr());
    println!("Slice 长度: {}", slice.len());
    println!("胖指针大小: {}", std::mem::size_of_val(&slice));  // 16
}
```

#### 3.2.2 Trait 对象语义

**Trait 对象**实现了运行时多态：

```rust
trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;
}

struct Circle { radius: f64 }
struct Rectangle { width: f64, height: f64 }

impl Drawable for Circle {
    fn draw(&self) { println!("绘制圆形"); }
    fn area(&self) -> f64 { std::f64::consts::PI * self.radius * self.radius }
}

impl Drawable for Rectangle {
    fn draw(&self) { println!("绘制矩形"); }
    fn area(&self) -> f64 { self.width * self.height }
}

fn trait_object_semantics() {
    // Trait 对象的内存表示
    // ┌──────────────┬──────────────┐
    // │  数据指针     │  vtable 指针  │
    // │  (usize)     │   (usize)    │
    // └──────────────┴──────────────┘

    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle { width: 4.0, height: 3.0 };

    // 创建 trait 对象
    let shapes: Vec<&dyn Drawable> = vec![&circle, &rectangle];

    for shape in &shapes {
        shape.draw();
        println!("面积: {}", shape.area());
    }
}
```

#### 3.2.3 胖指针语义

```rust
fn fat_pointer_semantics() {
    // 瘦指针（thin pointer）
    let x: i32 = 42;
    let thin: *const i32 = &x;
    println!("瘦指针大小: {}", std::mem::size_of_val(&thin));  // 8

    // 胖指针（fat pointer）
    let slice: &[i32] = &[1, 2, 3];
    println!("Slice 胖指针大小: {}", std::mem::size_of_val(&slice));  // 16

    let trait_obj: &dyn std::fmt::Display = &42;
    println!("Trait 对象胖指针大小: {}", std::mem::size_of_val(&trait_obj));  // 16
}
```

### 3.3 类型擦除语义

#### 3.3.1 Any trait 语义

**Any** trait 提供了运行时类型信息：

```rust
use std::any::{Any, TypeId};

fn any_trait_semantics() {
    // 获取 TypeId
    let id_i32 = TypeId::of::<i32>();
    let id_string = TypeId::of::<String>();

    // 类型擦除
    let values: Vec<Box<dyn Any>> = vec![
        Box::new(42i32),
        Box::new("hello".to_string()),
        Box::new(3.14f64),
    ];

    for value in &values {
        if let Some(num) = value.downcast_ref::<i32>() {
            println!("i32: {}", num);
        } else if let Some(s) = value.downcast_ref::<String>() {
            println!("String: {}", s);
        } else {
            println!("其他类型");
        }
    }
}
```

#### 3.3.2 向下转换语义

```rust
fn downcast_semantics() {
    fn process_any(value: &dyn Any) {
        match value.downcast_ref::<i32>() {
            Some(n) => println!("整数: {}", n),
            None => println!("不是整数"),
        }
    }

    process_any(&42i32);
    process_any(&"hello");
}
```

#### 3.3.3 运行时类型信息

```rust
use std::any::type_name;

fn rtti_semantics() {
    // 类型名称（调试用途）
    println!("类型名: {}", type_name::<i32>());
    println!("类型名: {}", type_name::<Vec<String>>());

    // 泛型函数中的类型信息
    fn print_type<T: Any>(value: &T) {
        println!("值的类型: {}", type_name::<T>());
        println!("TypeId: {:?}", TypeId::of::<T>());
    }

    print_type(&42i32);
    print_type(&vec![1, 2, 3]);
}
```

---

## 4. 调度语义

### 4.1 线程调度语义

#### 4.1.1 OS 调度器交互

Rust 线程直接映射到操作系统线程：

```rust
use std::thread;
use std::time::Duration;

fn os_scheduler_semantics() {
    // 创建 OS 线程
    let handle = thread::spawn(|| {
        // 此代码在独立的 OS 线程中运行
        println!("线程 ID: {:?}", thread::current().id());

        // 与 Linux 的交互：clone() 系统调用
        // 与 Windows 的交互：CreateThread API
    });

    // 线程调度由 OS 完成（1:1 模型）
    // Linux: CFS（完全公平调度器）
    // Windows: 优先级抢占式调度

    handle.join().unwrap();
}
```

**Linux 线程创建的系统调用追踪：**

```rust
fn thread_syscall_analysis() {
    // pthread_create 内部调用：
    // 1. mmap/mprotect：分配线程栈
    // 2. clone(CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | ...)
    // 3. 在新线程上下文中调用入口函数

    let handle = thread::spawn(|| {
        // gettid() - 获取线程 ID
        // 线程本地存储通过 fs/gs 段寄存器访问
    });

    handle.join().unwrap();
}
```

#### 4.1.2 线程状态转换

$$
\text{ThreadState} : \{ \text{New}, \text{Runnable}, \text{Running}, \text{Blocked}, \text{Terminated} \}
$$

```rust
fn thread_state_transitions() {
    // New -> Runnable
    let handle = thread::spawn(|| {
        // Runnable -> Running（被调度器选中）
        println!("运行中");

        // Running -> Blocked（等待 I/O）
        std::thread::sleep(Duration::from_millis(100));

        // Blocked -> Runnable -> Running（I/O 完成）
        println!("恢复运行");

        // Running -> Terminated（函数返回）
    });

    // 主线程 Blocked（等待子线程）
    handle.join().unwrap();
    // -> Runnable
}
```

#### 4.1.3 上下文切换开销

```rust
use std::time::Instant;

fn context_switch_overhead() {
    // 测量线程上下文切换开销
    let iterations = 100_000;
    let start = Instant::now();

    let (tx1, rx1) = std::sync::mpsc::channel();
    let (tx2, rx2) = std::sync::mpsc::channel();

    // 创建乒乓线程
    let t1 = thread::spawn(move || {
        for _ in 0..iterations {
            rx1.recv().unwrap();
            tx2.send(()).unwrap();
        }
    });

    let t2 = thread::spawn(move || {
        for _ in 0..iterations {
            tx1.send(()).unwrap();
            rx2.recv().unwrap();
        }
    });

    t1.join().unwrap();
    t2.join().unwrap();

    let elapsed = start.elapsed();
    let switches_per_sec = (iterations * 2) as f64 / elapsed.as_secs_f64();
    println!("每秒上下文切换: {:.0}", switches_per_sec);
    println!("每次切换耗时: {:?}", elapsed / (iterations * 2));
    // 典型值：约 1-10 微秒
}
```

### 4.2 任务调度语义

#### 4.2.1 异步任务调度

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Wake, Waker};
use std::sync::Arc;

// 简单异步运行时实现
struct SimpleExecutor {
    task_queue: Vec<Pin<Box<dyn Future<Output = ()>>>>,
}

impl SimpleExecutor {
    fn run(&mut self) {
        while let Some(mut task) = self.task_queue.pop() {
            struct DummyWaker;
            impl Wake for DummyWaker {
                fn wake(self: Arc<Self>) {}
            }

            let waker = Waker::from(Arc::new(DummyWaker));
            let mut context = Context::from_waker(&waker);

            match task.as_mut().poll(&mut context) {
                Poll::Ready(()) => {}
                Poll::Pending => {
                    // 在实际运行时，会重新加入队列
                }
            }
        }
    }
}
```

#### 4.2.2 工作窃取调度

```rust
// crossbeam-deque 的工作窃取语义
use crossbeam_deque::{Worker, Stealer, Injector};

fn work_stealing_semantics() {
    // 每个线程有自己的工作队列
    let worker = Worker::new_lifo();
    let stealer = worker.stealer();

    // 本地任务（LIFO）
    worker.push(1);
    worker.push(2);
    worker.push(3);

    // 本地执行（栈顺序：3, 2, 1）
    while let Some(task) = worker.pop() {
        println!("本地任务: {}", task);
    }

    // 其他线程可以窃取任务（FIFO）
    std::thread::spawn(move || {
        while let Some(task) = stealer.steal().success() {
            println!("窃取任务: {}", task);
        }
    });
}

// Rayon 的数据并行调度
use rayon::prelude::*;

fn rayon_scheduling() {
    let data: Vec<i32> = (0..10000).collect();

    // 自动工作窃取
    let sum: i32 = data.par_iter()
        .map(|x| x * x)
        .sum();

    // 线程池维护任务队列
    // 当线程空闲时，从其他线程窃取任务
}
```

#### 4.2.3 优先级调度

```rust
// Tokio 的任务优先级（通过任务属性）
#[tokio::main]
async fn priority_scheduling() {
    // 高优先级任务
    let high_priority = tokio::spawn(async {
        tokio::task::yield_now().await;
        println!("高优先级任务");
    });

    // 低优先级任务
    let low_priority = tokio::spawn(async {
        println!("低优先级任务");
    });

    // Tokio 使用多级反馈队列
    // I/O 密集型任务自动获得更高优先级

    let _ = tokio::join!(high_priority, low_priority);
}
```

### 4.3 协作式调度语义

#### 4.3.1 yield_now 语义

```rust
use std::task::Poll;

fn yield_semantics() {
    // 同步线程让出
    std::thread::yield_now();

    // 异步任务让出
    async fn async_yield() {
        tokio::task::yield_now().await;
    }
}
```

#### 4.3.2 自愿让出语义

```rust
fn cooperative_yielding() {
    // 协作式调度要求任务主动让出
    async fn cooperative_task() {
        for i in 0..100 {
            process_chunk(i);

            // 定期让出，防止阻塞其他任务
            if i % 10 == 0 {
                tokio::task::yield_now().await;
            }
        }
    }

    // 对比：阻塞 vs 非阻塞
    async fn blocking_approach() {
        // 好：只阻塞当前任务
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}

fn process_chunk(i: i32) {
    let _ = i * i;
}
```

#### 4.3.3 忙等待 vs 阻塞

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

fn busy_wait_vs_blocking() {
    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = Arc::clone(&flag);

    // 坏：忙等待（消耗 CPU）
    thread::spawn(move || {
        while !flag_clone.load(Ordering::Relaxed) {
            // 空循环 - 浪费 CPU！
        }
        println!("忙等待检测到标志");
    });

    // 好：阻塞等待（不消耗 CPU）
    thread::spawn(move || {
        thread::park();
        println!("阻塞等待完成");
    });

    // 更好：使用适当的同步原语
    use std::sync::{Condvar, Mutex};
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        while !*started {
            started = cvar.wait(started).unwrap();
        }
        println!("条件变量唤醒");
    });
}
```

---

## 5. I/O 运行时语义

### 5.1 阻塞 I/O 语义

#### 5.1.1 系统调用语义

```rust
use std::fs::File;
use std::io::{self, Read};

fn blocking_io_semantics() {
    // 打开文件：open() 系统调用
    let mut file = File::open("test.txt").unwrap();

    // 读文件：read() 系统调用
    let mut buffer = [0u8; 1024];
    match file.read(&mut buffer) {
        Ok(n) => println!("读取 {} 字节", n),
        Err(e) => println!("错误: {}", e),
    }

    // 系统调用流程：
    // 1. 用户态准备参数
    // 2. int 0x80 / syscall（进入内核态）
    // 3. 内核执行操作
    // 4. 如果数据未就绪，将线程标记为睡眠
    // 5. 调度器选择其他线程运行
    // 6. 数据就绪后，唤醒线程
    // 7. 返回用户态
}
```

#### 5.1.2 线程阻塞语义

```rust
use std::net::TcpListener;
use std::io::Write;

fn thread_blocking_semantics() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();

    // 阻塞等待连接
    match listener.accept() {
        Ok((mut stream, addr)) => {
            println!("连接来自: {}", addr);
            stream.write(b"Hello").unwrap();
        }
        Err(e) => println!("错误: {}", e),
    }
}
```

#### 5.1.3 唤醒语义

```rust
fn io_wakeup_semantics() {
    // 内核使用以下机制唤醒阻塞线程：
    // 1. 中断处理（硬件 I/O 完成）
    // 2. 信号（软中断）
    // 3. 定时器
}
```

### 5.2 异步 I/O 语义

#### 5.2.1 反应堆模式

```rust
// mio 提供的反应堆模式
use mio::{Events, Interest, Poll, Token};
use mio::net::TcpListener;

fn reactor_pattern_semantics() {
    let mut poll = Poll::new().unwrap();
    let mut events = Events::with_capacity(1024);

    let addr = "127.0.0.1:9000".parse().unwrap();
    let mut listener = TcpListener::bind(addr).unwrap();

    poll.registry()
        .register(&mut listener, Token(0), Interest::READABLE)
        .unwrap();

    loop {
        poll.poll(&mut events, None).unwrap();

        for event in events.iter() {
            match event.token() {
                Token(0) => {
                    let (stream, addr) = listener.accept().unwrap();
                    println!("接受连接: {}", addr);
                }
                _ => {}
            }
        }
    }
}
```

#### 5.2.2 事件通知语义

```rust
fn io_event_notification_semantics() {
    // Linux: epoll
    // epoll_create()  - 创建 epoll 实例
    // epoll_ctl()     - 注册/修改/删除文件描述符
    // epoll_wait()    - 等待事件

    // BSD/macOS: kqueue
    // EVFILT_READ   - 可读事件
    // EVFILT_WRITE  - 可写事件

    // Windows: IOCP
    // CreateIoCompletionPort()
    // GetQueuedCompletionStatus()
}
```

#### 5.2.3 就绪状态管理

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

async fn readiness_management() {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await.unwrap();

    // 内部状态机：
    // 1. 检查是否可读（通过 epoll/kqueue/IOCP）
    // 2. 如果不可读，返回 Poll::Pending，注册 waker
    // 3. 当可读时，waker 被调用，任务重新调度
    // 4. 再次 poll，执行实际读取

    let mut buffer = [0u8; 1024];
    let n = stream.read(&mut buffer).await.unwrap();
}
```

### 5.3 文件系统语义

#### 5.3.1 打开/关闭语义

```rust
use std::fs::OpenOptions;

fn file_open_semantics() {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o644)
        .open("test.txt")
        .unwrap();

    // 系统调用：
    // Linux: openat()
    // Windows: CreateFileW()
}

impl Drop for File {
    fn drop(&mut self) {
        // 关闭文件描述符
        // Linux: close()
    }
}
```

#### 5.3.2 读/写语义

```rust
use std::io::{Read, Write, Seek, SeekFrom};

fn file_rw_semantics() {
    let mut file = File::create("test.txt").unwrap();

    // 写入：用户空间缓冲区 -> 内核页缓存 -> 异步刷盘
    file.write_all(b"Hello, World!").unwrap();

    // 读取：先检查页缓存，未命中则从磁盘读取
    file.seek(SeekFrom::Start(0)).unwrap();
    let mut buffer = String::new();
    file.read_to_string(&mut buffer).unwrap();
}
```

#### 5.3.3 同步语义（fsync）

```rust
use std::os::unix::io::AsRawFd;
use std::fs::File;
use std::io::Write;

fn fsync_semantics() {
    let mut file = File::create("important.txt").unwrap();
    file.write_all(b"重要数据").unwrap();

    // 确保数据写入磁盘
    file.sync_all().unwrap();  // fsync()
    // 或
    file.sync_data().unwrap();  // fdatasync()
}
```

---

## 6. 网络运行时语义

### 6.1 TCP 语义

#### 6.1.1 连接建立语义

```rust
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

fn tcp_connection_establishment() {
    let listener = TcpListener::bind("127.0.0.1:8080").unwrap();

    // TCP 三次握手：
    // 1. SYN      -> 客户端发送 SYN
    // 2. SYN-ACK  <- 服务器回复 SYN-ACK
    // 3. ACK      -> 客户端发送 ACK

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                println!("连接建立: {:?}", stream.peer_addr());
                handle_connection(stream);
            }
            Err(e) => println!("错误: {}", e),
        }
    }
}

fn handle_connection(mut stream: TcpStream) {
    stream.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    stream.set_write_timeout(Some(Duration::from_secs(30))).unwrap();
    stream.set_nodelay(true).unwrap();
}
```

#### 6.1.2 数据传输语义

```rust
use std::io::{Read, Write};

fn tcp_data_transfer() {
    // TCP 提供的是字节流语义
    // 不保留消息边界！

    let mut stream = TcpStream::connect("127.0.0.1:8080").unwrap();
    stream.write_all(&[0u8; 100]).unwrap();

    // 应用层协议示例（长度前缀）：
    // [4 字节长度 | N 字节数据]
}
```

#### 6.1.3 连接关闭语义

```rust
fn tcp_connection_close() {
    // TCP 四次挥手：
    // 1. FIN -> 主动关闭方发送 FIN
    // 2. ACK <- 被动方确认
    // 3. FIN <- 被动方发送 FIN
    // 4. ACK -> 主动方确认

    let mut stream = TcpStream::connect("127.0.0.1:8080").unwrap();

    // 半关闭：只关闭写端，仍可读取
    stream.shutdown(std::net::Shutdown::Write).unwrap();
}
```

### 6.2 UDP 语义

#### 6.2.1 数据报语义

```rust
use std::net::UdpSocket;

fn udp_datagram_semantics() {
    let socket = UdpSocket::bind("127.0.0.1:9000").unwrap();

    // UDP 提供数据报语义
    // 发送和接收保持消息边界

    socket.send_to(b"Hello", "127.0.0.1:9001").unwrap();

    let mut buf = [0u8; 1024];
    match socket.recv_from(&mut buf) {
        Ok((len, src)) => {
            println!("从 {} 收到 {} 字节", src, len);
        }
        Err(e) => println!("错误: {}", e),
    }
}
```

#### 6.2.2 无连接语义

```rust
fn udp_connectionless_semantics() {
    let socket = UdpSocket::bind("0.0.0.0:0").unwrap();

    // 可以向任意地址发送
    socket.send_to(b"Msg1", "1.1.1.1:53").unwrap();
    socket.send_to(b"Msg2", "8.8.8.8:53").unwrap();

    // 也可以"连接"到特定地址
    socket.connect("127.0.0.1:9000").unwrap();
    socket.send(b"Connected message").unwrap();
}
```

#### 6.2.3 可靠性语义

```rust
// 在 UDP 上实现可靠性
fn udp_reliability() {
    // 1. 序列号检测丢失和重复
    // 2. 确认机制（ACK）
    // 3. 超时重传
    // 4. 可选：滑动窗口流量控制
}
```

### 6.3 超时和重试语义

#### 6.3.1 连接超时

```rust
use std::net::TcpStream;
use std::time::Duration;

fn connection_timeout_semantics() {
    // 标准库不支持原生连接超时
    // 需要使用非阻塞模式或线程
}
```

#### 6.3.2 读写超时

```rust
fn read_write_timeout() {
    let stream = TcpStream::connect("127.0.0.1:8080").unwrap();

    stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    stream.set_write_timeout(Some(Duration::from_secs(5))).unwrap();
}
```

#### 6.3.3 重试策略

```rust
use std::time::Duration;
use std::thread;

fn retry_policy() {
    fn retry_with_backoff<F, T>(mut f: F, max_retries: u32) -> Result<T, ()>
    where
        F: FnMut() -> Option<T>,
    {
        let mut retries = 0;
        let mut delay = Duration::from_millis(100);

        loop {
            match f() {
                Some(result) => return Ok(result),
                None if retries < max_retries => {
                    thread::sleep(delay);
                    delay *= 2;
                    delay = std::cmp::min(delay, Duration::from_secs(60));
                    retries += 1;
                }
                None => return Err(()),
            }
        }
    }
}
```

---

## 7. 时间语义

### 7.1 时钟语义

#### 7.1.1 系统时钟

```rust
use std::time::{SystemTime, UNIX_EPOCH};

fn system_clock_semantics() {
    // SystemTime：系统实时时钟
    // 可以向前或向后调整（NTP 同步、闰秒等）

    let now = SystemTime::now();
    println!("当前时间: {:?}", now);

    // 获取时间戳
    match now.duration_since(UNIX_EPOCH) {
        Ok(duration) => {
            println!("Unix 时间戳: {} 秒", duration.as_secs());
        }
        Err(e) => {
            println!("时间在 Epoch 之前: {:?}", e.duration());
        }
    }

    // 时钟可能回退！
    let t1 = SystemTime::now();
    let t2 = SystemTime::now();

    if let Ok(diff) = t2.duration_since(t1) {
        println!("经过: {:?}", diff);
    } else {
        println!("时钟回退了！");
    }
}
```

#### 7.1.2 单调时钟

```rust
use std::time::Instant;

fn monotonic_clock_semantics() {
    // Instant：单调时钟
    // 保证永远不会回退
    // 适合测量时间间隔

    let start = Instant::now();
    do_work();
    let duration = start.elapsed();
    println!("操作耗时: {:?}", duration);

    // 保证：
    let t1 = Instant::now();
    let t2 = Instant::now();
    assert!(t2 >= t1);  // 总是成立

    // 底层实现：
    // Linux: CLOCK_MONOTONIC
    // Windows: QueryPerformanceCounter
    // macOS: mach_absolute_time
}

fn do_work() {
    std::thread::sleep(std::time::Duration::from_millis(10));
}
```

#### 7.1.3 高精度计时器

```rust
fn high_precision_timing() {
    // 测量短操作的时间
    let iterations = 1_000_000;

    let start = Instant::now();
    for _ in 0..iterations {
        black_box(compute());
    }
    let duration = start.elapsed();

    let per_op = duration / iterations;
    println!("每次操作: {:?}", per_op);
}

fn compute() -> i32 {
    42
}

fn black_box<T>(dummy: T) -> T {
    unsafe {
        let ret = std::ptr::read_volatile(&dummy);
        std::mem::forget(dummy);
        ret
    }
}
```

### 7.2 睡眠语义

#### 7.2.1 线程睡眠

```rust
use std::thread;
use std::time::Duration;

fn thread_sleep_semantics() {
    // 线程睡眠：放弃 CPU 时间片
    thread::sleep(Duration::from_millis(100));

    // 操作系统保证：
    // - 至少睡眠指定时间
    // - 可能因调度延迟而更长

    // Linux 实现：
    // nanosleep() 系统调用
}
```

#### 7.2.2 异步延迟

```rust
use tokio::time::{sleep, Duration};

async fn async_delay_semantics() {
    // 异步睡眠：只阻塞当前任务，不阻塞线程

    println!("开始");
    sleep(Duration::from_secs(1)).await;
    println!("1 秒后");

    // 实现原理：
    // 1. 创建定时器，注册到反应堆
    // 2. 返回 Poll::Pending
    // 3. 定时器到期时唤醒任务
    // 4. 任务重新调度，继续执行
}
```

#### 7.2.3 定时器语义

```rust
use tokio::time::{interval, Interval};

async fn timer_semantics() {
    // 间隔定时器
    let mut interval = interval(Duration::from_secs(1));

    for _ in 0..5 {
        interval.tick().await;
        println!("tick!");
    }

    // 语义细节：
    // - 第一次 tick 立即返回
    // - 后续 tick 在上次调用后间隔时间返回
    // - 如果错过时间点，会立即返回（burst 模式）
}
```

### 7.3 超时语义

#### 7.3.1 相对超时

```rust
use tokio::time::{timeout, Duration};

async fn relative_timeout_semantics() {
    // 相对超时：从调用点开始计时

    let result = timeout(
        Duration::from_secs(5),
        slow_operation()
    ).await;

    match result {
        Ok(value) => println!("成功: {}", value),
        Err(_) => println!("超时！"),
    }
}

async fn slow_operation() -> String {
    sleep(Duration::from_secs(10)).await;
    "完成".to_string()
}
```

#### 7.3.2 绝对超时

```rust
use tokio::time::Instant;

async fn absolute_timeout_semantics() {
    let deadline = Instant::now() + Duration::from_secs(30);

    // 在 deadline 前完成所有操作
    while Instant::now() < deadline {
        match timeout_at(deadline, fetch_data()).await {
            Ok(data) => process(data),
            Err(_) => break,
        }
    }
}

async fn timeout_at<T>(deadline: Instant, fut: impl Future<Output = T>) -> Result<T, ()> {
    let now = Instant::now();
    if deadline <= now {
        return Err(());
    }
    timeout(deadline - now, fut).await.map_err(|_| ())
}

async fn fetch_data() -> Vec<u8> {
    vec![]
}

fn process(_data: Vec<u8>) {}
```

#### 7.3.3 超时组合

```rust
use tokio::time::timeout;

async fn timeout_composition() {
    // 总超时 + 每个操作超时
    let overall_result = timeout(Duration::from_secs(60), async {
        for i in 0..10 {
            let item_result = timeout(
                Duration::from_secs(5),
                fetch_item(i)
            ).await;

            match item_result {
                Ok(item) => println!("获取项目: {}", item),
                Err(_) => println!("项目 {} 超时", i),
            }
        }
    }).await;
}

async fn fetch_item(i: u32) -> String {
    sleep(Duration::from_millis(100)).await;
    format!("item-{}", i)
}
```

---

## 8. 错误处理运行时语义

### 8.1 Panic 运行时语义

#### 8.1.1 展开调用栈

```rust
fn panic_unwind_semantics() {
    // Panic 时的栈展开（unwind）

    fn level3() {
        panic!("出错！");
    }

    fn level2() {
        let _guard = ScopeGuard::new(|| println!("level2 清理"));
        level3();
    }

    fn level1() {
        let _guard = ScopeGuard::new(|| println!("level1 清理"));
        level2();
    }

    // 发生 panic 时：
    // 1. level3 panic
    // 2. 栈展开，调用 level2 的 guard drop
    // 3. 栈展开，调用 level1 的 guard drop
}
```

#### 8.1.2 Drop 守卫调用

```rust
struct Guard<F: FnOnce()>(Option<F>);

impl<F: FnOnce()> Drop for Guard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.0.take() {
            f();
        }
    }
}

fn drop_guard_semantics() {
    let _guard = Guard(Some(|| {
        println!("清理资源");
    }));

    // 正常路径：guard 在作用域结束时 drop
    // panic 路径：栈展开时同样调用 drop

    // 注意：如果 drop 中再次 panic，进程将中止（abort）
}
```

#### 8.1.3 中止 vs 展开

```rust
// Cargo.toml:
// [profile.release]
// panic = "abort"  // 或 "unwind"

fn panic_strategy_comparison() {
    // 展开策略（unwind）：
    // - 运行析构函数
    // - 可以捕获 panic
    // - 二进制更大（需要展开表）
    // - 运行时开销

    // 中止策略（abort）：
    // - 立即终止进程
    // - 不运行析构函数
    // - 二进制更小
    // - 更快
    // - 无法捕获 panic

    // 捕获 panic（仅 unwind 策略）
    let result = std::panic::catch_unwind(|| {
        panic!("测试");
    });

    match result {
        Ok(_) => println!("正常返回"),
        Err(_) => println!("捕获到 panic"),
    }
}
```

### 8.2 结果传播语义

#### 8.2.1 ? 运算符语义

```rust
fn question_mark_semantics() -> Result<(), Box<dyn std::error::Error>> {
    // ? 运算符展开：
    // let x = operation()?;
    // 等价于：
    // let x = match operation() {
    //     Ok(val) => val,
    //     Err(e) => return Err(From::from(e)),
    // };

    let file = std::fs::File::open("test.txt")?;
    let mut buf = String::new();
    std::io::Read::read_to_string(&file, &mut buf)?;

    Ok(())
}
```

#### 8.2.2 错误转换

```rust
use std::fmt;
use std::error::Error;

#[derive(Debug)]
struct MyError {
    message: String,
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Error for MyError {}

// From trait 实现错误转换
impl From<std::io::Error> for MyError {
    fn from(e: std::io::Error) -> Self {
        MyError {
            message: format!("IO 错误: {}", e),
        }
    }
}

fn error_conversion() -> Result<(), MyError> {
    let _file = std::fs::File::open("test.txt")?;
    Ok(())
}
```

#### 8.2.3 回溯收集

```rust
use std::backtrace::Backtrace;

fn backtrace_collection() {
    // 获取当前调用栈
    let bt = Backtrace::capture();
    println!("回溯:\n{}", bt);

    // 强制收集完整回溯
    let bt = Backtrace::force_capture();
}

// 在错误中包含回溯
#[derive(Debug)]
struct ErrorWithBacktrace {
    message: String,
    backtrace: Backtrace,
}

impl ErrorWithBacktrace {
    fn new(msg: &str) -> Self {
        Self {
            message: msg.to_string(),
            backtrace: Backtrace::capture(),
        }
    }
}
```

### 8.3 信号处理语义

#### 8.3.1 Unix 信号语义

```rust
#[cfg(unix)]
fn unix_signal_semantics() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    // 设置信号处理器
    let running = Arc::new(AtomicBool::new(true));
    let r = Arc::clone(&running);

    ctrlc::set_handler(move || {
        r.store(false, Ordering::SeqCst);
        println!("\n收到 Ctrl+C");
    }).unwrap();

    println!("运行中...");
    while running.load(Ordering::SeqCst) {
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    println!("优雅退出");
}

// 信号处理器限制（信号安全函数）
// 安全的操作：
// - 原子操作
// - 写入管道/套接字
// - _exit()
//
// 不安全（可能死锁）：
// - 获取锁
// - 分配内存
```

#### 8.3.2 Windows 异常语义

```rust
#[cfg(windows)]
fn windows_exception_semantics() {
    // Windows 使用结构化异常处理（SEH）
    // Rust panic 映射到 SEH

    // Vectored Exception Handler
    // AddVectoredExceptionHandler()
}
```

#### 8.3.3 信号安全代码

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 信号安全的计数器
static SIGNAL_COUNT: AtomicUsize = AtomicUsize::new(0);

fn signal_safe_code() {
    // 信号处理器只能使用信号安全操作
    fn signal_handler(_sig: i32) {
        // OK：原子操作
        SIGNAL_COUNT.fetch_add(1, Ordering::SeqCst);

        // NOT OK：可能死锁
        // println!("信号！");  // 内部使用锁

        // NOT OK：未定义行为
        // let v = vec![1, 2, 3];  // 分配内存
    }
}
```

---

## 9. FFI 运行时语义

### 9.1 C 互操作语义

#### 9.1.1 ABI 兼容性

```rust
use std::os::raw::{c_int, c_char, c_void};

// C 函数声明
extern "C" {
    fn printf(format: *const c_char, ...) -> c_int;
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
}

fn abi_compatibility() {
    // ABI 指定了：
    // - 参数传递方式（寄存器/栈）
    // - 返回值处理
    // - 栈清理责任
    // - 命名修饰（name mangling）

    // "C" ABI：
    // - System V AMD64 ABI（Linux/macOS）
    // - Windows x64 calling convention
}
```

#### 9.1.2 调用约定

```rust
// 定义 C 可调用的函数
#[no_mangle]
pub extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}

// 复杂类型传递
#[repr(C)]
pub struct Point {
    x: f64,
    y: f64,
}

#[no_mangle]
pub extern "C" fn distance(p1: Point, p2: Point) -> f64 {
    ((p2.x - p1.x).powi(2) + (p2.y - p1.y).powi(2)).sqrt()
}
```

#### 9.1.3 类型转换语义

```rust
fn type_conversion_semantics() {
    // Rust 类型到 C 类型映射

    let _: std::os::raw::c_int = 42i32;
    let _: std::os::raw::c_long = 42i64;
    let _: std::os::raw::c_char = 42i8;

    // 字符串转换
    let rust_str = "hello";
    let c_string = std::ffi::CString::new(rust_str).unwrap();
    let c_ptr = c_string.as_ptr();
}
```

### 9.2 内存布局语义

#### 9.2.1 repr(C) 语义

```rust
#[repr(C)]
struct CCompatible {
    a: u8,
    b: u32,
    c: u16,
}

fn repr_c_semantics() {
    // C 布局保证：
    // - 字段按声明顺序排列
    // - 遵循 C 对齐规则
    // - 与 C 结构体兼容

    println!("大小: {}", std::mem::size_of::<CCompatible>());
    println!("对齐: {}", std::mem::align_of::<CCompatible>());
}
```

#### 9.2.2 repr(transparent) 语义

```rust
#[repr(transparent)]
struct Wrapper<T>(T);

#[repr(transparent)]
struct Handle(*mut c_void);

fn repr_transparent_semantics() {
    // transparent 保证：
    // - 单字段结构体的 ABI 与内部类型相同
    // - 零开销抽象

    let x: i32 = 42;
    let w = Wrapper(x);

    // Wrapper<i32> 的 ABI 与 i32 完全相同
}
```

#### 9.2.3 packed 语义

```rust
#[repr(C, packed)]
struct PackedStruct {
    a: u8,
    b: u32,
    c: u16,
}

fn packed_semantics() {
    println!("大小: {}", std::mem::size_of::<PackedStruct>());

    // 访问字段是 unsafe
    let packed = PackedStruct { a: 1, b: 2, c: 3 };
    let b = unsafe {
        std::ptr::read_unaligned(std::ptr::addr_of!(packed.b))
    };
}
```

### 9.3 回调语义

#### 9.3.1 回调安全性

```rust
// 从 C 调用 Rust 回调
extern "C" fn rust_callback(data: *mut c_void, value: c_int) {
    let state = unsafe { &mut *(data as *mut MyState) };
    state.process(value);
}

struct MyState {
    count: i32,
}

impl MyState {
    fn process(&mut self, value: i32) {
        self.count += value;
    }
}
```

#### 9.3.2 线程边界

```rust
use std::sync::mpsc::channel;

fn callback_thread_boundary() {
    // C 回调可能在不同线程调用

    let (tx, rx) = channel();

    extern "C" fn callback(data: *mut c_void) {
        let tx = unsafe { &*(data as *const std::sync::mpsc::Sender<i32>) };
        tx.send(42).unwrap();
    }
}
```

#### 9.3.3 生命周期管理

```rust
struct OwnedContext {
    data: String,
}

impl OwnedContext {
    fn into_raw(self) -> *mut c_void {
        Box::into_raw(Box::new(self)) as *mut c_void
    }

    unsafe fn from_raw(ptr: *mut c_void) -> Box<Self> {
        Box::from_raw(ptr as *mut Self)
    }
}

extern "C" fn callback(ctx: *mut c_void) {
    let ctx = unsafe { &*(ctx as *const OwnedContext) };
    println!("回调数据: {}", ctx.data);
}

fn safe_callback_lifetime() {
    let ctx = OwnedContext {
        data: "重要数据".to_string(),
    };

    let raw_ctx = ctx.into_raw();

    unsafe {
        async_operation(callback, raw_ctx);
    }
}
```

---

## 10. 性能运行时语义

### 10.1 缓存语义

#### 10.1.1 CPU 缓存行为

```rust
use std::time::Instant;

fn cache_behavior_semantics() {
    const SIZE: usize = 1024 * 1024;
    let mut data = vec![0u64; SIZE];

    // 顺序访问（缓存友好）
    let start = Instant::now();
    for i in 0..SIZE {
        data[i] = data[i].wrapping_add(1);
    }
    let sequential_time = start.elapsed();

    // 随机访问（缓存不友好）
    let mut indices: Vec<usize> = (0..SIZE).collect();
    // shuffle...

    // 性能差异：10-100 倍
}
```

#### 10.1.2 缓存一致性

```rust
use std::sync::atomic::{fence, Ordering};

fn cache_coherence_semantics() {
    // MESI 协议

    let data = std::sync::Arc::new(std::sync::atomic::AtomicI64::new(0));
    let data2 = std::sync::Arc::clone(&data);

    std::thread::spawn(move || {
        data2.store(42, Ordering::Relaxed);
        fence(Ordering::Release);
    });

    fence(Ordering::Acquire);
    let value = data.load(Ordering::Relaxed);
}
```

#### 10.1.3 伪共享避免

```rust
use std::sync::atomic::AtomicU64;

#[repr(align(64))]
struct PaddedCounter {
    value: AtomicU64,
}

fn false_sharing_avoidance() {
    // 好：每个计数器在独立缓存行
    let good_counters: Vec<PaddedCounter> = (0..4)
        .map(|_| PaddedCounter { value: AtomicU64::new(0) })
        .collect();

    // 性能差异：伪共享可能导致 10-100 倍减速
}
```

### 10.2 向量化语义

#### 10.2.1 SIMD 语义

```rust
#![feature(portable_simd)]
use std::simd::*;

fn simd_semantics() {
    // 128-bit SIMD (SSE2)
    let a = f32x4::from_array([1.0, 2.0, 3.0, 4.0]);
    let b = f32x4::from_array([5.0, 6.0, 7.0, 8.0]);
    let c = a + b;  // 4 个加法同时执行

    // 256-bit SIMD (AVX)
    let a = f64x4::from_array([1.0, 2.0, 3.0, 4.0]);
    let b = f64x4::from_array([5.0, 6.0, 7.0, 8.0]);
    let c = a * b;
}
```

#### 10.2.2 自动向量化

```rust
fn auto_vectorization() {
    let mut a = [0.0f64; 1024];
    let b = [1.0f64; 1024];
    let c = [2.0f64; 1024];

    // 编译器可以自动向量化
    for i in 0..1024 {
        a[i] = b[i] + c[i];
    }
}
```

#### 10.2.3 显式向量化

```rust
use std::simd::*;

fn explicit_vectorization() {
    let a: Vec<f32> = (0..1024).map(|i| i as f32).collect();
    let b: Vec<f32> = (0..1024).map(|i| (i * 2) as f32).collect();
    let mut c = vec![0.0f32; 1024];

    // 手动 SIMD
    const LANES: usize = 16;

    for (result, (x, y)) in c.chunks_exact_mut(LANES)
        .zip(a.chunks_exact(LANES).zip(b.chunks_exact(LANES)))
    {
        let vx: f32x16 = f32x16::from_slice(x);
        let vy: f32x16 = f32x16::from_slice(y);
        let vz = vx + vy;
        vz.copy_to_slice(result);
    }
}
```

### 10.3 分支预测语义

#### 10.3.1 分支提示

```rust
fn branch_hints() {
    // likely/unlikely（需要 nightly 或外部 crate）

    // 通过代码组织提供提示
    if likely_condition {
        // 热路径
        hot_path();
    } else {
        // 冷路径
        cold_path();
    }
}

#[cold]
fn cold_path() {
    // 标记为冷路径
}
```

#### 10.3.2 概率预测

```rust
fn branch_probability() {
    // 好的模式：一致的分支方向
    let data = vec![1, 2, 3, 4, 5];
    for &x in &data {
        if x > 0 {  // 总是为真
            process(x);
        }
    }
}

fn process(x: i32) { let _ = x; }
```

#### 10.3.3 优化指导

```rust
fn optimization_hints() {
    // 消除分支
    let condition = true;
    let value = condition as i32 * 100;

    // 查表法
    let opcode = 3;
    let handlers: [fn(); 4] = [handler0, handler1, handler2, handler3];
    handlers[opcode]();
}

fn handler0() {}
fn handler1() {}
fn handler2() {}
fn handler3() {}
```

---

## 11. 安全运行时语义

### 11.1 边界检查语义

#### 11.1.1 数组边界检查

```rust
fn array_bounds_checking() {
    let arr = [1, 2, 3, 4, 5];
    let index = 10;

    // 运行时边界检查
    // let x = arr[index];  // panic

    // 安全访问
    match arr.get(index) {
        Some(&x) => println!("值: {}", x),
        None => println!("越界"),
    }

    // 编译器优化：
    // - 如果索引是编译时常量，在编译时检查
    // - 如果编译器能证明索引在范围内，移除检查

    for i in 0..arr.len() {
        println!("{}", arr[i]);  // 可能无边界检查
    }
}
```

#### 11.1.2 切片边界检查

```rust
fn slice_bounds_checking() {
    let slice: &[i32] = &[1, 2, 3, 4, 5];

    // 切片操作也检查边界
    // let sub = &slice[2..10];  // panic

    // 安全切片
    let sub = slice.get(2..4);
    println!("{:?}", sub);  // Some([3, 4])
}
```

#### 11.1.3 优化边界检查

```rust
fn optimize_bounds_checks() {
    let data = vec![1, 2, 3, 4, 5];

    // 编译器可以移除的检查
    for i in 0..data.len() {
        println!("{}", data[i]);  // 无检查
    }

    // 迭代器无边界检查
    for item in &data {
        println!("{}", item);  // 无检查
    }

    // unsafe 方式（如果确信安全）
    unsafe {
        let ptr = data.as_ptr();
        for i in 0..data.len() {
            println!("{}", *ptr.add(i));
        }
    }
}
```

### 11.2 空指针检查语义

#### 11.2.1 Option/Result 语义

```rust
fn option_result_semantics() {
    // Option：可能为空（None）或包含值（Some）
    let maybe_value: Option<i32> = Some(42);

    // 安全解包
    match maybe_value {
        Some(v) => println!("值: {}", v),
        None => println!("无值"),
    }

    // 或使用方法
    let value = maybe_value.unwrap_or(0);

    // Result：可能成功（Ok）或失败（Err）
    let result: Result<i32, &str> = Ok(42);

    // ? 传播错误
    fn may_fail() -> Result<i32, String> {
        let x = result?;
        Ok(x * 2)
    }
}
```

#### 11.2.2 空指针优化

```rust
fn null_pointer_optimization() {
    // 某些类型的 Option 使用空值表示 None

    println!("Option<&i32> 大小: {}", std::mem::size_of::<Option<&i32>>());
    println!("&i32 大小: {}", std::mem::size_of::<&i32>());

    println!("Option<Box<i32>> 大小: {}", std::mem::size_of::<Option<Box<i32>>>());

    // 不适用的类型
    println!("Option<i32> 大小: {}", std::mem::size_of::<Option<i32>>());
}
```

#### 11.2.3 可空类型

```rust
use std::ptr::NonNull;

fn nullable_types() {
    // NonNull<T>：保证非空的指针
    let ptr: NonNull<i32> = NonNull::new(Box::into_raw(Box::new(42))).unwrap();

    unsafe {
        println!("{}", *ptr.as_ptr());
    }
}
```

### 11.3 未定义行为检测

#### 11.3.1 Miri 语义解释器

```rust
// 运行：cargo +nightly miri run

fn miri_undefined_behavior_detection() {
    // Miri 可以检测的未定义行为：

    // 1. 使用未初始化内存
    let x: i32;
    // println!("{}", x);  // UB

    // 2. 悬垂指针解引用
    // let ptr = { let v = vec![1, 2, 3]; v.as_ptr() };
    // unsafe { println!("{}", *ptr); }  // UB

    // 3. 数据竞争
    // 4. 对齐违规
    // 5. 违反引用规则
    // 6. 类型混淆
}
```

#### 11.3.2 Sanitizers 语义

```rust
// AddressSanitizer（ASan）：检测内存错误
// ThreadSanitizer（TSan）：检测数据竞争
// MemorySanitizer（MSan）：检测未初始化内存使用

fn sanitizers_semantics() {
    // ASan 可以检测：
    // - 缓冲区溢出
    // - 使用已释放内存
    // - 内存泄漏
}
```

#### 11.3.3 调试断言

```rust
fn debug_assertions() {
    // debug_assert! 仅在调试构建时检查
    let v = vec![1, 2, 3];
    debug_assert!(!v.is_empty(), "向量不应为空");

    // 调试构建：cargo build
    // 发布构建：cargo build --release
}
```

---

## 12. 平台抽象语义

### 12.1 跨平台语义

#### 12.1.1 平台差异抽象

```rust
use std::path::Path;

fn platform_abstraction() {
    // 路径分隔符
    let path = Path::new("dir").join("file.txt");
    // Windows: dir\file.txt
    // Unix: dir/file.txt

    // 行尾符
    #[cfg(windows)]
    const LINE_ENDING: &str = "\r\n";
    #[cfg(unix)]
    const LINE_ENDING: &str = "\n";
}
```

#### 12.1.2 条件编译语义

```rust
#[cfg(target_os = "linux")]
fn linux_specific() {
    // Linux 特有代码
}

#[cfg(target_os = "windows")]
fn windows_specific() {
    // Windows 特有代码
}

#[cfg(target_arch = "x86_64")]
fn x86_64_specific() {
    // x86_64 特有优化
}

#[cfg(not(target_arch = "wasm32"))]
fn non_wasm_code() {
    // 非 WebAssembly 平台
}
```

#### 12.1.3 特性门控

```rust
// Cargo.toml 中定义特性
// [features]
// default = ["std"]
// std = []

#[cfg(feature = "std")]
pub fn std_function() {
    // 使用标准库
}

#[cfg(not(feature = "std"))]
pub fn no_std_function() {
    // 使用 core + alloc
}

// 运行时特性检测
fn runtime_feature_detection() {
    if is_x86_feature_detected!("avx2") {
        // 使用 AVX2 优化代码
    }
}
```

### 12.2 标准库语义

#### 12.2.1 std vs core vs alloc

```rust
// core：最小子集，无堆分配
#![no_std]
use core::slice;
use core::mem;
use core::ptr;

// alloc：加上堆分配
extern crate alloc;
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::string::String;

// std：完整标准库
// use std::*;
```

**模块层次：**

```
std
├── core（核心类型、切片、迭代器、原子操作）
├── alloc（堆分配类型）
└── sys（平台特定代码）
    ├── unix
    └── windows
```

#### 12.2.2 平台特定扩展

```rust
// Unix 扩展
#[cfg(unix)]
fn unix_extensions() {
    use std::os::unix::{
        fs::PermissionsExt,
        net::UnixStream,
    };

    // Unix 域套接字
    let socket = UnixStream::connect("/tmp/socket").unwrap();

    // 文件权限
    let metadata = std::fs::metadata("file.txt").unwrap();
    let mode = metadata.permissions().mode();
}

// Windows 扩展
#[cfg(windows)]
fn windows_extensions() {
    use std::os::windows::{
        fs::OpenOptionsExt,
    };
}
```

#### 12.2.3 兼容性保证

```rust
// Rust 的版本和兼容性策略

// 1. 语义版本控制
// - 主版本：破坏性变更
// - 次版本：新功能，向后兼容
// - 补丁版本：bug 修复

// 2. Edition 系统
// edition = "2021"

// 3. 稳定 vs Nightly
// 稳定：6 周发布周期，保证兼容性
// Nightly：实验性功能

// 4. 弃用过程
#[deprecated(since = "1.50.0", note = "使用 new_function 代替")]
fn old_function() {}
```

---

## 13. 总结

### Rust 运行时语义的核心特点

1. **最小运行时设计**：将最大工作量移到编译时，保证零成本抽象
2. **RAII 内存管理**：自动资源管理，避免垃圾回收开销
3. **强类型安全**：编译时消除大部分内存错误
4. **零成本抽象**：高级特性编译为高效机器码
5. **平台抽象**：统一的跨平台 API，底层适配各操作系统

### 运行时与编译时的分工

| 检查类型 | 编译时 | 运行时 |
|---------|--------|--------|
| 类型检查 | ✓ | |
| 借用检查 | ✓ | |
| 生命周期验证 | ✓ | |
| 数组边界检查 | 部分 | ✓ |
| 空指针检查 | 部分 | ✓ |
| 内存分配 | | ✓ |
| 线程调度 | | ✓ |
| I/O 操作 | | ✓ |

### Unsafe 代码的语义边界

```rust
// Unsafe 可以执行的操作：
// 1. 解引用裸指针
// 2. 调用 unsafe 函数
// 3. 实现 unsafe trait
// 4. 访问/修改可变静态变量
// 5. 使用内联汇编

// Unsafe 不能改变的语义：
// - 借用规则仍然适用
// - 类型系统仍然有效
// - 并发规则必须遵守

unsafe fn unsafe_boundary() {
    // 必须维护的不变量：
    // - 不创建悬垂引用
    // - 不违反借用规则
    // - 不进行无效类型转换
    // - 不引起数据竞争
}
```

### 性能与安全的平衡

Rust 在运行时语义设计中始终追求性能与安全的平衡：

- **边界检查**：默认安全，编译器优化移除可证明安全的检查
- **类型擦除**：提供动态多态，但保留零大小类型的零成本
- **异步运行时**：协作式调度，无栈协程，高效 I/O 多路复用
- **内存布局**：精细控制内存对齐和填充，优化缓存性能

这份文档为理解 Rust 的运行时行为提供了完整的语义框架，有助于编写高效、安全、跨平台的 Rust 代码。

---

## 附录：符号说明

| 符号 | 含义 |
|------|------|
| $\text{Runtime}$ | 运行时系统 |
| $\text{Box}(T)$ | 堆分配的 T |
| $\text{Own}(T)$ | T 的所有权 |
| $\text{ZST}(T)$ | T 是零大小类型 |
| $\text{size}(T)$ | T 的大小（字节） |
| $\text{align}(T)$ | T 的对齐要求 |
| $\Gamma \vdash e : \tau$ | 类型判断：在环境 $\Gamma$ 下，表达式 $e$ 具有类型 $\tau$ |
| $\langle e, \sigma \rangle \to \langle v, \sigma' \rangle$ | 小步操作语义：表达式 $e$ 在状态 $\sigma$ 下转换到值 $v$ 和状态 $\sigma'$ |

---

## 参考文献

1. The Rust Programming Language - Official Documentation
2. Rust Reference - Memory Model
3. Rust Nomicon - The Dark Arts of Unsafe Rust
4. The Rust Unstable Book - Advanced Features
5. LLVM Language Reference Manual
6. System V AMD64 ABI Specification
7. Linux Kernel Documentation - Memory Management
8. Windows Internals, 7th Edition
