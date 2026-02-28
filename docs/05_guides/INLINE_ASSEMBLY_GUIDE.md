# Rust 内联汇编完整指南

> **文档类型**: 高级指南
> **难度**: ⭐⭐⭐⭐⭐ 专家
> **Rust 版本**: 1.93.1+ (nightly 部分特性)
> **最后更新**: 2026-02-28

---

## 📋 目录

- [Rust 内联汇编完整指南](#rust-内联汇编完整指南)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 为什么需要内联汇编](#11-为什么需要内联汇编)
    - [1.2 基本示例](#12-基本示例)
  - [2. 基本语法](#2-基本语法)
    - [2.1 简单示例](#21-简单示例)
  - [3. 操作数类型](#3-操作数类型)
    - [3.1 `in` - 输入操作数](#31-in---输入操作数)
    - [3.2 `out` - 输出操作数](#32-out---输出操作数)
    - [3.3 `inout` - 输入兼输出](#33-inout---输入兼输出)
    - [3.4 `lateout` - 延迟输出](#34-lateout---延迟输出)
    - [3.5 `inlateout` - 延迟输入输出](#35-inlateout---延迟输入输出)
    - [3.6 内存操作数](#36-内存操作数)
  - [4. 寄存器操作](#4-寄存器操作)
    - [4.1 显式寄存器](#41-显式寄存器)
    - [4.2 寄存器约束](#42-寄存器约束)
    - [4.3 保留寄存器](#43-保留寄存器)
  - [5. 标签和控制流](#5-标签和控制流)
    - [5.1 汇编标签](#51-汇编标签)
    - [5.2 条件分支](#52-条件分支)
  - [6. 汇编选项](#6-汇编选项)
    - [6.1 `nomem`](#61-nomem)
    - [6.2 `nostack`](#62-nostack)
    - [6.3 `pure`](#63-pure)
    - [6.4 `noreturn`](#64-noreturn)
    - [6.5 `may_unwind`](#65-may_unwind)
  - [7. 平台特定代码](#7-平台特定代码)
    - [7.1 x86\_64 特定](#71-x86_64-特定)
    - [7.2 AArch64 特定](#72-aarch64-特定)
    - [7.3 多平台抽象](#73-多平台抽象)
  - [8. Naked 函数](#8-naked-函数)
    - [8.1 基本语法 (nightly)](#81-基本语法-nightly)
    - [8.2 系统调用封装](#82-系统调用封装)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 安全封装](#91-安全封装)
    - [9.2 测试验证](#92-测试验证)
    - [9.3 文档和注释](#93-文档和注释)
  - [10. 完整示例：内存屏障](#10-完整示例内存屏障)

---

## 1. 概述

Rust 的内联汇编使用 `asm!` 宏，允许在 Rust 代码中直接嵌入汇编指令。

### 1.1 为什么需要内联汇编

- 访问硬件特定指令（如 CPUID、RDTSC）
- 实现底层优化
- 与硬件直接交互
- 系统编程（操作系统、驱动开发）

### 1.2 基本示例

```rust
use std::arch::asm;

fn read_tsc() -> u64 {
    let low: u32;
    let high: u32;
    unsafe {
        asm!(
            "rdtsc",           // 指令
            lateout("eax") low, // 输出: EAX -> low
            lateout("edx") high, // 输出: EDX -> high
            options(nomem, nostack) // 选项
        );
    }
    ((high as u64) << 32) | (low as u64)
}

fn main() {
    let timestamp = read_tsc();
    println!("时间戳计数器: {}", timestamp);
}
```

---

## 2. 基本语法

```rust
asm!(
    "汇编模板字符串",
    操作数1,
    操作数2,
    ...,
    选项
);
```

### 2.1 简单示例

```rust
use std::arch::asm;

fn add_asm(a: i32, b: i32) -> i32 {
    let result: i32;
    unsafe {
        asm!(
            "add {0}, {1}",     // 汇编指令
            inout(reg) a => result,  // inout: 输入兼输出
            in(reg) b,          // in: 仅输入
        );
    }
    result
}
```

---

## 3. 操作数类型

### 3.1 `in` - 输入操作数

```rust
fn input_example() {
    let x: u64 = 42;
    unsafe {
        asm!(
            "/* 使用 {0} 作为输入 */",
            in(reg) x,  // x 的值加载到寄存器
        );
    }
}
```

### 3.2 `out` - 输出操作数

```rust
fn output_example() -> u64 {
    let result: u64;
    unsafe {
        asm!(
            "mov {0}, 42",  // 将 42 写入输出寄存器
            out(reg) result,
        );
    }
    result
}
```

### 3.3 `inout` - 输入兼输出

```rust
fn inout_example(mut x: u64) -> u64 {
    unsafe {
        asm!(
            "add {0}, 1",   // 读取并修改
            inout(reg) x,
        );
    }
    x
}
```

### 3.4 `lateout` - 延迟输出

用于可能覆盖输入寄存器的输出：

```rust
fn lateout_example() {
    let x: u64 = 42;
    let y: u64;
    unsafe {
        asm!(
            "mov {1}, {0}",
            in(reg) x,
            lateout(reg) y,  // y 可能使用 x 的寄存器
        );
    }
}
```

### 3.5 `inlateout` - 延迟输入输出

```rust
fn inlateout_example(mut x: u64) {
    unsafe {
        asm!(
            "xor {0}, {0}",  // 清零（读取后覆盖）
            inlateout(reg) x,
        );
    }
}
```

### 3.6 内存操作数

```rust
fn memory_example() {
    let mut x: u64 = 42;
    unsafe {
        asm!(
            "mov qword ptr [{0}], 0",  // 写入内存
            in(reg) &mut x,
        );
    }
    assert_eq!(x, 0);
}
```

---

## 4. 寄存器操作

### 4.1 显式寄存器

```rust
fn explicit_register() {
    let eax: u32;
    unsafe {
        asm!(
            "cpuid",
            lateout("eax") eax,
            lateout("ebx") _,
            lateout("ecx") _,
            lateout("edx") _,
            in("eax") 0,  // 查询 vendor ID
        );
    }
}
```

### 4.2 寄存器约束

```rust
fn register_constraints() {
    let x: u64 = 42;
    unsafe {
        // 使用特定类型的寄存器
        asm!(
            "mov {0}, 0",
            out(reg) _,        // 通用寄存器
            // out(reg_abcd) _, // 仅限 a/b/c/d 寄存器
            // out(reg_byte) _, // 8位寄存器
        );
    }
}
```

### 4.3 保留寄存器

```rust
fn preserve_registers() {
    let mut x: u64 = 42;
    unsafe {
        asm!(
            "push rbx",         // 保存 RBX
            "mov rbx, {0}",
            "add rbx, 1",
            "mov {0}, rbx",
            "pop rbx",          // 恢复 RBX
            inout(reg) x,
        );
    }
}
```

---

## 5. 标签和控制流

### 5.1 汇编标签

```rust
fn asm_labels(mut x: u64) -> u64 {
    unsafe {
        asm!(
            "cmp {0}, 10",
            "jle 2f",          // 向前跳转到标签 2
            "sub {0}, 10",
            "2:",              // 标签 2
            "add {0}, 1",
            inout(reg) x,
        );
    }
    x
}
```

### 5.2 条件分支

```rust
fn conditional_asm(input: u64) -> u64 {
    let mut output: u64 = 0;
    unsafe {
        asm!(
            "test {0}, {0}",
            "jz 1f",
            "mov {1}, 1",
            "jmp 2f",
            "1:",
            "mov {1}, 0",
            "2:",
            in(reg) input,
            lateout(reg) output,
        );
    }
    output
}
```

---

## 6. 汇编选项

### 6.1 `nomem`

不访问内存：

```rust
fn pure_computation(x: u64) -> u64 {
    let result: u64;
    unsafe {
        asm!(
            "bswap {0}",  // 仅寄存器操作
            inout(reg) x => result,
            options(nomem),  // 不访问内存
        );
    }
    result
}
```

### 6.2 `nostack`

不使用栈：

```rust
fn no_stack_example(x: u64) -> u64 {
    let result: u64;
    unsafe {
        asm!(
            "mov {0}, {1}",
            lateout(reg) result,
            in(reg) x,
            options(nostack),  // 不 push/pop
        );
    }
    result
}
```

### 6.3 `pure`

纯函数（无副作用，相同输入相同输出）：

```rust
fn pure_example(x: u64) -> u64 {
    let result: u64;
    unsafe {
        asm!(
            "bswap {0}",
            inout(reg) x => result,
            options(pure, nomem, nostack),
        );
    }
    result
}
```

### 6.4 `noreturn`

不返回：

```rust
fn exit_process(code: i32) -> ! {
    unsafe {
        asm!(
            "mov eax, 60",   // sys_exit
            "syscall",
            in("edi") code,
            options(noreturn),
        );
    }
}
```

### 6.5 `may_unwind`

可能抛出异常：

```rust
fn potentially_unwinding() {
    unsafe {
        asm!(
            "call some_c_function",
            options(may_unwind),
        );
    }
}
```

---

## 7. 平台特定代码

### 7.1 x86_64 特定

```rust
#[cfg(target_arch = "x86_64")]
fn x86_specific() {
    let result: u64;
    unsafe {
        asm!(
            "rdmsr",
            in("ecx") 0x1B,  // IA32_APIC_BASE
            lateout("eax") result,
            lateout("edx") _,
        );
    }
}
```

### 7.2 AArch64 特定

```rust
#[cfg(target_arch = "aarch64")]
fn aarch64_specific() {
    let result: u64;
    unsafe {
        asm!(
            "mrs {0}, cntvct_el0",  // 读取虚拟计数器
            lateout(reg) result,
        );
    }
}
```

### 7.3 多平台抽象

```rust
fn read_cycle_counter() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let low: u32;
        let high: u32;
        asm!("rdtsc", lateout("eax") low, lateout("edx") high);
        ((high as u64) << 32) | (low as u64)
    }

    #[cfg(target_arch = "aarch64")]
    unsafe {
        let result: u64;
        asm!("mrs {0}, cntvct_el0", lateout(reg) result);
        result
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    compile_error!("不支持的平台")
}
```

---

## 8. Naked 函数

### 8.1 基本语法 (nightly)

```rust
#![feature(naked_functions)]

use std::arch::asm;

#[naked]
pub extern "C" fn naked_function() {
    unsafe {
        asm!(
            "push rbp",
            "mov rbp, rsp",
            // 函数体
            "pop rbp",
            "ret",
            options(noreturn),
        );
    }
}
```

### 8.2 系统调用封装

```rust
#![feature(naked_functions)]

#[naked]
pub unsafe extern "C" fn syscall_3(
    num: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
) -> usize {
    asm!(
        "mov rax, rdi",   // syscall number
        "mov rdi, rsi",   // arg1
        "mov rsi, rdx",   // arg2
        "mov rdx, rcx",   // arg3
        "syscall",
        "ret",
        options(noreturn),
    );
}
```

---

## 9. 最佳实践

### 9.1 安全封装

```rust
/// 安全地封装不安全的汇编代码
pub fn safe_rdtsc() -> u64 {
    unsafe { read_tsc() }
}

unsafe fn read_tsc() -> u64 {
    // 实际汇编实现
    0
}
```

### 9.2 测试验证

```rust
#[test]
fn test_asm_add() {
    assert_eq!(add_asm(10, 20), 30);
}

#[test]
fn test_asm_bswap() {
    let input: u32 = 0x12345678;
    let expected: u32 = 0x78563412;
    assert_eq!(bswap_u32(input), expected);
}
```

### 9.3 文档和注释

```rust
/// 使用 CPUID 获取 CPU 功能信息
///
/// # Safety
/// 需要确保 CPU 支持 CPUID 指令（所有现代 x86_64 CPU 都支持）
unsafe fn get_cpu_features() -> u64 {
    let result: u64;
    asm!(
        // EAX=1: 获取处理器信息和特性
        "mov eax, 1",
        "cpuid",
        // EDX 包含特性标志
        lateout("rdx") result,
        lateout("eax") _,
        lateout("ebx") _,
        lateout("ecx") _,
    );
    result
}
```

---

## 10. 完整示例：内存屏障

```rust
use std::arch::asm;

/// 内存屏障 - 确保所有之前的内存操作完成
pub fn memory_fence() {
    unsafe {
        asm!(
            "mfence",
            options(nomem, nostack, preserves_flags),
        );
    }
}

/// 读屏障
pub fn read_fence() {
    unsafe {
        asm!(
            "lfence",
            options(nomem, nostack, preserves_flags),
        );
    }
}

/// 写屏障
pub fn write_fence() {
    unsafe {
        asm!(
            "sfence",
            options(nomem, nostack, preserves_flags),
        );
    }
}
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-02-28
**版本**: v1.0 (完整版)
