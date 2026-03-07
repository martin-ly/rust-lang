# 内联汇编

> **权威来源**: The Rust Reference (Inline Assembly)
> **Rust 版本**: 1.94.0 (stable)
> **难度**: 🔴 高级
> **前置知识**: 汇编基础、Unsafe Rust

---

## 目录

- [内联汇编](#内联汇编)
  - [目录](#目录)
  - [1. 基本语法](#1-基本语法)
    - [1.1 最简单的汇编](#11-最简单的汇编)
    - [1.2 完整结构](#12-完整结构)
  - [2. 操作数类型](#2-操作数类型)
    - [2.1 寄存器约束](#21-寄存器约束)
    - [2.2 具体寄存器](#22-具体寄存器)
    - [2.3 内存操作数](#23-内存操作数)
  - [3. 输入输出](#3-输入输出)
    - [3.1 简单输入输出](#31-简单输入输出)
    - [3.2 读写同一变量](#32-读写同一变量)
    - [3.3 多个输出](#33-多个输出)
  - [4. 实战示例](#4-实战示例)
    - [4.1 获取 CPU ID](#41-获取-cpu-id)
    - [4.2 RDTSC (读取时间戳计数器)](#42-rdtsc-读取时间戳计数器)
    - [4.3 原子操作实现](#43-原子操作实现)
  - [5. 注意事项](#5-注意事项)
    - [5.1 安全注意事项](#51-安全注意事项)
    - [5.2 平台差异](#52-平台差异)
    - [5.3 选项说明](#53-选项说明)
  - [参考](#参考)

---

## 1. 基本语法

### 1.1 最简单的汇编

```rust
use std::arch::asm;

unsafe {
    asm!("nop");  // 执行一个空操作
}
```

### 1.2 完整结构

```rust
unsafe {
    asm!(
        "assembly template",      // 汇编模板
        in(reg) input1,           // 输入操作数
        in(reg) input2,
        out(reg) output,          // 输出操作数
        lateout(reg) clobbered,   // 被修改的寄存器
        options(nostack, preserves_flags)  // 选项
    );
}
```

---

## 2. 操作数类型

### 2.1 寄存器约束

```rust
let mut x: u64 = 5;

unsafe {
    asm!(
        "mov {0}, {1}",
        out(reg) x,       // 输出到任意通用寄存器
        in(reg) 10        // 输入从任意通用寄存器
    );
}

assert_eq!(x, 10);
```

### 2.2 具体寄存器

```rust
let mut ax: u16 = 0;

unsafe {
    asm!(
        "mov {0}, 42",
        out("ax") ax  // 强制使用 AX 寄存器
    );
}
```

### 2.3 内存操作数

```rust
let mut arr: [u64; 4] = [1, 2, 3, 4];

unsafe {
    asm!(
        "add qword ptr [{0} + 8], 10",  // arr[1] += 10
        in(reg) arr.as_mut_ptr()
    );
}

assert_eq!(arr[1], 12);
```

---

## 3. 输入输出

### 3.1 简单输入输出

```rust
fn add(a: u64, b: u64) -> u64 {
    let result: u64;

    unsafe {
        asm!(
            "add {0}, {1}",
            out(reg) result,
            in(reg) a,
            in(reg) b
        );
    }

    result
}
```

### 3.2 读写同一变量

```rust
fn multiply_by_2(x: u64) -> u64 {
    let mut x = x;

    unsafe {
        asm!(
            "shl {0}, 1",  // x <<= 1
            inout(reg) x
        );
    }

    x
}
```

### 3.3 多个输出

```rust
fn div_rem(dividend: u64, divisor: u64) -> (u64, u64) {
    let mut quotient: u64;
    let mut remainder: u64;

    unsafe {
        asm!(
            "div {2}",
            inout("rax") dividend => quotient,
            lateout("rdx") remainder,
            in(reg) divisor,
        );
    }

    (quotient, remainder)
}
```

---

## 4. 实战示例

### 4.1 获取 CPU ID

```rust
fn cpuid(leaf: u32) -> (u32, u32, u32, u32) {
    let mut eax: u32;
    let mut ebx: u32;
    let mut ecx: u32;
    let mut edx: u32;

    unsafe {
        asm!(
            "cpuid",
            inout("eax") leaf => eax,
            lateout("ebx") ebx,
            lateout("ecx") ecx,
            lateout("edx") edx,
        );
    }

    (eax, ebx, ecx, edx)
}

fn main() {
    let (a, b, c, d) = cpuid(0);
    println!("CPUID(0): {:08x} {:08x} {:08x} {:08x}", a, b, c, d);
}
```

### 4.2 RDTSC (读取时间戳计数器)

```rust
fn rdtsc() -> u64 {
    let low: u32;
    let high: u32;

    unsafe {
        asm!(
            "rdtsc",
            lateout("eax") low,
            lateout("edx") high,
            options(nomem, nostack)
        );
    }

    ((high as u64) << 32) | (low as u64)
}

fn measure<F>(f: F) -> u64
where
    F: FnOnce(),
{
    let start = rdtsc();
    f();
    let end = rdtsc();
    end - start
}
```

### 4.3 原子操作实现

```rust
fn atomic_add(ptr: *mut u64, val: u64) -> u64 {
    let result: u64;

    unsafe {
        asm!(
            "lock xadd qword ptr [{0}], {1}",
            in(reg) ptr,
            inout("rax") val => result,
            options(nostack)
        );
    }

    result
}
```

---

## 5. 注意事项

### 5.1 安全注意事项

```rust
// ⚠️ 汇编代码不经过 Rust 安全检查
// - 不检查数组越界
// - 不检查空指针
// - 不检查整数溢出

// ✅ 在 Rust 层做检查
fn safe_asm_op(arr: &mut [u64], index: usize) {
    assert!(index < arr.len());  // 先检查

    unsafe {
        asm!(
            "inc qword ptr [{0} + {1} * 8]",
            in(reg) arr.as_mut_ptr(),
            in(reg) index,
        );
    }
}
```

### 5.2 平台差异

```rust
// x86_64 汇编
#[cfg(target_arch = "x86_64")]
fn arch_specific() {
    unsafe {
        asm!("mov rax, 42");
    }
}

// AArch64 汇编
#[cfg(target_arch = "aarch64")]
fn arch_specific() {
    unsafe {
        asm!("mov x0, 42");
    }
}
```

### 5.3 选项说明

```rust
unsafe {
    asm!(
        "instruction",
        options(
            pure,           // 无副作用，可重复执行
            nomem,          // 不访问内存
            nostack,        // 不修改栈
            preserves_flags // 保留标志寄存器
        )
    );
}
```

---

## 参考

- [The Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)
- [Rust Inline Assembly RFC](https://rust-lang.github.io/rfcs/2873-inline-asm.html)

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
