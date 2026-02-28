# Rust 内联汇编完整指南

> **文档状态**: ✅ 完整
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **适用范围**: x86/x86_64, ARM/AArch64, RISC-V

---

## 目录

- [Rust 内联汇编完整指南](#rust-内联汇编完整指南)
  - [目录](#目录)
  - [快速开始](#快速开始)
  - [基础语法](#基础语法)
    - [asm! 宏基本结构](#asm-宏基本结构)
    - [global\_asm! 全局汇编](#global_asm-全局汇编)
  - [操作数详解](#操作数详解)
    - [1. 输入操作数 (in)](#1-输入操作数-in)
    - [2. 输出操作数 (out)](#2-输出操作数-out)
    - [3. 输入输出操作数 (inout)](#3-输入输出操作数-inout)
    - [4. 延迟输出 (lateout)](#4-延迟输出-lateout)
    - [5. 内存操作数 (mem)](#5-内存操作数-mem)
    - [6. 标签和跳转](#6-标签和跳转)
  - [汇编选项](#汇编选项)
    - [选项组合示例](#选项组合示例)
  - [平台特定指南](#平台特定指南)
    - [x86/x86\_64](#x86x86_64)
    - [ARM/AArch64](#armaarch64)
    - [RISC-V](#risc-v)
  - [实战示例](#实战示例)
    - [1. 系统调用封装](#1-系统调用封装)
    - [2. SIMD 操作 (x86\_64 AVX)](#2-simd-操作-x86_64-avx)
    - [3. 原子操作（自定义实现）](#3-原子操作自定义实现)
  - [与 naked 函数配合](#与-naked-函数配合)
  - [常见陷阱](#常见陷阱)
    - [陷阱 1: 忘记标记 clobbered 寄存器](#陷阱-1-忘记标记-clobbered-寄存器)
    - [陷阱 2: 输入输出操作数混淆](#陷阱-2-输入输出操作数混淆)
    - [陷阱 3: 忘记内存屏障](#陷阱-3-忘记内存屏障)
    - [陷阱 4: 平台假设](#陷阱-4-平台假设)
  - [总结](#总结)

---

## 快速开始

```rust
// 最简单的内联汇编
use std::arch::asm;

fn main() {
    let mut x: u64 = 1;
    unsafe {
        asm!(
            "add {0}, {1}",      // 汇编指令
            inout(reg) x,        // 输入输出操作数
            in(reg) 5,           // 输入操作数
        );
    }
    assert_eq!(x, 6);
}
```

---

## 基础语法

### asm! 宏基本结构

```rust
asm!(
    "汇编指令模板",           // 必需
    操作数1,                  // 可选
    操作数2,
    ...,
    options(选项1, 选项2),    // 可选
);
```

### global_asm! 全局汇编

```rust
use std::arch::global_asm;

// 在模块级别定义全局汇编代码
global_asm!(
    ".global my_function",
    "my_function:",
    "    ret",
);

extern "C" {
    fn my_function();
}
```

---

## 操作数详解

### 1. 输入操作数 (in)

```rust
let x: u64 = 42;
unsafe {
    asm!(
        "mov rax, {0}",     // 使用位置参数
        in("rax") x,        // 绑定到 rax 寄存器
    );
}
```

### 2. 输出操作数 (out)

```rust
let mut y: u64;
unsafe {
    asm!(
        "mov {0}, 42",
        out(reg) y,         // 输出到变量 y
    );
}
```

### 3. 输入输出操作数 (inout)

```rust
let mut z: u64 = 10;
unsafe {
    asm!(
        "add {0}, 5",
        inout(reg) z,       // 既是输入也是输出
    );
    assert_eq!(z, 15);
}
```

### 4. 延迟输出 (lateout)

```rust
// lateout: 在输入操作数使用完之后再写入
// 避免寄存器分配冲突
unsafe {
    asm!(
        "cpuid",
        in("eax") 0,                    // 输入
        lateout("ebx") _,               // 延迟输出（丢弃）
        lateout("ecx") _,               // 延迟输出（丢弃）
        lateout("edx") _,               // 延迟输出（丢弃）
    );
}
```

### 5. 内存操作数 (mem)

```rust
let mut arr = [1u64; 4];
unsafe {
    asm!(
        "mov qword ptr [{0}], 42",      // 直接内存访问
        in(reg) arr.as_mut_ptr(),
    );
}
assert_eq!(arr[0], 42);
```

### 6. 标签和跳转

```rust
// 使用本地标签
let mut result: u64;
unsafe {
    asm!(
        "cmp {0}, 10",
        "jle 1f",                       // 向前跳转到标签 1
        "mov {1}, 1",                   // 大于 10
        "jmp 2f",
        "1:",                           // 标签 1
        "mov {1}, 0",                   // 小于等于 10
        "2:",                           // 标签 2
        in(reg) 15,
        out(reg) result,
    );
}
assert_eq!(result, 1);
```

---

## 汇编选项

| 选项 | 含义 | 使用场景 |
|------|------|----------|
| `pure` | 无副作用，纯计算 | 允许编译器优化重复调用 |
| `nomem` | 不访问内存 | 寄存器操作 |
| `noreturn` | 不返回 | panic, exit, 无限循环 |
| `nostack` | 不调整栈指针 | 简单计算 |
| `preserves_flags` | 保留 CPU 标志位 | 需要保持条件码 |
| `may_unwind` | 可能展开栈 | 调用可能 panic 的函数 |

### 选项组合示例

```rust
// 纯计算，无副作用
unsafe fn add_asm(a: u64, b: u64) -> u64 {
    let result: u64;
    asm!(
        "add {0}, {1}",
        out(reg) result,
        in(reg) a,
        in(reg) b,
        options(pure, nomem, nostack),  // 纯计算选项
    );
    result
}

// 不返回的汇编
unsafe fn exit_process(code: i32) -> ! {
    asm!(
        "mov rdi, {0}",
        "mov rax, 60",      // sys_exit
        "syscall",
        in(reg) code,
        options(noreturn),  // 不会返回
    );
}
```

---

## 平台特定指南

### x86/x86_64

```rust
#[cfg(target_arch = "x86_64")]
mod x86_64_examples {
    use std::arch::asm;

    /// 读取时间戳计数器 (RDTSC)
    pub unsafe fn rdtsc() -> u64 {
        let low: u32;
        let high: u32;
        asm!(
            "rdtsc",
            out("eax") low,
            out("edx") high,
            options(nomem, nostack),
        );
        ((high as u64) << 32) | (low as u64)
    }

    /// 内存屏障
    pub unsafe fn memory_fence() {
        asm!(
            "mfence",
            options(nomem, nostack, preserves_flags),
        );
    }

    /// CPUID 指令
    pub unsafe fn cpuid(leaf: u32) -> (u32, u32, u32, u32) {
        let eax: u32;
        let ebx: u32;
        let ecx: u32;
        let edx: u32;
        asm!(
            "cpuid",
            inout("eax") leaf => eax,
            lateout("ebx") ebx,
            lateout("ecx") ecx,
            lateout("edx") edx,
        );
        (eax, ebx, ecx, edx)
    }
}
```

### ARM/AArch64

```rust
#[cfg(target_arch = "aarch64")]
mod aarch64_examples {
    use std::arch::asm;

    /// 读取系统计数器
    pub unsafe fn read_cntvct() -> u64 {
        let cnt: u64;
        asm!(
            "mrs {0}, cntvct_el0",
            out(reg) cnt,
            options(nomem, nostack),
        );
        cnt
    }

    /// 数据同步屏障
    pub unsafe fn dsb() {
        asm!(
            "dsb sy",
            options(nomem, nostack),
        );
    }

    /// 指令同步屏障
    pub unsafe fn isb() {
        asm!(
            "isb",
            options(nomem, nostack),
        );
    }
}
```

### RISC-V

```rust
#[cfg(target_arch = "riscv64")]
mod riscv_examples {
    use std::arch::asm;

    /// 读取 cycle 计数器
    pub unsafe fn read_cycle() -> u64 {
        let cycle: u64;
        asm!(
            "rdcycle {0}",
            out(reg) cycle,
            options(nomem, nostack),
        );
        cycle
    }

    ///  fence 指令
    pub unsafe fn fence() {
        asm!(
            "fence",
            options(nomem, nostack),
        );
    }
}
```

---

## 实战示例

### 1. 系统调用封装

```rust
/// Linux x86_64 系统调用
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub unsafe fn syscall_3(
    num: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
) -> usize {
    let result: usize;
    asm!(
        "syscall",
        inout("rax") num => result,
        in("rdi") arg1,
        in("rsi") arg2,
        in("rdx") arg3,
        lateout("rcx") _,   // 被 syscall 破坏
        lateout("r11") _,   // 被 syscall 破坏
        options(nostack),
    );
    result
}

/// 使用示例：write 系统调用
pub fn sys_write(fd: usize, buf: &[u8]) -> isize {
    unsafe {
        syscall_3(
            1,                  // SYS_write
            fd,
            buf.as_ptr() as usize,
            buf.len(),
        ) as isize
    }
}
```

### 2. SIMD 操作 (x86_64 AVX)

```rust
#[cfg(target_arch = "x86_64")]
pub unsafe fn add_vectors_avx(a: &[f32; 8], b: &[f32; 8]) -> [f32; 8] {
    let mut result: [f32; 8] = [0.0; 8];
    asm!(
        "vmovups {2}, (%rsi)",      // 加载 a
        "vmovups {3}, (%rdx)",      // 加载 b
        "vaddps {2}, {2}, {3}",     // a + b
        "vmovups (%rcx), {2}",      // 存储结果

        inout("ymm0") a => _,
        inout("ymm1") b => _,
        in("rsi") a.as_ptr(),
        in("rdx") b.as_ptr(),
        in("rcx") result.as_mut_ptr(),
        options(nostack),
    );
    result
}
```

### 3. 原子操作（自定义实现）

```rust
use std::sync::atomic::Ordering;

pub struct AtomicU64 {
    value: std::cell::UnsafeCell<u64>,
}

unsafe impl Send for AtomicU64 {}
unsafe impl Sync for AtomicU64 {}

impl AtomicU64 {
    pub fn new(val: u64) -> Self {
        Self {
            value: std::cell::UnsafeCell::new(val),
        }
    }

    /// 原子加载（使用内联汇编实现）
    #[cfg(target_arch = "x86_64")]
    pub unsafe fn load(&self, _order: Ordering) -> u64 {
        let result: u64;
        asm!(
            "mov {0}, qword ptr [{1}]",
            out(reg) result,
            in(reg) self.value.get(),
            options(nostack, readonly),
        );
        result
    }

    /// 原子比较交换
    #[cfg(target_arch = "x86_64")]
    pub unsafe fn compare_exchange(
        &self,
        current: u64,
        new: u64,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<u64, u64> {
        let prev: u64;
        asm!(
            "lock cmpxchg qword ptr [{2}], {1}",
            inout("rax") current => prev,
            in(reg) new,
            in(reg) self.value.get(),
            options(nostack),
        );
        if prev == current {
            Ok(prev)
        } else {
            Err(prev)
        }
    }
}
```

---

## 与 naked 函数配合

裸函数（`#[naked]`）与内联汇编结合，可以完全控制函数 prologue/epilogue：

```rust
#![feature(naked_functions)]

use std::arch::naked_asm;

/// 裸函数示例：信号处理跳转
#[naked]
pub extern "C" fn naked_trampoline() {
    unsafe {
        naked_asm!(
            "push rbp",
            "mov rbp, rsp",
            "sub rsp, 16",
            "call {handler}",
            "leave",
            "ret",
            handler = sym signal_handler,
        );
    }
}

extern "C" fn signal_handler() {
    // 实际处理逻辑
    println!("Signal handled!");
}

/// 系统调用入口（裸函数）
#[cfg(target_arch = "x86_64")]
#[naked]
pub unsafe extern "C" fn syscall_entry() {
    naked_asm!(
        "swapgs",                       // 切换 GS 段
        "mov gs:[0], rsp",             // 保存用户栈
        "mov rsp, gs:[8]",             // 加载内核栈
        "push r11",                     // 保存 rflags
        "push rcx",                     // 保存返回地址
        "call {handler}",
        "pop rcx",
        "pop r11",
        "mov rsp, gs:[0]",             // 恢复用户栈
        "swapgs",
        "sysretq",
        handler = sym handle_syscall,
    );
}

extern "C" fn handle_syscall() {
    // 系统调用处理
}
```

---

## 常见陷阱

### 陷阱 1: 忘记标记 clobbered 寄存器

```rust
// ❌ 错误：未标记被修改的寄存器
unsafe {
    asm!(
        "mov rax, 42",      // 修改了 rax 但未声明
    );
}

// ✅ 正确：使用 lateout 声明
unsafe {
    asm!(
        "mov {0}, 42",
        lateout("rax") _,   // 声明 rax 被修改
    );
}
```

### 陷阱 2: 输入输出操作数混淆

```rust
let mut x = 10;
// ❌ 错误：使用 out 当应该用 inout
unsafe {
    asm!(
        "add {0}, 5",       // 读取未初始化的值！
        out(reg) x,
    );
}

// ✅ 正确：使用 inout
unsafe {
    asm!(
        "add {0}, 5",
        inout(reg) x,       // x 既是输入也是输出
    );
}
```

### 陷阱 3: 忘记内存屏障

```rust
// ❌ 错误：编译器可能重排内存操作
static mut COUNTER: u64 = 0;
unsafe {
    COUNTER += 1;
    asm!("nop");
}

// ✅ 正确：添加内存屏障或声明内存访问
unsafe {
    asm!(
        "lock inc qword ptr [{0}]",
        in(reg) &raw mut COUNTER,
        options(nomem, preserves_flags),
    );
}
```

### 陷阱 4: 平台假设

```rust
// ❌ 错误：假设只有 x86_64
pub fn get_cycle_count() -> u64 {
    unsafe {
        let low: u32;
        let high: u32;
        asm!(
            "rdtsc",
            out("eax") low,
            out("edx") high,
        );
        ((high as u64) << 32) | (low as u64)
    }
}

// ✅ 正确：条件编译
#[cfg(target_arch = "x86_64")]
pub fn get_cycle_count() -> u64 {
    unsafe {
        let low: u32;
        let high: u32;
        asm!(
            "rdtsc",
            out("eax") low,
            out("edx") high,
        );
        ((high as u64) << 32) | (low as u64)
    }
}

#[cfg(target_arch = "aarch64")]
pub fn get_cycle_count() -> u64 {
    unsafe {
        let cnt: u64;
        asm!(
            "mrs {0}, cntvct_el0",
            out(reg) cnt,
        );
        cnt
    }
}
```

---

## 总结

| 主题 | 关键点 |
|------|--------|
| 基本语法 | `asm!` 和 `global_asm!` |
| 操作数 | `in`, `out`, `inout`, `lateout`, `mem` |
| 选项 | `pure`, `nomem`, `noreturn`, `nostack`, `preserves_flags` |
| 平台支持 | x86_64, AArch64, RISC-V |
| 裸函数 | `#[naked]` + `naked_asm!` |

---

**最后更新**: 2026-02-28
**参考**: [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)
