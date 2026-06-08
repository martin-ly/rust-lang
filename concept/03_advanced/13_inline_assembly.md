> **内容分级**: [专家级]

# 内联汇编 (Inline Assembly)

> **EN**: Inline Assembly
> **Summary**: Low-level inline assembly in Rust using `asm!` and `global_asm!`, covering syntax, constraints, platform-specific features, and safety boundaries.
> **受众**: [专家]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **P** — Process / Platform
> **双维定位**: C×Ana — 分析跨平台内联汇编的语义差异与安全边界
> **定位**: 深入分析 Rust `asm!` 宏的语法、约束系统、寄存器管理，以及 x86_64、aarch64、RISC-V、s390x 四大平台的差异，重点覆盖 Rust 1.96 为 s390x 引入的向量寄存器支持。
> **前置概念**: [Unsafe Rust](./03_unsafe.md) · [FFI](./05_rust_ffi.md) · [Platform Support](../06_ecosystem/17_cross_compilation.md)
> **后置概念**: [Rust for Linux](../07_future/19_rust_for_linux.md) · [Kernel Development](../07_future/19_rust_for_linux.md)

---

> **来源**: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) ·
> [RFC 2873 — Inline Assembly](https://rust-lang.github.io/rfcs/2873-inline-assembly.html) ·
> [Rust By Example — Inline Assembly](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html) ·
> [s390x Vector Support PR](https://github.com/rust-lang/rust/pull/150551) ·
> [LLVM SystemZ Backend](https://llvm.org/docs/SystemZ.html)
> **前置依赖**: [Unsafe Rust](./03_unsafe.md)
> **对应 Crate**: [`c03_control_fn`](../../crates/c03_control_fn/) (底层控制流)

## 📑 目录

- [内联汇编 (Inline Assembly)](#内联汇编-inline-assembly)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 为什么需要内联汇编](#11-为什么需要内联汇编)
    - [1.2 `asm!` 宏基础语法](#12-asm-宏基础语法)
    - [1.3 约束系统 (Constraints)](#13-约束系统-constraints)
    - [1.4 Clobber 与 Options](#14-clobber-与-options)
  - [二、平台差异矩阵](#二平台差异矩阵)
    - [2.1 x86\_64](#21-x86_64)
    - [2.2 aarch64](#22-aarch64)
    - [2.3 RISC-V](#23-risc-v)
    - [2.4 s390x (IBM Z / LinuxONE)](#24-s390x-ibm-z--linuxone)
  - [三、s390x 向量寄存器 (Rust 1.96+)](#三s390x-向量寄存器-rust-196)
    - [3.1 背景：IBM Z 向量扩展](#31-背景ibm-z-向量扩展)
    - [3.2 Rust 1.96 的变更](#32-rust-196-的变更)
    - [3.3 代码示例](#33-代码示例)
    - [3.4 与 x86\_64 SIMD 的对比](#34-与-x86_64-simd-的对比)
  - [四、安全边界与常见陷阱](#四安全边界与常见陷阱)
    - [4.1 编译器无法验证的契约](#41-编译器无法验证的契约)
    - [4.2 常见错误模式](#42-常见错误模式)
  - [五、来源与延伸阅读](#五来源与延伸阅读)
  - [权威来源索引](#权威来源索引)

---

## 一、核心概念

### 1.1 为什么需要内联汇编

Rust 的内联汇编允许在高级代码中直接嵌入底层机器指令，绕过编译器的优化和控制流分析。典型使用场景：

| 场景 | 示例 | 替代方案 |
|:---|:---|:---|
| **特殊 CPU 指令** | CPUID、RDRAND、AES-NI | `core::arch` 内联函数 (优先) |
| **操作系统原语** | 系统调用入口、线程上下文切换 | `libc` crate、标准库封装 |
| **极致性能优化** | 手写 SIMD、循环展开、分支预测提示 | `std::simd`、编译器内建属性 |
| **裸机/内核开发** | MMIO 寄存器访问、启动代码 | `volatile` crate、`mmio` 抽象 |

> **原则**: 内联汇编是**最后手段**。优先使用 `core::arch` 中的类型安全内联函数，它们由编译器验证并在多平台上提供统一抽象。

### 1.2 `asm!` 宏基础语法

```rust
use std::arch::asm;

// 最简形式：无输入输出
unsafe { asm!("nop"); }

// 带输入输出操作数
let mut x: u64 = 10;
unsafe {
    asm!(
        "add {0}, {1}",      // 汇编模板
        inout(reg) x,        // 输出操作数：x 既读又写
        in(reg) 5,           // 输入操作数：常量 5
    );
}
assert_eq!(x, 15);
```

**模板语法**：

- `{0}`、`{1}` ... 按位置引用操作数
- `{name}` 按命名引用：`inout("name" reg) x`
- `{{` 和 `}}` 转义为字面量 `{` 和 `}`

### 1.3 约束系统 (Constraints)

约束告诉编译器如何为操作数分配寄存器或内存：

| 约束 | 含义 | 适用平台 |
|:---|:---|:---|
| `reg` | 通用寄存器 | 所有平台 |
| `reg_abcd` | x86 的 a/b/c/d 寄存器 | x86/x86_64 |
| `vreg` | 向量寄存器 (SIMD) | aarch64, s390x (1.96+) |
| `vreg_low16` | 低 16 个向量寄存器 | aarch64 |
| `xmm_reg` | XMM 寄存器 (128-bit) | x86_64 |
| `ymm_reg` | YMM 寄存器 (256-bit) | x86_64 |
| `zmm_reg` | ZMM 寄存器 (512-bit) | x86_64 |
| `mem` | 内存地址 | 所有平台 |
| `imm` / `const` | 立即数 / 常量 | 所有平台 |

```rust
// 命名操作数 + 向量寄存器约束 (aarch64)
#[cfg(target_arch = "aarch64")]
unsafe fn vector_add(a: &[i32; 4], b: &[i32; 4]) -> [i32; 4] {
    let mut result: [i32; 4] = [0; 4];
    asm!(
        "ld1 {{v0.4s}}, [{a_ptr}]\n\t"
        "ld1 {{v1.4s}}, [{b_ptr}]\n\t"
        "add v2.4s, v0.4s, v1.4s\n\t"
        "st1 {{v2.4s}}, [{res_ptr}]",
        a_ptr = in(reg) a.as_ptr(),
        b_ptr = in(reg) b.as_ptr(),
        res_ptr = in(reg) result.as_mut_ptr(),
        out("v0") _, out("v1") _, out("v2") _,
        options(nostack, preserves_flags),
    );
    result
}
```

### 1.4 Clobber 与 Options

**Clobber**: 显式声明汇编代码修改了哪些未列出的寄存器：

```rust
unsafe {
    asm!(
        "cpuid",
        out("eax") _, out("ebx") _, out("ecx") _, out("edx") _,
        // 无需 inout，因为 cpuid 覆盖这些寄存器
    );
}
```

**Options**: 控制编译器对内联汇编的处理方式：

| Option | 含义 |
|:---|:---|
| `pure` | 无副作用，可被优化掉若输出未使用 |
| `nomem` | 不访问内存，允许编译器重排 |
| `readonly` | 只读内存，不写入 |
| `nostack` | 不修改栈指针 |
| `preserves_flags` | 不修改条件码/标志寄存器 |
| `noreturn` | 永不返回（如无限循环、panic） |
| `att_syntax` / `intel_syntax` | x86 汇编语法风格 |

---

## 二、平台差异矩阵

### 2.1 x86_64

```rust
#[cfg(target_arch = "x86_64")]
unsafe fn read_tsc() -> u64 {
    let mut low: u32;
    let mut high: u32;
    asm!(
        "rdtsc",
        out("eax") low, out("edx") high,
        options(nomem, nostack, preserves_flags),
    );
    ((high as u64) << 32) | (low as u64)
}
```

**特点**: AT&T 语法默认（`att_syntax`），Intel 语法可用（`intel_syntax`）；丰富的寄存器约束（`xmm_reg`、`ymm_reg`、`zmm_reg`）。

### 2.2 aarch64

```rust
#[cfg(target_arch = "aarch64")]
unsafe fn get_cpu_id() -> u64 {
    let mut mpidr: u64;
    asm!(
        "mrs {0}, mpidr_el1",
        out(reg) mpidr,
        options(nomem, nostack, preserves_flags),
    );
    mpidr
}
```

**特点**: 统一寄存器文件（31 个 64-bit 通用寄存器）；向量寄存器约束为 `vreg` / `vreg_low16`；系统寄存器访问通过 `mrs`/`msr`。

### 2.3 RISC-V

```rust
#[cfg(target_arch = "riscv64")]
unsafe fn read_cycle() -> u64 {
    let mut cycle: u64;
    asm!(
        "rdcycle {0}",
        out(reg) cycle,
        options(nomem, nostack, preserves_flags),
    );
    cycle
}
```

**特点**: 模块化 ISA 扩展；标准寄存器约束为 `reg`；浮点寄存器为 `freg`；向量扩展 (RVV) 的约束仍在 nightly 演进中。

### 2.4 s390x (IBM Z / LinuxONE)

```rust
#[cfg(target_arch = "s390x")]
unsafe fn read_tod_clock() -> u64 {
    let mut tod: u64;
    asm!(
        "stck {0}",
        out(reg) tod,
        options(nomem, nostack),
    );
    tod
}
```

**特点**: 大端架构 (big-endian)；16 个 64-bit 通用寄存器 (GPR)；16 个 64-bit 浮点寄存器 (FPR)；**Rust 1.96+ 新增 32 个 128-bit 向量寄存器 (VR) 支持**。

---

## 三、s390x 向量寄存器 (Rust 1.96+)

### 3.1 背景：IBM Z 向量扩展

IBM Z 架构（s390x）在 z13 处理器（2015）引入了向量设施（Vector Facility），提供 32 个 128-bit 向量寄存器（VR0-VR31）。与 x86_64 的 SSE/AVX 不同：

| 维度 | s390x VR | x86_64 XMM/YMM/ZMM |
|:---|:---|:---|
| 寄存器数量 | 32 × 128-bit | 16 × 128-bit / 16 × 256-bit / 32 × 512-bit |
| 数据类型支持 | 整数、浮点、字符串、十进制 | 整数、浮点 |
| 独有指令 | 字符串加载/存储、十进制运算 |  gather/scatter、FMA |
| 对齐要求 | 128-bit 对齐 | 128/256/512-bit 对齐 |

### 3.2 Rust 1.96 的变更

Rust 1.96 之前，`asm!` 在 s390x 上仅支持通用寄存器（`reg`）和浮点寄存器（`freg`）。**1.96 新增了 `vreg` 约束**，允许在 `asm!` 中直接使用 128-bit 向量寄存器。

```rust
// Rust 1.96+ 可用
#[cfg(all(target_arch = "s390x", target_feature = "vector"))]
unsafe fn vector_add_i32(a: &[i32; 4], b: &[i32; 4]) -> [i32; 4] {
    let mut result: [i32; 4] = [0; 4];
    asm!(
        "vl {v0}, 0({a_ptr})\n\t"      // 向量加载 a → VR
        "vl {v1}, 0({b_ptr})\n\t"      // 向量加载 b → VR
        "vaf {v2}, {v0}, {v1}\n\t"     // 向量加法 (32-bit int)
        "vst {v2}, 0({res_ptr})",       // 向量存储结果
        a_ptr = in(reg) a.as_ptr(),
        b_ptr = in(reg) b.as_ptr(),
        res_ptr = in(reg) result.as_mut_ptr(),
        v0 = out(vreg) _,
        v1 = out(vreg) _,
        v2 = out(vreg) _,
        options(nostack),
    );
    result
}
```

> **注意**: `vreg` 约束要求目标启用 `vector` target feature。在编译时需使用 `-C target-feature=+vector` 或确认目标 CPU 支持（z13+）。

### 3.3 代码示例

```rust
#[cfg(all(target_arch = "s390x", target_feature = "vector"))]
mod s390x_vector_demo {
    use std::arch::asm;

    /// 使用 s390x 向量寄存器进行 128-bit XOR
    ///
    /// 对应指令: vx (vector XOR)
    pub unsafe fn vector_xor(a: &[u32; 4], b: &[u32; 4]) -> [u32; 4] {
        let mut result: [u32; 4] = [0; 4];
        asm!(
            "vl %v0, 0({a})\n\t"
            "vl %v1, 0({b})\n\t"
            "vx %v2, %v0, %v1\n\t"
            "vst %v2, 0({res})",
            a = in(reg) a.as_ptr(),
            b = in(reg) b.as_ptr(),
            res = in(reg) result.as_mut_ptr(),
            out("v0") _, out("v1") _, out("v2") _,
            options(nostack),
        );
        result
    }

    /// 使用 vlgvb (vector load grain byte) 提取元素
    pub unsafe fn vector_extract_byte(v: &[u8; 16], index: u8) -> u8 {
        let mut byte: u8 = 0;
        asm!(
            "vl {vr}, 0({v})\n\t"
            "vlgvb {out}, {vr}, {idx}",
            v = in(reg) v.as_ptr(),
            idx = in(reg) index,
            vr = out(vreg) _,
            out = out(reg) byte,
            options(nostack),
        );
        byte
    }
}
```

### 3.4 与 x86_64 SIMD 的对比

```rust
// x86_64 SSE2 等效实现
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
unsafe fn sse2_xor(a: &[u32; 4], b: &[u32; 4]) -> [u32; 4] {
    let mut result: [u32; 4] = [0; 4];
    asm!(
        "movdqu {a}, %xmm0\n\t"
        "movdqu {b}, %xmm1\n\t"
        "pxor %xmm1, %xmm0\n\t"
        "movdqu %xmm0, {res}",
        a = in(xmm_reg) *a,          // 直接传入数组值
        b = in(xmm_reg) *b,
        res = in(xmm_reg) *result,
        options(nostack),
    );
    result
}
```

**关键差异**：

- s390x 使用内存加载/存储指令（`vl`/`vst`），x86_64 SSE 可直接操作内存
- s390x 向量指令使用 `%vN` 寄存器语法，x86_64 使用 `%xmmN`
- s390x 大端序影响向量元素的内存布局解释

---

## 四、安全边界与常见陷阱

### 4.1 编译器无法验证的契约

内联汇编是 Rust 中最"不安全"的特性之一——编译器几乎不做任何验证：

| 契约 | 程序员责任 | 编译器行为 |
|:---|:---|:---|
| 寄存器约束正确性 | 确保约束与实际使用的寄存器匹配 | 仅按约束分配，不检查汇编文本 |
| 内存访问合法性 | 确保所有内存访问在有效范围内 | `nomem`/`readonly` 仅影响优化 |
| 栈使用 | 确保栈操作与 `nostack` 声明一致 | 不生成栈管理代码 |
| 标志寄存器 | 确保条件码在需要时保留 | `preserves_flags` 仅影响优化 |
| 调用约定 | 确保不破坏调用约定所需的寄存器 | 不保存/恢复未声明的寄存器 |

> **定理**: 内联汇编的 `unsafe` 块内，**任何错误都是 UB**，因为编译器无法验证汇编指令的语义。

### 4.2 常见错误模式

```rust
// ❌ 错误：忘记声明 clobber 寄存器
unsafe {
    let mut x: u64 = 10;
    asm!(
        "mov rax, 42",  // 隐式修改 rax，但未声明
        inout(reg) x,
        // 缺少 out("rax") _
    );
    // x 可能不是期望的值，且编译器不知道 rax 被修改
}

// ✅ 正确：显式声明所有修改的寄存器
unsafe {
    let mut x: u64 = 10;
    asm!(
        "mov {tmp}, 42\n\t"
        "add {x}, {tmp}",
        x = inout(reg) x,
        tmp = out(reg) _,
    );
}

// ❌ 错误：误用 nomem 但实际访问内存
unsafe {
    asm!(
        "mov [{ptr}], {val}",  // 写入内存！
        ptr = in(reg) addr,
        val = in(reg) 42,
        options(nomem),       // 错误声明：编译器可能重排或删除
    );
}

// ✅ 正确：移除 nomem 或使用正确的内存约束
unsafe {
    asm!(
        "mov [{ptr}], {val}",
        ptr = in(reg) addr,
        val = in(reg) 42,
        // 不声明 nomem，编译器知道有副作用
    );
}
```

---

## 五、来源与延伸阅读

| 资源 | 说明 |
|:---|:---|
| [Rust Reference: Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) | 权威语法参考 |
| [RFC 2873](https://rust-lang.github.io/rfcs/2873-inline-assembly.html) | 内联汇编设计 RFC |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html) | 交互式教程 |
| [LLVM SystemZ Backend](https://llvm.org/docs/SystemZ.html) | s390x 后端文档 |
| [IBM Z Architecture Principles](https://www.ibm.com/docs/en/zos/2.5.0?topic=operations-vector-instructions) | IBM Z 向量指令参考 |

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---|:---|
| [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) | ✅ 一级 | 官方语法规范 |
| [RFC 2873](https://rust-lang.github.io/rfcs/2873-inline-assembly.html) | ✅ 一级 | 设计决策记录 |
| [s390x Vector Support PR](https://github.com/rust-lang/rust/pull/150551) | ✅ 一级 | Rust 1.96 s390x vreg 实现 |
| [LLVM SystemZ Backend](https://llvm.org/docs/SystemZ.html) | ✅ 二级 | 底层代码生成参考 |
| [IBM Z Vector Instructions](https://www.ibm.com/docs/en/zos/2.5.0?topic=operations-vector-instructions) | ✅ 二级 | 硬件指令集手册 |

---

```rust
#[cfg(test)]
mod tests {
    #[test]
    #[cfg(target_arch = "s390x")]
    fn test_s390x_vector_xor() {
        use super::s390x_vector_demo::*;
        let a = [0xFFFF_FFFFu32; 4];
        let b = [0x0000_0000u32; 4];
        let result = unsafe { vector_xor(&a, &b) };
        assert_eq!(result, a); // x XOR 0 = x
    }
}
```
