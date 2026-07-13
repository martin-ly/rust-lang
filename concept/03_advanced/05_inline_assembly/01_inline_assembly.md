> **内容分级**: [专家级]

# 内联汇编 (Inline Assembly)

> **EN**: Inline Assembly
> **Summary**: Low-level inline assembly in Rust using `asm!` and `global_asm!`, covering syntax, constraints, platform-specific features, and safety boundaries.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Process / Platform
> **双维定位**: C×Ana — 分析跨平台内联汇编（Inline Assembly）的语义差异与安全边界
> **定位**: 深入分析 Rust `asm!` 宏（Macro）的语法、约束系统、寄存器管理，以及 x86_64、aarch64、RISC-V、s390x 四大平台的差异，重点覆盖 Rust 1.96 为 s390x 引入的向量寄存器支持。
> **前置概念**: [Unsafe Rust](../02_unsafe/01_unsafe.md) · [FFI](../04_ffi/01_rust_ffi.md) · [Platform Support](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) · [Unsafe Rust 模式](../02_unsafe/04_unsafe_rust_patterns.md) · [Generics](../../02_intermediate/01_generics/01_generics.md)
> **后置概念**: [Rust for Linux](../../07_future/04_research_and_experimental/04_rust_for_linux.md) · [Kernel Development](../../07_future/04_research_and_experimental/04_rust_for_linux.md)

---

> **来源**: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) · · [Kohlbecker et al. — Hygienic Macro Expansion](https://doi.org/10.1145/41625.41632) · [Flatt — Binding as Sets of Scopes](https://doi.org/10.1145/2814304.2814305) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [RFC 2873 — Inline Assembly](https://rust-lang.github.io/rfcs//2873-inline-asm.html) ·
> [Rust By Example — Inline Assembly](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html) ·
> [s390x Vector Support PR](https://github.com/rust-lang/rust/pull/150551) ·
> [LLVM SystemZ Backend](https://llvm.org/docs/CompilerWriterInfo.html) ·
> [Intel 64 and IA-32 Architectures Software Developer Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) ·
> [ARM Architecture Reference Manual](https://developer.arm.com/documentation/ddi0487/latest/)
> **前置依赖**: [Unsafe Rust](../02_unsafe/01_unsafe.md)
> **对应 Crate**: [`c03_control_fn`](../../crates/c03_control_fn) (底层控制流)

---

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
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：asm! 宏基本语法（记忆层）](#测验-1asm-宏基本语法记忆层)
    - [测验 2：操作数约束（理解层）](#测验-2操作数约束理解层)
    - [测验 3：用内联汇编实现原子操作（应用层）](#测验-3用内联汇编实现原子操作应用层)
    - [测验 4：clobber 与内存屏障（分析层）](#测验-4clobber-与内存屏障分析层)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)
  - [⚠️ 反例与陷阱](#️-反例与陷阱)
    - [反例：不存在的寄存器约束（rustc 1.97.0 实测）](#反例不存在的寄存器约束rustc-1970-实测)
    - [✅ 修正：使用合法寄存器或类别约束](#-修正使用合法寄存器或类别约束)

---

## 一、核心概念

内联汇编（inline assembly）是「在 Rust 代码中嵌入目标架构机器指令」的机制，四个核心概念：

1. **为什么需要内联汇编**：正当场景只有四类——访问编译器不暴露的 CPU 特性（特殊控制寄存器、`cpuid`、`rdtsc` 精确计时）、实现硬件协议要求的精确指令序列（内存屏障 `mfence`、原子原语的底层实现）、手写超越编译器的极限优化（极罕见，需基准证明）、以及操作系统/嵌入式开发（系统调用入口、上下文切换）。反模式：用汇编「优化」普通算术——现代 LLVM 几乎总是做得更好。
2. **`asm!` 宏基础语法**：`asm!("指令模板", 操作数列表)`——模板中 `{}`/`{name}` 引用操作数；操作数按方向分 `in("reg") expr`（输入）、`out("reg") ret`（输出）、`inout("reg") expr => ret`、`lateout`、`sym`（符号地址）、`const`（立即数）。2020 起稳定（`std::arch::asm`，取代旧 `llvm_asm!`）。
3. **约束系统（Constraints）**：`"reg"`（任意通用寄存器）、架构特定类（x86 的 `"rax"`/`"eax"` 显式寄存器、 `"m"` 内存操作数在部分架构可用）。编译器据约束分配寄存器并插入必要的 mov——约束是「Rust 世界与汇编世界的类型系统」。
4. **Clobber 与 Options**：`options(...)` 声明副作用——`nostack`（不碰栈）、`preserves_flags`（不改标志寄存器）、`readonly`/`pure`（内存访问语义，影响优化器重排）、`nomem`、`att_syntax`。未声明的副作用（如写了内存却加 `nomem`）使优化器基于错误假设重排代码——静默错误，比崩溃难查十倍。

判定一段内联汇编的正确性：操作数方向全、约束精确、options 与指令真实副作用一致——三者任一缺失都是「编译器看不见的不变量」。

### 1.1 为什么需要内联汇编

Rust 的内联汇编允许在高级代码中直接嵌入底层机器指令，绕过编译器的优化和控制流分析。(Source: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html), [RFC 2873 — Inline Assembly](https://rust-lang.github.io/rfcs/2873-inline-asm.html))典型使用场景：

| 场景 | 示例 | 替代方案 |
|:---|:---|:---|
| **特殊 CPU 指令** | CPUID、RDRAND、AES-NI | `core::arch` 内联函数 (优先) |
| **操作系统原语** | 系统调用入口、线程上下文切换 | `libc` crate、标准库封装 |
| **极致性能优化** | 手写 SIMD、循环展开、分支预测提示 | `std::simd`、编译器内建属性 |
| **裸机/内核开发** | MMIO 寄存器访问、启动代码 | `volatile` crate、`mmio` 抽象 |

> **原则**: 内联汇编是**最后手段**。优先使用 `core::arch` 中的类型安全内联函数，它们由编译器验证并在多平台上提供统一抽象。(Source: [Rust By Example — Inline Assembly](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html))

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

- `{0}`、`{1}` ... 按位置引用（Reference）操作数
- `{name}` 按命名引用（Reference）：`inout("name" reg) x`
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

```rust,ignore
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

`asm!` 的可移植性边界由「汇编本身是目标架构方言」决定，本节矩阵对比 Rust 支持的主要目标在三方面的差异：

| 维度 | x86_64 | aarch64 | RISC-V |
|:---|:---|:---|:---|
| 寄存器类 | `reg`/`rax` 等具名 + `xmm`/`ymm` | `reg`/`vreg`（NEON） | `reg`/`freg` |
| 调用约定约束 | System V / Microsoft x64 双 ABI（Windows 目标注意 `rcx`/`rdx` 影子空间） | AAPCS64，`x18` 保留 | 标准 ELF psABI |
| 特性门槛 | `target_feature`（sse/avx）需在安全封装内启用 | 多数特性基线可用 | 扩展（m/a/f/d/c）按目标字符串 |

通用约束：**`asm!` 永远是 `unsafe`**，编译器不校验指令语义只校验操作数约束字符串；`options(nomem, nostack, pure)` 等选项是向编译器作出的**可验证承诺**，错误承诺（如标注 `pure` 却读内存）直接产生 UB。平台矩阵之外，应优先检查 `core::arch` 是否已有对应 intrinsics——有 intrinsics 就不用 `asm!`。

### 2.1 x86_64

```rust,ignore
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

**特点**: 模块（Module）化 ISA 扩展；标准寄存器约束为 `reg`；浮点寄存器为 `freg`；向量扩展 (RVV) 的约束仍在每日构建版演进中。

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

s390x（IBM Z）在 Rust 1.96 获得向量寄存器约束支持，本节说明背景、变更与对比：

- **背景：IBM Z 向量扩展**：z13（2015）起 IBM Z 引入向量设施（Vector Facility）——32 个 128 位向量寄存器 `v0`–`v31`，支持 SIMD 整数/浮点/字符串操作（与 x86 SSE/AVX、ARM NEON 同代际定位）。向量指令在 Linux on Z 与 z/OS 的 COBOL/Java 工作负载加速中是关键路径。
- **Rust 1.96 的变更**：`asm!` 约束系统新增 s390x 向量寄存器类——`vreg`（任意向量寄存器）与显式 `v0`..`v31` 约束，使 `asm!` 能直接操作向量寄存器（此前只能用通用寄存器 `reg` 类，向量代码需外挂 C 汇编文件）。同步稳定化的还有相关 `in/out/lateout` 变体，约束语义与 x86 的 `xmm`/`ymm` 类对齐。
- **代码示例**：典型的「向量加载-加和-存回」三指令序列，输入 `in("vreg")` 两个向量、输出 `out("vreg")` 结果，`options(nostack)` 声明不触栈——结构与 x86_64 的 SSE 加法完全同构。
- **与 x86_64 SIMD 的对比**：寄存器宽度（128 位固定 vs SSE 128/AVX 256/AVX-512 分级）、寄存器数（32 vs 16/32）、约束类名（`vreg` vs `xmm`/`ymm`/`zmm`）。工程结论：跨架构 SIMD 汇编应保持「同构模板 + cfg 分发」结构——算法骨架一致，寄存器约束与指令助记符按平台替换；优先考虑 `std::arch::s390x` 内建 intrinsics（编译器校验约束），`asm!` 仅用于 intrinsics 未覆盖的指令。

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

```rust,ignore
// x86_64 SSE2 等效实现
#[cfg(target_arch = "x86_64")]
// （实际代码需加 #[target_feature] 属性启用 sse2）
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

内联汇编的安全边界由一条总原则定义：**编译器对 `asm!` 块内部零理解**——模板字符串对优化器是不透明的：

- **编译器无法验证的契约**：指令的内存效果（读/写哪些地址）、寄存器副作用（约束未列出的寄存器被改写——x86 的 `mul` 隐含写 `rdx:rax`、`cpuid` 写四个寄存器）、标志寄存器变化（`preserves_flags` 未声明时编译器已保守假设全毁，声明后写错指令即违约）、控制流（汇编内跳转出块是 UB）。这些契约全部以「程序员注释」形式存在，违反即优化器基于错误假设重排/删除代码。
- **常见错误模式**：① 漏写隐含输出（`cpuid` 只声明 `out("eax")` 漏 `ebx/ecx/edx`——编译器可能把其他值分配进这些寄存器）；② `options(pure)` 滥用（声称无副作用的块实际读内存——值被缓存致结果过期）；③ 指针有效性（`in("r") ptr` 不检查对齐/有效——与裸指针同等责任）；④ 跨平台假设（x86 模板在 aarch64 编译失败——`#[cfg(target_arch)]` 分平台实现 + 纯 Rust fallback 是必需工程结构）。

安全实践阶梯：能用 `std::arch` 内建 intrinsics（SIMD、`x86_64::_rdtsc`）就不用 `asm!`——intrinsics 有类型与约束的编译器校验；必须用 `asm!` 时，块外写「契约注释」（输入假设、副作用清单、参考手册条目），并用 Miri/多平台 CI 覆盖。内联汇编的正确性没有「局部保证」——它是 unsafe 的最高形态。

### 4.1 编译器无法验证的契约

内联汇编是 Rust 中最"不安全"的特性之一——编译器几乎不做任何验证：(Source: [Rust Reference — Inline Assembly Safety](https://doc.rust-lang.org/reference/inline-assembly.html#safety))

| 契约 | 程序员责任 | 编译器行为 |
|:---|:---|:---|
| 寄存器约束正确性 | 确保约束与实际使用的寄存器匹配 | 仅按约束分配，不检查汇编文本 |
| 内存访问合法性 | 确保所有内存访问在有效范围内 | `nomem`/`readonly` 仅影响优化 |
| 栈使用 | 确保栈操作与 `nostack` 声明一致 | 不生成栈管理代码 |
| 标志寄存器 | 确保条件码在需要时保留 | `preserves_flags` 仅影响优化 |
| 调用约定 | 确保不破坏调用约定所需的寄存器 | 不保存/恢复未声明的寄存器 |

> **定理**: 内联汇编的 `unsafe` 块内，**任何错误都是 UB**，因为编译器无法验证汇编指令的语义。

### 4.2 常见错误模式

```rust,ignore
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
| [RFC 2873](https://rust-lang.github.io/rfcs//2873-inline-asm.html) | 内联汇编设计 RFC |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html) | 交互式教程 |
| [LLVM SystemZ Backend](https://llvm.org/docs/CompilerWriterInfo.html) | s390x 后端文档 |
| [IBM Z Architecture Principles](https://www.ibm.com/docs/en/zos/2.5.0?topic=operations-vector-instructions) | IBM Z 向量指令参考 |

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---|:---|
| [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) | ✅ 一级 | 官方语法规范 |
| [RFC 2873](https://rust-lang.github.io/rfcs//2873-inline-asm.html) | ✅ 一级 | 设计决策记录 |
| [s390x Vector Support PR](https://github.com/rust-lang/rust/pull/150551) | ✅ 一级 | Rust 1.96 s390x vreg 实现 |
| [LLVM SystemZ Backend](https://llvm.org/docs/CompilerWriterInfo.html) | ✅ 二级 | 底层代码生成参考 |
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

---

## 嵌入式测验

本节测验聚焦内联汇编的安全契约，按认知层级排列：

- **理解层**：`asm!` 与 C 的 `__asm__` 扩展语法差异——Rust 强制显式 `in`/`out`/`inout` 操作数与 clobber 声明，禁止隐式读写；
- **应用层**：为给定指令序列选择正确的寄存器类与 `options` 组合——判定准则是「编译器需要知道什么才能正确调度周围代码」；
- **分析层**：`options` 承诺审计——给定一段 `asm!` 判断其 `options` 是否过强（漏标 `preserves_flags`/`att_syntax` 之外的副作用），过强的承诺 = UB。

作答建议：每题先写出「编译器视角下这段代码的读写集合」，再对照 `options` 是否恰好覆盖——不少 UB 源于把「我读了的内存」漏出承诺集合。

### 测验 1：asm! 宏基本语法（记忆层）

**题目**: 以下 `asm!` 宏（Macro）调用中，哪个是正确的 x86_64 内联汇编（Inline Assembly）？

- A. `asm!("mov rax, {0}", in(reg) 42)`
- B. `unsafe { asm!("mov %rax, $0", in(reg) 42) }`
- C. `unsafe { asm!("mov rax, {val}", val = in(reg) 42) }`
- D. `asm!("mov rax, 42")`

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 C**。

Rust 内联汇编语法规则：

```rust,ignore
unsafe {
    asm!(
        "汇编模板",                    // 汇编指令模板
        named_operand = in(reg) value,  // 命名操作数
        lateout(reg) _                 // 输出/ clobber
    );
}
```

**语法要求**：

| 要求 | 说明 |
|:---|:---|
| `unsafe` 块 | `asm!` 是 unsafe 的（可能破坏内存安全（Memory Safety））|
| 命名操作数 | `{name}` 或 `name = in(reg) value` |
| 寄存器约束 | `in(reg)` / `out(reg)` / `lateout(reg)` |

**选项分析**：

- **A**: 缺少 `unsafe` 块
- **B**: 使用 AT&T 语法 (`%rax`, `$0`)，Rust 默认使用 Intel 语法
- **C**: ✅ 正确。`{val}` 引用（Reference）命名操作数，`in(reg)` 指定输入寄存器
- **D**: 硬编码立即数绕过 Rust 的类型系统（Type System），不安全

**完整示例**：

```rust,ignore
// x86_64: 读取 CPU 时间戳计数器 (RDTSC)
unsafe {
    let lo: u32;
    let hi: u32;
    asm!(
        "rdtsc",
        out("eax") lo,
        out("edx") hi,
    );
    let tsc = ((hi as u64) << 32) | (lo as u64);
}
```

> **注意**: 从 Rust 1.59 开始，`asm!` 是稳定功能（无需每日构建版）。之前需要使用 `llvm_asm!`（已废弃）。
</details>

---

### 测验 2：操作数约束（理解层）

**题目**: `lateout` 与 `out` 有什么区别？以下代码为什么要用 `lateout`？

```rust,ignore
unsafe {
    let mut x: u64 = 1;
    asm!(
        "add {x}, {y}",
        x = inout(reg) x,
        y = in(reg) 2,
    );
}
```

- A. `lateout` 表示输出值会在汇编代码**之后**才写入，允许编译器复用输入寄存器
- B. `lateout` 和 `out` 没有区别，可以互换
- C. `lateout` 表示寄存器在汇编代码**之前**被读取
- D. 应该使用 `inlateout` 替代 `inout`

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 A**。

**操作数约束类型**：

| 约束 | 含义 | 使用场景 |
|:---|:---|:---|
| `in(reg)` | 输入，汇编前写入 | 只读参数 |
| `out(reg)` | 输出，汇编后读取 | 纯输出（汇编前寄存器值不被使用）|
| `inout(reg)` | 输入+输出 | 读取-修改-写入（如计数器递增）|
| `lateout(reg)` | 延迟输出 | 输出值仅在汇编**末尾**写入，允许复用输入寄存器 |
| `inlateout(reg)` | 输入+延迟输出 | 输入被读取，输出在末尾写入 |

**`out` vs `lateout` 的关键区别**：

```rust,ignore
// 场景: x = x + y
unsafe {
    let mut x: u64 = 1;
    asm!(
        "add {x}, {y}",
        x = inlateout(reg) x,   // ✅ x 先作为输入，最后作为输出
        y = in(reg) 2,
    );
    assert_eq!(x, 3);
}

// 如果用 out：
// asm!("add {x}, {y}", x = out(reg) _, y = in(reg) 2);
// ❌ x 在汇编前未初始化，add 读取的是垃圾值！
```

**寄存器复用优化**：

```rust,ignore
// 使用 lateout 允许编译器将输出放入输入寄存器
// 节省一个寄存器！
unsafe {
    let x: u64 = 1;
    let y: u64;
    asm!(
        "mov {y}, {x}",
        x = in(reg) x,
        y = lateout(reg) y,   // y 可能复用 x 的寄存器
    );
}
```

> **选择指南**: 如果汇编代码**不会读取**输出寄存器的旧值 → 用 `out`。如果汇编代码**会读取**旧值 → 用 `inout` 或 `inlateout`。
</details>

---

### 测验 3：用内联汇编实现原子操作（应用层）

**题目**: 在 `no_std` 环境下，如何用 x86_64 内联汇编实现一个原子自增？

```rust,ignore
unsafe fn atomic_inc(ptr: *mut u64) -> u64 {
    let result: u64;
    asm!(
        // 填写汇编代码
        inout("reg") ptr => _,
        out("reg") result,
    );
    result
}
```

- A. `"inc qword ptr [{0}]"` — 直接递增内存
- B. `"lock inc qword ptr [{ptr}]"` — 加 `lock` 前缀的原子递增
- C. `"xadd [{ptr}], {result}"` — 交换并相加
- D. `"lock xadd qword ptr [{ptr}], {result}"` — `lock` + `xadd`

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 D**。

**x86_64 原子操作（Atomic Operations）指令**：

```rust,ignore
unsafe fn atomic_fetch_add(ptr: *mut u64, value: u64) -> u64 {
    let mut old = value;
    asm!(
        "lock xadd qword ptr [{ptr}], {old}",  // 原子交换并相加
        ptr = in(reg) ptr,
        old = inlateout(reg) old,  // 输入=value，输出=旧值
        options(nostack, preserves_flags),
    );
    old  // 返回旧值
}
```

**关键指令解析**：

| 指令 | 作用 | 原子性 |
|:---|:---|:---:|
| `inc [mem]` | 内存值 +1 | ❌ 非原子 |
| `lock inc [mem]` | 原子 +1 | ✅ |
| `xadd [mem], reg` | 交换 `[mem]` 和 `reg`，然后相加 | ❌ 非原子 |
| `lock xadd [mem], reg` | 原子交换-相加 | ✅ |

**为什么需要 `lock` 前缀**：

```asm
; 无 lock：CPU 可能将 inc 拆分为 读-修改-写 三个微操作
; 其他 CPU 可能在"读"和"写"之间修改内存 → 丢失更新

; 有 lock：CPU 锁定内存总线，确保读-修改-写不可中断
lock xadd qword ptr [rdi], rax
```

**与 `AtomicUsize::fetch_add` 的对比**：

```rust,ignore
// Rust 标准库实现（概念上等价）：
std::sync::atomic::AtomicUsize::fetch_add(1, Ordering::SeqCst);

// 底层在 x86_64 上就是：
// lock xadd [ptr], 1
```

> **生产环境**: 永远优先使用 `std::sync::atomic`，不要手写汇编。内联汇编只在 `no_std` + 特殊指令（如 RDTSC、CPUID）时才需要。
</details>

---

### 测验 4：clobber 与内存屏障（分析层）

**题目**: 以下代码没有使用 `options(nomem)`，编译器会做出什么假设？如果加上 `options(nomem)` 会有什么问题？

```rust,ignore
let mut x = 0;
unsafe {
    asm!(
        "mov {tmp}, 1",
        tmp = out(reg) _,
    );
    x = 1;
}
assert_eq!(x, 1);
```

- A. 没有区别，`options(nomem)` 只是优化提示
- B. 不加 `nomem`：编译器假设汇编可能访问内存，不会在汇编前后重排内存操作。加 `nomem`：编译器可能将 `x = 1` 重排到汇编之前！
- C. 必须加 `nomem`，否则编译器会生成错误的代码
- D. `nomem` 表示汇编代码不使用任何寄存器

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

**`asm!` 的 options 控制编译器假设**：

```rust,ignore
unsafe {
    asm!(...,
        options(
            pure,        // 汇编无副作用（同输入总是同输出）
            nomem,       // 汇编不读写内存
            nostack,     // 汇编不修改栈指针
            preserves_flags,  // 汇编不修改标志寄存器
        )
    );
}
```

**不加 `nomem` 时**：

```rust,ignore
let mut x = 0;
unsafe {
    asm!("syscall", ...);  // 编译器假设可能读写内存
    x = 1;  // 不会重排到 syscall 之前
}
```

**加 `nomem` 后的危险**：

```rust,ignore
static mut FLAG: bool = false;
static mut DATA: u64 = 0;

unsafe {
    DATA = 42;
    asm!(
        "mov byte ptr [{flag}], 1",
        flag = in(reg) &mut FLAG,
        options(nomem),  // ❌ 错误：汇编确实访问了内存！
    );
}

// 编译器可能重排：
// asm!()      // FLAG = 1（但 DATA 可能还是 0！）
// DATA = 42   // 被重排到汇编之后
```

**正确的内存屏障使用**：

```rust,ignore
unsafe {
    DATA = 42;
    asm!(
        "sfence",  // 存储屏障
        options(nomem, preserves_flags),
    );
    FLAG = true;  // sfence 保证 DATA=42 在 FLAG=true 之前可见
}
```

| option | 含义 | 不加时的默认 |
|:---|:---|:---|
| `pure` | 无副作用 + 确定性 | 可能有副作用 |
| `nomem` | 不访问内存 | 可能读写任意内存 |
| `nostack` | 不修改栈 | 可能使用栈 |
| `preserves_flags` | 保留 EFLAGS | 可能修改标志位 |

> **关键原则**: 不要过度使用 `options`。只有当**确定**汇编代码满足条件时才添加。错误的 option 会导致编译器优化破坏程序正确性。
</details>

---

> **测验设计来源**: [Bloom Taxonomy 2001] · [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) · [Rust By Example - Assembly](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html)

> **权威来源**: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html), [RFC 2873 — Inline Assembly](https://rust-lang.github.io/rfcs/2873-inline-asm.html), [Rust By Example — Inline Assembly](https://doc.rust-lang.org/rust-by-example/unsafe/asm.html)
>
> **权威来源对齐变更日志**: 2026-07-10 Stage F L3 补全权威来源块与关键引用 [Authority Source Sprint Batch 10](../../00_meta/02_sources/05_international_authority_index.md)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/libc — 生态权威 API 文档](https://docs.rs/libc) · [docs.rs/nix — 生态权威 API 文档](https://docs.rs/nix)

## ⚠️ 反例与陷阱

本节以无效寄存器约束名为反例，展示 `asm!` 在编译期校验目标架构寄存器与约束字符串。

### 反例：不存在的寄存器约束（rustc 1.97.0 实测）

```rust,compile_fail
use std::arch::asm;
fn main() {
    let mut x: u64 = 0;
    unsafe { asm!("mov {}, 1", out("not_a_register") x); } // ❌ 非法寄存器名
    println!("{}", x);
}
```

**错误**：`error: invalid register not_a_register: unknown register`——寄存器与约束在编译期对照目标架构校验。

### ✅ 修正：使用合法寄存器或类别约束

```rust,ignore
use std::arch::asm;
fn main() {
    let mut x: u64;
    unsafe { asm!("mov {}, 1", out(reg) x); } // 编译器分配通用寄存器
    println!("{}", x);
}
```
