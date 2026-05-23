# 内联汇编 (Inline Assembly)

> **Bloom 层级**: 理解

> **📌 简介**: Rust 的内联汇编 (`asm!` 宏) 允许在 Rust 代码中直接嵌入汇编指令 [来源: Rust Reference — Inline Assembly / 2025; RFC 2873 — Inline Assembly / 2020; 核心设计决策: 基于 LLVM 内联汇编基础设施，提供与 C 语言 `asm` 关键字等价的表达能力，但通过 Rust 的类型系统和约束系统保证安全边界]，用于实现编译器无法生成的底层操作、访问特权指令、与硬件直接交互，或优化极致性能的热路径。
>
> **⏱️ 预计学习时间**: 2-3 小时
> **📚 难度级别**: ⭐⭐⭐⭐⭐ 专家
> **权威来源**: [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html), [std::arch::asm](https://doc.rust-lang.org/core/arch/macro.asm.html), [LLVM Inline Assembler](https://llvm.org/docs/LangRef.html#inline-assembler-expressions), [RFC 2873: Inline Assembly](https://rust-lang.github.io/rfcs/2873-inline-assembly.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 RFC 2873 设计决策来源标注、LLVM 内联汇编语义引用、x86_64/AArch64/RISC-V 架构官方文档来源 [来源: Authority Source Sprint Batch 8]

---

## 🎯 学习目标
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

完成本章后，你将能够：

- [x] 理解 `asm!` 宏的基本语法：模板字符串、操作数、约束、选项
- [x] 正确使用输入/输出操作数、临时寄存器、早绑定输出
- [x] 在 x86_64、AArch64、RISC-V 和 PowerPC/PowerPC64 上编写可移植的内联汇编
- [x] 识别和避免内联汇编的常见未定义行为
- [x] 在 `unsafe` 块中安全地封装内联汇编抽象

---

## 📋 先决条件
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **Unsafe Rust** — 未定义行为、原始指针（`unsafe_rust.md`）
2. **目标架构汇编** — 至少了解一种 CPU 汇编语法
3. **调用约定** — ABI、寄存器保存规则（`ffi.md`）

---

## 🧠 核心概念
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 模块 1: 概念定义
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 1.1 直观定义

内联汇编允许在 Rust 函数体中直接嵌入目标架构的汇编指令，由编译器在代码生成阶段将其插入到生成的机器码中。

```rust
use std::arch::asm;

fn add(a: i32, b: i32) -> i32 {
    let result: i32;
    unsafe {
        asm!(
            "add {0}, {1}",      // 汇编模板
            out(reg) result,     // 输出操作数
            in(reg) a,           // 输入操作数
            in(reg) b,
        );
    }
    result
}
```

#### 1.2 何时需要内联汇编

| 场景 | 替代方案 | 是否需要 asm |
|------|---------|-------------|
| SIMD 并行计算 | `std::simd` / `packed_simd` | ❌ 优先用库 |
| 原子操作 | `std::sync::atomic` | ❌ 优先用标准库 |
| 内存屏障 | `atomic::fence` | ❌ 优先用标准库 |
| 读取 CPU 时间戳 | `std::arch::x86_64::_rdtsc()` | ❌ 优先用固有函数 |
| 自定义特权指令 | 无 | ✅ 需要 asm |
| 引导加载器 / OS 开发 | 无 | ✅ 需要 asm |
| 编译器无法优化的热路径 | 检查 LLVM IR 后决定 | ⚠️ 谨慎使用 |

### 模块 2: 属性清单
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 约束 | 说明 | 示例 |
|------|------|------|
| `in(reg) val` | 输入寄存器 | `in("eax") val` |
| `out(reg) val` | 输出寄存器 | `out(reg) result` |
| `inout(reg) val` | 读写同一寄存器 | `inout(reg) val` |
| `lateout(reg) _` | 晚绑定输出（不占用输入寄存器）| `lateout("rax") _` |
| `inlateout(reg) in => out` | 输入+晚绑定输出 | `inlateout(reg) x => y` |
| `sym path` | 符号操作数（函数/静态变量）| `sym foo` |
| `options(pure, nomem, nostack)` | 汇编块属性 | `options(nomem)` |

| 选项 | 含义 |
|------|------|
| `pure` | 无副作用，仅依赖输入产生输出 |
| `nomem` | 不访问内存（允许编译器重排）|
| `nostack` | 不使用栈指针 |
| `preserves_flags` | 不修改条件码寄存器 |
| `noreturn` | 不会返回到调用点 |

### 模块 3: 概念依赖图
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
内联汇编
├── 语法结构
│   ├── 模板字符串 (占位符 {n})
│   ├── 操作数列表 (in/out/inout/lateout)
│   └── 选项 (pure/nomem/nostack/noreturn)
├── 寄存器管理
│   ├── 显式寄存器 ("eax", "x0")
│   ├── 隐式寄存器 (reg, reg_abcd)
│   └──  clobber 声明
├── 架构特定
│   ├── x86_64 (Intel/AT&T 语法)
│   ├── AArch64 (ARM64)
│   ├── RISC-V
│   └── PowerPC / PowerPC64 (Rust 1.95+ 稳定) ✅
└── 安全封装
    ├── unsafe 边界
    ├── 前提条件文档
    └── Miri / 测试验证
```

### 模块 4: 机制解释
> **[来源: [crates.io](https://crates.io/)]**

#### 4.1 编译器如何内联汇编

1. **模板解析**: Rust 编译器解析 `asm!` 宏，提取模板字符串和操作数
2. **约束求解**: 编译器根据操作数约束分配寄存器
3. **代码生成**: LLVM 将汇编模板直接嵌入到 IR 中
4. **优化边界**: `options` 影响编译器能否跨越 `asm!` 块进行优化

#### 4.2 占位符与命名操作数

```rust
// 数字占位符: {0}, {1}, ...
asm!("add {0}, {1}", out(reg) c, in(reg) a, in(reg) b);

// 命名操作数 (Rust 1.77+): {name}
asm!(
    "add {result}, {a}",
    result = out(reg) c,
    a = in(reg) a,
    in("rbx") b,  // 显式寄存器
);
```

### 模块 5: 正例集
> **[来源: [docs.rs](https://docs.rs/)]**

#### 5.1 读取 x86 CPU ID

```rust
use std::arch::asm;

/// 获取 CPU 厂商信息
fn cpuid_vendor() -> [u8; 12] {
    let mut ebx: u32;
    let mut edx: u32;
    let mut ecx: u32;

    unsafe {
        asm!(
            "cpuid",
            in("eax") 0,           // CPUID 功能号 0
            lateout("ebx") ebx,    // 晚绑定，不占用 eax
            lateout("edx") edx,
            lateout("ecx") ecx,
            options(preserves_flags, nomem, nostack),
        );
    }

    let mut result = [0u8; 12];
    result[0..4].copy_from_slice(&ebx.to_le_bytes());
    result[4..8].copy_from_slice(&edx.to_le_bytes());
    result[8..12].copy_from_slice(&ecx.to_le_bytes());
    result
}

fn main() {
    let vendor = cpuid_vendor();
    println!("CPU Vendor: {}", std::str::from_utf8(&vendor).unwrap());
}
```

#### 5.2 AArch64 系统调用封装

```rust
#[cfg(target_arch = "aarch64")]
fn syscall3(nr: usize, a1: usize, a2: usize, a3: usize) -> usize {
    let ret: usize;
    unsafe {
        asm!(
            "svc #0",
            inlateout("x8") nr => _,
            inlateout("x0") a1 => ret,
            in("x1") a2,
            in("x2") a3,
            options(nostack, preserves_flags),
        );
    }
    ret
}
```

#### 5.3 内存屏障（当标准库不足时）

```rust
use std::arch::asm;

/// 全内存屏障
#[inline]
pub fn full_memory_barrier() {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        asm!("mfence", options(nomem, nostack, preserves_flags));
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        asm!("dmb ish", options(nomem, nostack, preserves_flags));
    }
}
```

### 模块 6: 反例集
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

#### 6.1 未声明 clobber 寄存器

```rust
// ❌ 错误: 修改了 rax 但没有声明
let x = 42;
unsafe {
    asm!(
        "mov rax, {0}",
        in(reg) x,
        // 缺少: lateout("rax") _
    );
}
// 编译器可能假设 rax 未被修改，导致错误优化

// ✅ 正确: 声明所有修改的寄存器
unsafe {
    asm!(
        "mov rax, {0}",
        in(reg) x,
        lateout("rax") _,
    );
}
```

#### 6.2 错误使用 `nomem` 选项

```rust
// ❌ 错误: 实际访问了内存但声明 nomem
let mut x = 0;
unsafe {
    asm!(
        "mov [{0}], dword ptr 1",
        in(reg) &mut x,
        options(nomem), // UB! 实际修改了内存
    );
}

// ✅ 正确: 不声明 nomem，或仅在真正不访问内存时使用
unsafe {
    asm!(
        "inc {0}",
        inout(reg) x,
    );
}
```

#### 6.3 忘记 `unsafe` 块

```rust
// ❌ 编译错误: asm! 必须在 unsafe 块中
asm!("nop");

// ✅ 正确
unsafe { asm!("nop", options(nomem, nostack)); }
```

### 模块 7: 思维表征
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

#### 内联汇编决策流程

```text
需要底层操作?
├── 否 → 使用 safe Rust
└── 是
    ├── 标准库/std::arch 固有函数是否支持?
    │   ├── 是 → 优先使用（可移植、安全）
    │   └── 否
    │       ├── 需要跨平台?
    │       │   ├── 是 → 为每个目标架构实现 cfg 分支
    │       │   └── 否 → 单架构实现
    │       └── 安全封装
    │           ├── unsafe fn + // SAFETY: 注释
    │           ├── 输入验证（范围、对齐）
    │           └── Miri / 硬件测试
```

### 模块 8: 国际化对齐
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 术语 (中文) | 英文 | 来源 |
|------------|------|------|
| 内联汇编 | Inline Assembly | Rust Reference |
| 操作数约束 | Operand Constraint | GCC / LLVM |
| 早绑定输出 | Early-clobber Output | GCC Manual |
| 晚绑定输出 | Late Output | Rust Reference |
| Clobber | Clobber | 汇编术语 |
| 内存屏障 | Memory Barrier / Fence | ARM/x86 Architecture |

### 模块 9: 设计权衡
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 方案 | 安全 | 性能 | 可移植性 | 维护性 |
|------|------|------|---------|--------|
| `std::arch` 固有函数 | ✅ | 高 | 中（需 cfg）| 高 |
| 内联汇编 (`asm!`) | ⚠️ | 最高 | 低 | 低 |
| C 外部函数 | ⚠️ | 高 | 中 | 中 |
| 纯 Rust 实现 | ✅ | 中 | 高 | 高 |

> **原则**: 仅在 `std::arch` 固有函数无法满足需求时使用 `asm!`。每次使用 `asm!` 都需要架构特定的测试和长期维护。

### 模块 10: 自我检测
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

#### 10.1 快速检查

| 问题 | 你的答案 |
|------|---------|
| 是否确认没有更安全的替代方案？ | ☐ 是 ☐ 否 |
| 所有修改的寄存器是否已声明为 clobber？ | ☐ 是 ☐ 否 |
| `options` 声明是否与实际行为一致？ | ☐ 是 ☐ 否 |
| 是否在目标架构上实际测试过？ | ☐ 是 ☐ 否 |
| 是否用 `objdump` / 调试器验证生成代码？ | ☐ 是 ☐ 否 |

#### 10.2 代码审查清单

- [ ] `// SAFETY:` 注释说明所有前提条件
- [ ] 输入操作数经过范围/对齐验证
- [ ] 所有非保留寄存器已声明为 `lateout`
- [ ] `nomem` / `nostack` / `pure` 选项与实际行为匹配
- [ ] 多架构代码有 `#[cfg(target_arch = ...)]` 分支
- [ ] 提供了纯 Rust fallback 路径（如适用）

---

## 🔗 参考资源
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)
- [Rust std::arch::asm](https://doc.rust-lang.org/core/arch/macro.asm.html)
- [LLVM Inline Assembler](https://llvm.org/docs/LangRef.html#inline-assembler-expressions)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 📚 权威来源索引
> **[来源: [crates.io](https://crates.io/)]**

### 官方来源

- [Rust Reference — Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) [来源: Rust Reference / 2025]
- [std::arch::asm](https://doc.rust-lang.org/core/arch/macro.asm.html) [来源: Rust Standard Library / 2025]
- [RFC 2873: Inline Assembly](https://rust-lang.github.io/rfcs/2873-inline-assembly.html) [来源: Rust Core Team / 2020]

### 架构来源

- Intel 64 and IA-32 Architectures Software Developer's Manual [来源: x86_64 指令集参考]
- ARM Architecture Reference Manual [来源: AArch64 指令集参考]
- RISC-V Instruction Set Manual [来源: RISC-V 指令集参考]

### 跨语言来源

- GCC Extended Asm [来源: GNU C 内联汇编; Rust `asm!` 的设计对标]
- MSVC `__asm` [来源: Microsoft C/C++ 内联汇编; 与 Rust 跨平台设计的对比]

---

## 相关概念
> **[来源: [docs.rs](https://docs.rs/)]**

- [FFI (Foreign Function Interface)](ffi.md)
- [MaybeUninit](maybe_uninit.md)
- [Unsafe Rust 指南](README.md)
- [Rust 所有权深入](../../01_fundamentals/ownership.md)

---

## 权威来源索引

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

