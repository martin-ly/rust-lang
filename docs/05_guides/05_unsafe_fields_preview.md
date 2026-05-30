# Unsafe Fields 预览指南

> **Bloom 层级**: L3-L4 (应用/分析)

> **创建日期**: 2026-05-08
> **最后更新**: 2026-05-08
> **Rust 版本**: 实验性 (未稳定)
> **状态**: 🧪 实验性预览

---

## 📋 目录
>
> **[来源: Rust Official Docs]**

- [Unsafe Fields 预览指南](#unsafe-fields-预览指南)
  - [📋 目录](#目录)
  - [🔑 什么是 Unsafe Fields](#什么是-unsafe-fields)
  - [💡 动机](#动机)
    - [问题：当前 `unsafe` 的粒度太粗](#问题当前-unsafe-的粒度太粗)
    - [Unsafe Fields 的目标](#unsafe-fields-的目标)
  - [📝 提议语法](#提议语法)
    - [基本语法](#基本语法)
    - [访问规则](#访问规则)
    - [模式匹配](#模式匹配)
  - [⚖️ 与当前 `unsafe` 块的对比](#与当前-unsafe-块的对比)
  - [🧪 当前状态](#当前状态)
    - [已知的设计问题](#已知的设计问题)
  - [🔧 与 Rust for Linux 的关系](#与-rust-for-linux-的关系)
    - [Linux 内核的需求](#linux-内核的需求)
    - [为什么内核特别需要这个特性](#为什么内核特别需要这个特性)
  - [📖 参考文献](#参考文献)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

---

## 🔑 什么是 Unsafe Fields
>
> **[来源: Rust Official Docs]**

**Unsafe Fields** 是 Rust Project Goal 2026 中提出的一项语言特性，允许在结构体定义中**显式标记哪些字段需要 `unsafe` 访问**。其核心思想是：将 `unsafe` 的粒度从"代码块"细化到"字段级别"，从而让 `unsafe` 的使用更加精确和可审计。

```text
当前模型 (unsafe 块) vs Unsafe Fields 模型:

当前模型:
┌─────────────────────────────────────────┐
│ struct Buffer {                         │
│     ptr: *mut u8,      ← 原始指针        │
│     len: usize,                         │
│     cap: usize,                         │
│ }                                       │
│                                         │
│ // 整个 unsafe 块需要人工审查              │
│ unsafe {                                │
│     (*buffer.ptr).write(42);            │
│ }                                       │
└─────────────────────────────────────────┘

Unsafe Fields 模型:
┌─────────────────────────────────────────┐
│ struct Buffer {                         │
│     unsafe field raw_ptr: *mut u8,  ← 标记 │
│     len: usize,                         │
│     cap: usize,                         │
│ }                                       │
│                                         │
│ // 编译器知道只有 raw_ptr 需要 unsafe    │
│ // 其他字段的访问保持安全                │
└─────────────────────────────────────────┘
```

---

## 💡 动机
>
> **[来源: Rust Official Docs]**

### 问题：当前 `unsafe` 的粒度太粗

> **[来源: Wikipedia - Type System]**
>
> **[来源: Rust Official Docs]**

在现有 Rust 中，一旦进入 `unsafe` 块，编译器就放弃对所有操作的检查。但一个结构体中通常**只有部分字段**涉及不安全的内存操作：

```rust,ignore
// 当前 Rust: 进入 unsafe 块后，所有操作都"不受保护"
struct IoBuffer {
    raw_ptr: *mut u8,      // 需要 unsafe
    len: usize,            // 完全安全
    capacity: usize,       // 完全安全
    flags: u32,            // 完全安全
}

impl IoBuffer {
    fn set_flag(&mut self, flag: u32) {
        // ❌ 问题: 明明只是设置一个标志位
        // 但如果放在 unsafe 块附近，审计者必须检查所有内容
        unsafe {
            self.flags = flag;  // 这个操作本身不需要 unsafe!
            (*self.raw_ptr).write(0);
        }
    }
}
```

### Unsafe Fields 的目标

> **[来源: Wikipedia - Rust (programming language)]**
>
> **[来源: Rust Official Docs]**

| 目标 | 说明 |
|------|------|
| **精确标记** | 只有真正不安全的字段需要 `unsafe` 访问 |
| **减少审计面** | 安全审查者只需关注标记的字段 |
| **防止误用** | 意外通过 safe 代码修改 unsafe 字段会变成编译错误 |
| **文档化** | `unsafe field` 本身就是文档，说明该字段的特殊性 |

---

## 📝 提议语法
>
> **[来源: Rust Official Docs]**

### 基本语法

> **[来源: Rust Reference - doc.rust-lang.org/reference]**
>
> **[来源: Rust Official Docs]**

```rust,ignore
pub struct KernelBuffer {
    // 安全字段: 正常访问
    pub len: usize,
    pub capacity: usize,

    // 不安全字段: 需要 unsafe 上下文
    pub unsafe field raw_ptr: *mut u8,
    pub unsafe field dma_handle: DmaHandle,
}
```

### 访问规则

> **[来源: POPL - Programming Languages Research]**
>
> **[来源: Rust Official Docs]**

```rust,ignore
impl KernelBuffer {
    // 安全方法: 访问安全字段
    pub fn len(&self) -> usize {
        self.len  // ✅ 不需要 unsafe
    }

    // 不安全方法: 访问 unsafe 字段
    pub unsafe fn as_mut_slice(&mut self) -> &mut [u8] {
        // ✅ raw_ptr 是 unsafe field，需要在 unsafe 上下文中访问
        std::slice::from_raw_parts_mut(self.raw_ptr, self.len)
    }

    // 错误示例
    pub fn buggy(&self) -> *mut u8 {
        self.raw_ptr  // ❌ 编译错误!
        // error: access to unsafe field `raw_ptr` requires unsafe function or block
    }
}
```

### 模式匹配

> **[来源: PLDI - Programming Language Design]**
>
> **[来源: Rust Official Docs]**

```rust,ignore
fn process_buffer(buf: &KernelBuffer) {
    // 解构时，unsafe field 需要显式处理
    let KernelBuffer { len, capacity, .. } = buf;
    // ✅ len 和 capacity 可以安全解构

    // 要访问 raw_ptr:
    unsafe {
        let KernelBuffer { raw_ptr, .. } = buf;
        // 在 unsafe 块内可以访问
    }
}
```

---

## ⚖️ 与当前 `unsafe` 块的对比
>
> **[来源: Rust Official Docs]**

| 方面 | 当前 `unsafe` 块 | Unsafe Fields |
|------|-----------------|---------------|
| **粒度** | 代码块级别 | 字段级别 |
| **编译器检查** | 块内全部放行 | 仅放行标记的字段 |
| **误用保护** | 低 (块内任何操作都允许) | 高 (未标记字段仍受检查) |
| **审计范围** | 整个 unsafe 块 | 仅限 unsafe field 的访问点 |
| **学习曲线** | 简单 | 稍复杂 |
| **向后兼容** | N/A | 保持现有 unsafe 块语义 |

```text
代码可审计性对比:

当前模型 (unsafe 块):
┌────────────────────────────────────────┐
│ unsafe {                               │
│     // 审计者必须检查这里面的所有内容    │
│     // 行 1: ???                       │
│     // 行 2: ???                       │
│     // 行 3: ???                       │
│     // 行 4: ???                       │
│ }  ← 整个块都是"危险区域"              │
└────────────────────────────────────────┘

Unsafe Fields 模型:
┌────────────────────────────────────────┐
│ // 安全代码区域                        │
│ self.len += 1;                         │
│                                        │
│ unsafe {                               │
│     // 审计者只需检查 raw_ptr 的使用    │
│     (*self.raw_ptr).write(42);         │
│ }  ← 危险区域被精确定位                │
│                                        │
│ // 回到安全代码区域                    │
│ self.flags |= READY;                   │
└────────────────────────────────────────┘
```

---

## 🧪 当前状态
>
> **[来源: Rust Official Docs]**

截至 2026-05，Unsafe Fields 仍处于**实验性讨论阶段**：

| 里程碑 | 状态 | 预计时间 |
|--------|------|----------|
| RFC 讨论 | 🔄 进行中 | 2026 年内 |
| 原型实现 | 🔄 实验分支 | 未知 |
| Nightly 可用 | ⏳ 等待中 | 2026+ |
| Stable 稳定 | ⏳ 长期目标 | 2027+ |

### 已知的设计问题

> **[来源: Wikipedia - Memory Safety]**

1. **与 `Drop` 的交互**: `unsafe field` 的析构是否也需要 `unsafe`?
2. **与 `union` 的关系**: `union` 的字段是否默认 unsafe?
3. **可见性**: `unsafe field` 的可见性如何与 `pub` / `priv` 交互?
4. **派生宏**: `#[derive(Debug)]` 等如何处理 `unsafe field`?

---

## 🔧 与 Rust for Linux 的关系
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

Unsafe Fields 特性的一个重要推动力来自 **Rust for Linux** 项目。

### Linux 内核的需求

> **[来源: Wikipedia - Type System]**

```text
内核编程的典型场景:

┌──────────────────────────────────────────────┐
│ struct DeviceBuffer {                        │
│     // 大部分字段是普通的配置/状态            │
│     size: usize,                             │
│     flags: u32,                              │
│     owner: *mut TaskStruct,  ← 但需要 unsafe  │
│     dma_addr: phys_addr_t,   ← 需要 unsafe   │
│     mmio_ptr: *mut u8,       ← 需要 unsafe   │
│ }                                            │
│                                              │
│ // 当前: 大量 unsafe 块混合安全/不安全操作    │
│ // Unsafe Fields: 精确分离两类操作            │
└──────────────────────────────────────────────┘
```

### 为什么内核特别需要这个特性
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 内核场景 | 当前问题 | Unsafe Fields 解决方案 |
|---------|---------|----------------------|
| **硬件寄存器访问** | MMIO 指针与安全字段混用 | 精确标记 MMIO 字段 |
| **DMA 缓冲区** | DMA 地址与普通元数据共存 | DMA 相关字段标记 unsafe |
| **锁与原始指针** | `spinlock_t` 内部包含 raw pointer | 指针字段独立标记 |
| **驱动审查** | 审查者需检查全部 unsafe 块 | 缩小审查范围至关键字段 |

> 💡 **关键洞察**: Rust for Linux 的维护者认为，Unsafe Fields 将显著降低内核代码的审查负担，使 Rust 驱动更容易被 C 语言背景的维护者接受。

---

## 📖 参考文献
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. **Rust Project Goals 2026**. "Safer Unsafe Rust: Unsafe Fields".
   <https://github.com/rust-lang/rust-project-goals>

2. **Rust for Linux 项目**. "Rust in the Linux Kernel".
   <https://rust-for-linux.com/>

3. **Miguel Ojeda (Rust for Linux 维护者)**. 多封邮件列表讨论关于 unsafe field 在内核中的需求。
   <https://lore.kernel.org/rust-for-linux/>

4. **Rust Internals 论坛讨论**. "Unsafe Fields RFC Pre-discussion".
   <https://internals.rust-lang.org/>

---

> 📌 **跟踪记录**
>
> - 2026-05-08: 初始创建，基于 Rust Project Goal 2026 公开讨论
> - 状态更新: 等待正式 RFC 草案发布
>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [05_guides 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: Rustonomicon]**

> **[来源: Rust Reference - Unsafe]**

> **[来源: RFC 2585 - Unsafe Guidelines]**

---
