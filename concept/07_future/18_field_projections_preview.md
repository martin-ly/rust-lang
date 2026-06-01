# Field Projections 预览：安全的字段级投影
>
> **受众**: [专家]
> **内容分级**: [实验级]

> **Bloom 层级**: L4 (分析)
> **A/S/P 标记**: **S** — Structure
> **定位**: 探讨 Rust 中 field projections 的提案——允许安全地从复合类型中"投影"出对字段的引用，而不暴露内部结构。分析其对内核编程、自引用结构和内存安全保证的影响。
> **前置概念**: [Pin](../03_advanced/06_pin_unpin.md) · [Lifetime](../01_foundation/03_lifetimes.md) · [Unsafe Rust](../03_advanced/03_unsafe.md)

---

## 📑 目录

- [Field Projections 预览：安全的字段级投影](#field-projections-预览安全的字段级投影)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 问题背景](#11-问题背景)
    - [1.2 Field Projections 提案](#12-field-projections-提案)
  - [二、技术细节](#二技术细节)
    - [2.1 投影类型系统](#21-投影类型系统)
    - [2.2 与 `Pin` 的协同](#22-与-pin-的协同)
  - [三、使用场景](#三使用场景)
    - [场景 1：MMIO 寄存器访问（嵌入式/内核）](#场景-1mmio-寄存器访问嵌入式内核)
    - [场景 2：安全地自引用结构](#场景-2安全地自引用结构)
    - [场景 3：零拷贝反序列化](#场景-3零拷贝反序列化)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 与 `offset_of!` 的关系](#41-与-offset_of-的关系)
    - [4.2 设计挑战](#42-设计挑战)
  - [五、演进路线](#五演进路线)
    - [相关已稳定特性](#相关已稳定特性)
  - [参考](#参考)
    - [补充定理链](#补充定理链)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

## 一、核心概念
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/expressions/field-access-expr.html)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 1.1 问题背景

当前 Rust 中，从结构体中获取字段引用是 trivial 的：

```rust
struct Packet {
    header: u32,
    payload: [u8; 1024],
}

let p = Packet { header: 0x1234, payload: [0; 1024] };
let h = &p.header; // ✅ 简单
```

但在某些场景中，我们需要**在不拥有完整结构体的情况下**获取字段引用：

- **内核驱动**: 从已知基地址的原始内存映射中读取字段
- **序列化/反序列化**: 在不构造完整对象的情况下访问字段偏移
- **自引用结构**: 安全地表达"结构体包含指向自身的指针"

### 1.2 Field Projections 提案
>
> **[来源: [Rust Internals Forum](https://internals.rust-lang.org/)]**
>
> **[来源: [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)]**

Field projections 允许编译器生成**安全的字段访问投影**，提供以下保证：

1. **生命周期保证**: 投影出的引用生命周期不超过父对象
2. **对齐保证**: 字段访问始终对齐
3. **不变性保证**: 只读/只写/读写权限精确控制

```rust,ignore
#![feature(field_projection)]

struct DeviceRegs {
    status: u32,
    control: u32,
    data: [u32; 8],
}

// 从已知基地址安全投影字段
let base: *mut DeviceRegs = MMIO_BASE as *mut _;
let status: &u32 = base.project::<DeviceRegs, _>(|d| &d.status); // 安全投影
```

---

## 二、技术细节
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/types.html)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 2.1 投影类型系统

```rust,ignore
// 投影 trait（概念性）
trait FieldProjection<Parent, Field> {
    fn project(parent: &Parent) -> &Field;
    fn project_mut(parent: &mut Parent) -> &mut Field;
}

// 编译器为每个字段自动生成 impl
impl FieldProjection<DeviceRegs, u32> for DeviceRegs {
    fn project(parent: &DeviceRegs) -> &u32 { &parent.status }
    fn project_mut(parent: &mut DeviceRegs) -> &mut u32 { &mut parent.status }
}
```

### 2.2 与 `Pin` 的协同

Field projections 可与 `Pin` 结合，实现**安全的自引用结构**初始化：

```rust,ignore
struct SelfRef {
    buffer: [u8; 1024],
    // 当前：需要 unsafe 和手动指针计算
    ptr: *const [u8],
}

// field projections 后：
struct SelfRef {
    buffer: [u8; 1024],
    // 编译器验证 ptr 始终指向 buffer
    ptr: Projected<&[u8], field=buffer>,
}
```

---

## 三、使用场景
>
> **[来源: [Rust Embedded Working Group](https://github.com/rust-embedded/wg)]**
>
> **[来源: [Rust for Linux](https://rust-for-linux.com/)]**

### 场景 1：MMIO 寄存器访问（嵌入式/内核）

```rust,ignore
struct UartRegs {
    tx: u32,
    rx: u32,
    status: u32,
}

impl UartRegs {
    // 当前方式：需要 unsafe + 手动偏移计算
    unsafe fn tx_ptr(base: *mut Self) -> *mut u32 {
        base.add(0) as *mut u32
    }

    // field projections 后：编译器验证偏移和对齐
    fn tx(base: *mut Self) -> &mut u32 {
        base.project_mut(|r| &mut r.tx)
    }
}
```

### 场景 2：安全地自引用结构

```rust,ignore
struct Parser {
    input: String,
    // 当前：Pin + unsafe 手动投影
    current: *const str,
}

// field projections 后：
struct Parser {
    input: String,
    current: Projected<&str, field=input>, // 编译器验证生命周期
}

impl Parser {
    fn new(input: String) -> Self {
        Parser {
            input,
            current: project!(input.as_str()), // 安全初始化
        }
    }
}
```

### 场景 3：零拷贝反序列化

```rust,ignore
#[repr(C)]
struct Packet {
    version: u16,
    len: u16,
    data: [u8; 0], // 柔性数组
}

// 直接从字节切片投影字段，无需复制
fn parse_packet(bytes: &[u8]) -> Option<&Packet> {
    if bytes.len() < 4 { return None; }
    let p = bytes.project::<Packet>()?;
    Some(p)
}
```

---

## 四、反命题与边界分析
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/types/struct.html)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/mem/macro.offset_of.html)]**

### 4.1 与 `offset_of!` 的关系

```rust,ignore
// 当前：offset_of! 宏（1.77+ stable）
use std::mem::offset_of;
let tx_offset = offset_of!(UartRegs, tx); // 编译期常量

// field projections 是 offset_of! 的运行时安全扩展
```

| 特性 | `offset_of!` | Field Projections |
|------|-------------|-------------------|
| 时机 | 编译期 | 运行时/编译期 |
| 安全性 | 纯计算，无 unsafe | 安全抽象 |
| 用途 | 布局检查、手动指针计算 | 直接安全访问 |
| 稳定状态 | **1.77+ stable** | 实验中 |

### 4.2 设计挑战

1. **未初始化字段**: 投影到未初始化字段是 UB，需要类型系统跟踪初始化状态
2. **packed 结构体**: `#[repr(packed)]` 字段可能未对齐，投影需要额外检查
3. **动态大小类型 (DST)**: 柔性数组字段的投影边界

---

## 五、演进路线

| 阶段 | 状态 | 预计 |
|------|------|------|
| RFC 讨论 | 早期 | 2026-2027 |
| Nightly 原型 | 无 | — |
| 稳定化 | 远未开始 | 2028+ |

### 相关已稳定特性

- `offset_of!` 宏（1.77+）: 编译期字段偏移计算
- `addr_of!` / `addr_of_mut!`（1.51+）: 安全获取字段裸指针

---

## 参考

> **[来源: Rust Project Goals 2026 — Rust for Linux]**
> **[来源: Rust Internals — Field Projections Discussion]**

| 资源 | 链接 |
|------|-----|
| `offset_of!` 文档 | <https://doc.rust-lang.org/std/mem/macro.offset_of.html> |
| Pin 投影模式 | <https://doc.rust-lang.org/std/pin/index.html#pin-projection> |
| Rust for Linux 需求 | <https://rust-lang.github.io/rust-project-goals/2026/> |

> **过渡**: Field Projections 预览：安全的字段级投影 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Field Projections 预览：安全的字段级投影 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Field Projections 预览：安全的字段级投影 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Field Projections 预览：安全的字段级投影 定义 ⟹ 类型安全保证
- **定理**: Field Projections 预览：安全的字段级投影 定义 ⟹ 类型安全保证
- **定理**: Field Projections 预览：安全的字段级投影 定义 ⟹ 类型安全保证

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Field Projections 预览：安全的字段级投影** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Field Projections 预览：安全的字段级投影 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Field Projections 预览：安全的字段级投影 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Field Projections 预览：安全的字段级投影 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Field Projections 预览：安全的字段级投影 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。

> **过渡**: 在工程实践中应用 Field Projections 预览：安全的字段级投影 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。

> **过渡**: Field Projections 预览：安全的字段级投影 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Field Projections 预览：安全的字段级投影 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
