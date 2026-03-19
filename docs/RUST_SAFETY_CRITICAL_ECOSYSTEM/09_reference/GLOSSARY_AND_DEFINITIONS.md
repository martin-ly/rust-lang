# Rust安全关键系统 - 术语表与定义

## A

**AdaCore GNAT Pro for Rust**
AdaCore公司提供的Rust工具链，集成到GCC生态系统中，支持Ada/Rust互操作和SPARK形式化验证。

**ASIL (Automotive Safety Integrity Level)**
汽车安全完整性等级，ISO 26262标准定义，从ASIL A到ASIL D，D为最高等级。

**所有权 (Ownership)**
Rust核心概念，每个值有且仅有一个所有者，所有者离开作用域时值被释放。

## B

**借用 (Borrowing)**
Rust中通过引用临时访问数据而不获取所有权，分为不可变借用(&T)和可变借用(&mut T)。

**借用检查器 (Borrow Checker)**
Rust编译器组件，在编译时验证借用规则，防止数据竞争和use-after-free。

**BitC**
Rust编译器内部表示，用于代码生成优化。

## C

**Cargo**
Rust的构建系统和包管理器，处理依赖、构建、测试和发布。

**认证工具链 (Certified Toolchain)**
通过功能安全标准（如ISO 26262）认证的编译器工具链，如Ferrocene。

**core库**
Rust标准库的子集，可在无操作系统环境（#![no_std]）中使用。

**CSP (CubeSat Space Protocol)**
CubeSat使用的网络协议，有Rust实现版本。

## D

**DAL (Development Assurance Level)**
DO-178C标准中的开发保证等级，从DAL A（最高）到DAL E（最低）。

**死代码 (Dead Code)**
永远不会执行的代码，Rust编译器通过lint检测并警告。

**Drop trait**
Rust中定义资源释放行为的trait，实现RAII模式。

## E

**嵌入式Rust (Embedded Rust)**
在裸机或RTOS环境中使用Rust，通常使用#![no_std]。

**嵌入式HAL (embedded-hal)**
硬件抽象层trait集合，用于编写跨平台的嵌入式驱动。

**Edition**
Rust语言的版本（如2015、2018、2021、2024），定义语法和特性。

**FFI (Foreign Function Interface)**
与其他语言（主要是C）交互的接口。

## F

**Ferrocene**
Ferrous Systems提供的认证Rust工具链，通过TÜV SÜD认证，支持ASIL D/SIL 4。

**FLS (Ferrocene Language Specification)**
Ferrocene的Rust语言规范文档，用于认证。

**形式化验证 (Formal Verification)**
使用数学方法证明程序正确性，工具包括Kani、Verus、Miri。

**功能安全 (Functional Safety)**
系统在故障条件下保持安全的能力，标准包括ISO 26262、IEC 61508。

**FSC (Functional Safety Certified)**
功能安全认证工程师资格。

## G

**GC (Garbage Collection)**
垃圾回收，Rust不使用GC，使用所有权系统管理内存。

**泛型 (Generics)**
参数化类型，允许编写适用于多种类型的代码。

## H

**HAL (Hardware Abstraction Layer)**
硬件抽象层，提供统一的硬件访问接口。

**High Assurance Rust**
基于MISRA C的安全Rust编码指南。

**生命周期 (Lifetime)**
Rust中引用有效的作用域范围，编译时验证。

## I

**IEC 61508**
工业领域功能安全国际标准，定义SIL等级。

**IEC 62304**
医疗设备软件生命周期国际标准。

**unsafe Rust**
Rust中用于底层操作的代码块，绕过编译器安全检查，需人工验证。

**ISO 26262**
汽车领域功能安全国际标准，定义ASIL等级。

## K

**Kani**
Amazon开发的Rust模型检查工具，用于验证安全属性。

**kernel**
操作系统内核，也可指Rust标准库的核心部分。

## L

**生命周期省略 (Lifetime Elision)**
编译器自动推断生命周期标注的规则，减少显式标注。

**Linux内核Rust支持**
Linux内核从6.x开始支持Rust编写驱动程序。

## M

**Miri**
Rust的未定义行为检测工具，解释执行Rust代码。

**MISRA C**
嵌入式C语言编码规范，广泛用于安全关键系统。

**MISRA Rust**
正在开发中的Rust编码规范（基于MISRA C:2025 Addendum 6）。

**MC/DC (Modified Condition/Decision Coverage)**
修改条件/判定覆盖，高级别安全认证要求的测试覆盖标准。

## N

**no_std**
Rust属性，表示不使用标准库，用于嵌入式和裸机环境。

**NASA cFS**
NASA核心飞行系统，有Rust绑定项目。

## O

**OOM (Out of Memory)**
内存不足，Rust中通常panic，嵌入式中可自定义处理。

**OOM钩子**
`set_alloc_error_hook`，自定义内存分配失败行为。

**Option<T>**
Rust标准库类型，表示可能有值(Some)或无(None)，替代空指针。

**所有权系统 (Ownership System)**
Rust内存管理核心机制，通过所有权、借用、生命周期保证安全。

## P

**Panic**
Rust的不可恢复错误处理机制，默认终止程序。

**PLDI (Programming Language Design and Implementation)**
ACM程序设计语言设计与实现会议，顶级会议。

**POPL (Principles of Programming Languages)**
ACM程序设计语言原理会议，顶级会议。

**Prove-it**
Amazon的Rust证明基础设施（Verus前身）。

## R

**RAII (Resource Acquisition Is Initialization)**
资源获取即初始化，Rust通过所有权和Drop trait实现。

**Result<T, E>**
Rust标准库类型，表示操作可能成功(Ok)或失败(Err)。

**Rust Foundation**
Rust基金会，负责Rust语言和生态治理。

**RustSec Advisory Database**
Rust crate安全漏洞数据库。

## S

**SAFETY (Safety Analysis)**
安全分析，包括FMEA、FTA等方法。

**Send trait**
标记类型可安全跨线程传输。

**SIL (Safety Integrity Level)**
IEC 61508定义的安全完整性等级，从SIL 1到SIL 4。

**SPARK**
Ada的子集，支持形式化验证，AdaCore提供Ada/Rust互操作。

**Sync trait**
标记类型可安全跨线程共享引用。

## T

**TÜV SÜD**
德国技术检验协会，提供功能安全认证服务。

**Trait**
Rust中定义共享行为的类型系统特性，类似接口。

**Tree Borrows**
Rust内存模型，PLDI 2025 Distinguished Paper，比Stacked Borrows更精确。

## U

**UB (Undefined Behavior)**
未定义行为，如空指针解引用、数据竞争等，Rust编译器防止Safe Rust出现UB。

**Unsafe Code Guidelines**
Rust不安全代码指南，定义unsafe代码的不变量。

## V

**Verus**
VMware开发的Rust定理证明工具。

**Vet**
Mozilla开发的供应链审计工具，`cargo vet`。

## W

**WASM (WebAssembly)**
Rust可编译为WebAssembly在浏览器或嵌入式运行。

## Z

**Zero-cost Abstraction**
零成本抽象，Rust的高级特性在编译后无运行时开销。

**ZST (Zero-Sized Type)**
零大小类型，如()`，不占用内存但提供类型安全。

---

## 缩略语表

| 缩略语 | 全称 | 中文 |
|--------|------|------|
| ASIL | Automotive Safety Integrity Level | 汽车安全完整性等级 |
| DAL | Development Assurance Level | 开发保证等级 |
| FLS | Ferrocene Language Specification | Ferrocene语言规范 |
| FMEA | Failure Mode and Effects Analysis | 失效模式与影响分析 |
| FTA | Fault Tree Analysis | 故障树分析 |
| FSC | Functional Safety Certified | 功能安全认证 |
| FSE | Functional Safety Expert | 功能安全专家 |
| FSM | Functional Safety Manager | 功能安全经理 |
| HAL | Hardware Abstraction Layer | 硬件抽象层 |
| MC/DC | Modified Condition/Decision Coverage | 修改条件/判定覆盖 |
| MIR | Mid-level IR | 中级中间表示 |
| MISRA | Motor Industry Software Reliability Association | 汽车工业软件可靠性协会 |
| OOM | Out of Memory | 内存不足 |
| PL | Programming Language | 程序设计语言 |
| POPL | Principles of Programming Languages | 程序设计语言原理 |
| PLDI | Programming Language Design and Implementation | 程序设计语言设计与实现 |
| RAII | Resource Acquisition Is Initialization | 资源获取即初始化 |
| SIL | Safety Integrity Level | 安全完整性等级 |
| TQL | Tool Qualification Level | 工具鉴定等级 |
| UB | Undefined Behavior | 未定义行为 |
| UAF | Use After Free | 释放后使用 |
| ZST | Zero-Sized Type | 零大小类型 |

---

## 中英文对照

| 英文 | 中文 |
|------|------|
| Ownership | 所有权 |
| Borrowing | 借用 |
| Lifetime | 生命周期 |
| Trait | 特质/特征 |
| Generic | 泛型 |
| Unsafe | 不安全 |
| Safety | 安全 |
| Security | 安全/安保 |
| Certification | 认证 |
| Qualification | 鉴定 |
| Verification | 验证 |
| Validation | 确认 |
| Traceability | 可追溯性 |
| Coverage | 覆盖率 |
| Compliance | 合规 |

---

**术语表版本**: 1.0
**最后更新**: 2026-03-18
**维护者**: Rust安全关键系统工作组

---

*术语建议？提交到项目文档仓库。*
