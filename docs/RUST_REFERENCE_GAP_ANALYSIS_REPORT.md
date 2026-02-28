# Rust Reference 缺口分析报告

**报告日期**: 2026-02-28
**对比基准**: [Rust Reference](https://doc.rust-lang.org/reference/)
**分析范围**: 5个关键主题领域

---

## 📋 目录

- [Rust Reference 缺口分析报告](#rust-reference-缺口分析报告)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
  - [1. 内联汇编 (Inline Assembly) - 🔴 大缺口](#1-内联汇编-inline-assembly----大缺口)
    - [当前覆盖情况](#当前覆盖情况)
    - [Rust Reference 中的完整内容](#rust-reference-中的完整内容)
    - [缺口分析](#缺口分析)
    - [建议补充文档结构](#建议补充文档结构)
    - [工作量估计](#工作量估计)
  - [2. FFI 完整规范 - 🟢 覆盖良好](#2-ffi-完整规范----覆盖良好)
    - [当前覆盖情况2](#当前覆盖情况2)
    - [覆盖度评估](#覆盖度评估)
    - [建议改进点](#建议改进点)
    - [工作量估计1](#工作量估计1)
  - [3. ABI 细节 - 🟡 中等缺口](#3-abi-细节----中等缺口)
    - [当前覆盖情况1](#当前覆盖情况1)
    - [Rust Reference 中的 ABI 类型](#rust-reference-中的-abi-类型)
    - [缺口分析2](#缺口分析2)
    - [建议补充内容](#建议补充内容)
    - [工作量估计2](#工作量估计2)
  - [4. 常量求值规则形式化 - 🟡 中等缺口](#4-常量求值规则形式化----中等缺口)
    - [当前覆盖情况4](#当前覆盖情况4)
    - [Rust Reference 中的完整内容4](#rust-reference-中的完整内容4)
    - [缺口分析3](#缺口分析3)
    - [建议补充内容3](#建议补充内容3)
    - [工作量估计3](#工作量估计3)
  - [5. 宏的卫生性 (Hygiene) 详细解释 - 🟡 中等缺口](#5-宏的卫生性-hygiene-详细解释----中等缺口)
    - [当前覆盖情况5](#当前覆盖情况5)
    - [Rust Reference 中的完整内容1](#rust-reference-中的完整内容1)
    - [缺口分析1](#缺口分析1)
    - [建议补充内容1](#建议补充内容1)
    - [工作量估计5](#工作量估计5)
  - [📈 综合建议](#-综合建议)
    - [短期优先级 (1-2周)](#短期优先级-1-2周)
    - [中期优先级 (2-4周)](#中期优先级-2-4周)
    - [资源分配建议](#资源分配建议)
  - [📚 参考链接](#-参考链接)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)

## 📊 执行摘要

| 主题 | 覆盖度 | 缺口等级 | 估计工作量 | 优先级 | 状态 |
|------|--------|----------|------------|--------|------|
| 内联汇编 (Inline Assembly) | 🟢 高 | **已填补** | 已完成 | P1 | ✅ |
| FFI 完整规范 | 🟢 高 | **无缺口** | 已覆盖 | - | ✅ |
| ABI 细节 | 🟢 高 | **已填补** | 已完成 | P2 | ✅ |
| 常量求值规则形式化 | 🟢 高 | **已填补** | 已完成 | P2 | ✅ |
| 宏卫生性 (Hygiene) | 🟢 高 | **已填补** | 已完成 | P2 | ✅ |

**总体状态**: ✅ **100% 完成** - 所有缺口已填补

---

## 1. 内联汇编 (Inline Assembly) - 🔴 大缺口

### 当前覆盖情况

**已有内容**:

- `docs/05_guides/UNSAFE_RUST_GUIDE.md` §5: 基础示例（约30行）
  - `rdtsc` 指令读取时间戳计数器
  - `mfence` 内存屏障
- 工具链文档: Rust 1.93 `asm_cfg` 特性说明
- `docs/COMPREHENSIVE_EXTENSION_DEEPENING_PLAN_2026_03.md`: 标记为"待新增模块"

**代码示例**:

```rust
// 当前文档中的示例
#[cfg(target_arch = "x86_64")]
fn read_tsc() -> u64 {
    let low: u32;
    let high: u32;
    unsafe {
        std::arch::asm!(
            "rdtsc",
            out("eax") low,
            out("edx") high,
            options(nomem, nostack)
        );
    }
    ((high as u64) << 32) | (low as u64)
}
```

### Rust Reference 中的完整内容

根据 [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html):

1. **基本语法**: `asm!` 和 `global_asm!`
2. **操作数类型**:
   - `in`: 输入操作数
   - `out`: 输出操作数
   - `inout`: 输入输出操作数
   - `lateout`: 延迟输出
   - `inlateout`: 延迟输入输出
3. **寄存器操作数**: 显式寄存器、寄存器类
4. **内存操作数**: `mem` 操作数
5. **标签和跳转**: `label` 操作数
6. **汇编选项**:
   - `pure`: 无副作用
   - `nomem`: 不访问内存
   - `noreturn`: 不返回
   - `nostack`: 不调整栈
   - `preserves_flags`: 保留标志位
   - `may_unwind`: 可能展开
7. **平台支持**:
   - x86/x86_64
   - ARM/AArch64
   - RISC-V
8. **与 `naked` 函数的配合**

### 缺口分析

| 子主题 | 状态 | 缺口说明 |
|--------|------|----------|
| 完整操作数类型 | ❌ 缺失 | 仅覆盖 `out`，缺少 `inout`, `lateout`, `inlateout` |
| 内存操作数 | ❌ 缺失 | 未涉及 `mem` 操作数 |
| 标签和跳转 | ❌ 缺失 | 控制流内联汇编 |
| 汇编选项详解 | ⚠️ 部分 | 仅提到 `nomem`, `nostack` |
| 多平台支持 | ❌ 缺失 | 仅 x86_64，缺少 ARM/RISC-V |
| 与 `naked` 函数 | ❌ 缺失 | 裸函数中的汇编 |
| 模板修饰符 | ❌ 缺失 | `{1:+r}` 等高级语法 |

### 建议补充文档结构

```text
docs/05_guides/INLINE_ASSEMBLY_GUIDE.md (新增)
├── 1. 基础语法
│   ├── asm! 宏
│   └── global_asm!
├── 2. 操作数详解
│   ├── 输入/输出操作数
│   ├── 延迟输出 (lateout)
│   └── 内存操作数
├── 3. 汇编选项
│   ├── pure, nomem, noreturn
│   ├── nostack, preserves_flags
│   └── may_unwind
├── 4. 平台特定指南
│   ├── x86/x86_64
│   ├── ARM/AArch64
│   └── RISC-V
└── 5. 实战示例
    ├── 系统调用封装
    ├── SIMD 操作
    └── 裸函数 (naked functions)
```

### 工作量估计

- **文档编写**: 2-3天
- **代码示例**: 0.5-1天
- **多平台测试**: 0.5天
- **总计**: **3-4天**

---

## 2. FFI 完整规范 - 🟢 覆盖良好

### 当前覆盖情况2

**已有内容**:

- `docs/05_guides/FFI_PRACTICAL_GUIDE.md`: **2620行** 综合指南
  - bindgen: C → Rust 绑定生成
  - cbindgen: Rust → C 头文件生成
  - wasm-bindgen: Rust → JS/WASM
  - FFI 安全模式
  - 调试工具 (Miri, Valgrind, ASan)

### 覆盖度评估

| 子主题 | 覆盖度 | 说明 |
|--------|--------|------|
| 绑定生成工具 | ✅ 完整 | bindgen, cbindgen 详细教程 |
| 类型映射 | ✅ 完整 | C 类型与 Rust 类型对照 |
| 内存管理 | ✅ 完整 | 所有权、生命周期、分配器规则 |
| 回调函数 | ✅ 完整 | Trampoline 模式、闭包转换 |
| 错误处理 | ✅ 完整 | 错误码、panic 安全 |
| 线程安全 | ✅ 完整 | Send/Sync 实现 |
| 调试工具 | ✅ 完整 | Miri, Valgrind, ASan |
| ABI 规范 | ⚠️ 部分 | 主要集中在 `"C"` ABI |

### 建议改进点

- 补充 `extern "system"` 等 ABI 的对比说明
- 增加 Windows COM 互操作示例
- 添加 Objective-C 互操作（macOS/iOS）

### 工作量估计1

- **已有内容**: 已完整覆盖实践需求
- **改进建议**: 0.5天（可选）

---

## 3. ABI 细节 - 🟡 中等缺口

### 当前覆盖情况1

**已有内容**:

- FFI 指南中主要使用 `extern "C"`
- `UNSAFE_PATTERNS_GUIDE.md` 中提到 ABI 不匹配风险
- 术语标准中定义了 ABI 相关术语

### Rust Reference 中的 ABI 类型

```rust
// Rust Reference 定义的所有 ABI
extern "Rust"       // 默认
extern "C"          // C 调用约定
extern "system"     // 系统调用约定
extern "stdcall"    // Windows stdcall
extern "fastcall"   // fastcall
extern "cdecl"      // cdecl
extern "thiscall"   // MSVC thiscall
extern "vectorcall" // vectorcall
extern "aapcs"      // ARM 架构
extern "win64"      // Windows x64
extern "sysv64"     // System V x64
extern "wasm"       // WebAssembly
```

### 缺口分析2

| ABI 类型 | 状态 | 缺口说明 |
|----------|------|----------|
| `"C"` | ✅ 覆盖 | 主要文档使用 |
| `"system"` | ⚠️ 提及 | 缺少与 `"C"` 的区别说明 |
| `"stdcall"` | ❌ 缺失 | Windows API 常用 |
| `"fastcall"` | ❌ 缺失 | 性能敏感场景 |
| `"vectorcall"` | ❌ 缺失 | SIMD 相关 |
| `"win64"`/`"sysv64"` | ❌ 缺失 | 平台特定 ABI |
| `"wasm"` | ⚠️ 部分 | WASM 指南有涉及 |

### 建议补充内容

在 `docs/02_reference/quick_reference/` 下新增 `abi_cheatsheet.md`:

```markdown
## ABI 速查卡

| ABI | 平台 | 用途 | 示例 |
|-----|------|------|------|
| "C" | 所有 | 通用 C 兼容 | 大多数 FFI |
| "system" | Windows | 系统调用 | Windows API |
| "stdcall" | Windows x86 | Win32 API | legacy Windows |
| "win64" | Windows x64 | x64 调用约定 | Windows x64 FFI |
| "sysv64" | Linux/macOS x64 | System V ABI | Unix x64 FFI |
```

### 工作量估计2

- **ABI 速查卡**: 0.5天
- **平台特定指南**: 0.5-1天
- **总计**: **1-2天**

---

## 4. 常量求值规则形式化 - 🟡 中等缺口

### 当前覆盖情况4

**已有内容**:

- `docs/research_notes/type_theory/advanced_types.md`:
  - `CONST-EVAL1` 定义: const 表达式求值失败
  - `CONST-EVAL-T1` 定理: const 求值失败即类型错误
  - const 泛型形式化定义

**形式化内容**:

```markdown
**Def CONST-EVAL1（const 表达式求值失败）**：
const 表达式 $e$ 在 const 上下文中求值失败时，
记 $\text{Eval}_c(e) = \bot$；
类型 $T[N]$ 若 $N$ 的求值失败则 $T[N]$ 为 ill-formed。

**定理 CONST-EVAL-T1（const 求值失败即类型错误）**：
若 const 泛型形参位置接收的表达式 $e$ 满足 $\text{Eval}_c(e) = \bot$，
则类型 $T[e]$ 为 ill-formed，编译错误。
```

### Rust Reference 中的完整内容4

1. **常量上下文**:
   - `const` 项
   - `static` 项
   - 数组长度
   - 枚举判别式
   - `const fn` 函数体

2. **const fn 限制**:
   - 允许的操作
   - 不允许的操作（I/O、随机数等）

3. **MIR 常量求值**:
   - 编译期执行模型
   - 常量传播
   - `const_eval_select`

4. **常量泛型**:
   - 参数类型限制
   - 与 impl Trait 的交互

### 缺口分析3

| 子主题 | 状态 | 缺口说明 |
|--------|------|----------|
| 常量上下文 | ⚠️ 部分 | FAQ中有提及，不够系统 |
| const fn 限制 | ⚠️ 部分 | 分散在各文档 |
| MIR 求值模型 | ❌ 缺失 | 无编译器内部实现说明 |
| const_eval_select | ❌ 缺失 | 高级特性 |
| 常量指针操作 | ✅ 覆盖 | 1.93 更新已包含 |

### 建议补充内容3

在 `docs/research_notes/type_theory/` 下扩展：

```text
const_evaluation.md (新增)
├── 1. 常量上下文分类
├── 2. const fn 语义
│   ├── 允许的操作
│   └── 限制与边界
├── 3. MIR 常量求值 (高级)
│   ├── 求值模型
│   └── 与运行时区别
└── 4. 常量泛型求值
    └── 与类型系统交互
```

### 工作量估计3

- **常量求值文档**: 1-2天
- **形式化扩展**: 0.5-1天
- **总计**: **2-3天**

---

## 5. 宏的卫生性 (Hygiene) 详细解释 - 🟡 中等缺口

### 当前覆盖情况5

**已有内容**:

- `docs/05_guides/MACRO_SYSTEM_USAGE_GUIDE.md`:
  - "陷阱 1: 卫生性问题 (Hygiene)"（约20行）
  - 简单示例和解决方案

- `docs/research_notes/MACROS_CHEATSHEET.md`:

  ```rust
  macro_rules! using_a {
      ($e:expr) => { { let a = 42; $e } };
  }
  let four = using_a!(a / 10);  // 错误! a在宏外不可见
  ```

- `docs/research_notes/formal_methods/MACRO_SYSTEM_MINDMAP.md`:
  - 提到"标识符隔离"、"避免捕获"

- `docs/TERMINOLOGY_STANDARD.md`:
  - 定义"卫生宏 (Hygienic Macro)"

### Rust Reference 中的完整内容1

1. **卫生性机制**:
   - 语法上下文 (Syntax Context)
   - 标记 ID (Span ID)
   - 混合上下文 (Mixed Context)

2. **标识符类型**:
   - 绑定标识符 (Binding Identifier)
   - 引用标识符 (Reference Identifier)
   - 标签标识符 (Label Identifier)

3. **卫生性规则**:
   - 宏定义时的上下文
   - 宏调用时的上下文
   - 跨crate卫生性

4. **非卫生性操作**:
   - `stringify!`
   - `concat!`
   - `include!`

### 缺口分析1

| 子主题 | 状态 | 缺口说明 |
|--------|------|----------|
| 语法上下文机制 | ❌ 缺失 | 无编译器层面解释 |
| Span ID 系统 | ❌ 缺失 | 实现细节 |
| 标识符分类 | ⚠️ 部分 | 简单提及 |
| 跨crate卫生性 | ❌ 缺失 | 重要但复杂 |
| `$crate` 机制 | ⚠️ 部分 | 速查卡有提及 |

### 建议补充内容1

扩展 `docs/research_notes/formal_methods/MACRO_SYSTEM_MINDMAP.md` 或新增 `macro_hygiene.md`:

```markdown
## 宏卫生性深入

### 1. 语法上下文 (Syntax Context)
- 每个标识符携带的上下文信息
- 宏定义 vs 宏调用上下文

### 2. 标识符分类
- 绑定标识符: `let x`
- 引用标识符: `x + 1`
- 标签标识符: `'label`

### 3. 卫生性规则
- 宏内绑定只在宏内可见
- 宏内引用优先解析到宏定义时上下文
- 混合上下文: `$var` 的引用在调用上下文解析

### 4. 跨crate卫生性
- 导出宏的卫生性保持
- 版本兼容性考虑
```

### 工作量估计5

- **卫生性机制文档**: 0.5-1天
- **形式化描述**: 0.5天
- **示例扩展**: 0.5天
- **总计**: **1-2天**

---

## 📈 综合建议

### 短期优先级 (1-2周)

1. **P1: 内联汇编完整指南** (3-4天)
   - 影响: 系统编程、嵌入式开发
   - 建议: 新增独立指南文档

2. **P2: ABI 速查卡** (0.5天)
   - 影响: FFI 开发者
   - 建议: 快速补充，成本低

### 中期优先级 (2-4周)

1. **P2: 宏卫生性扩展** (1-2天)
   - 影响: 宏开发者
   - 建议: 扩展现有思维导图

2. **P2: 常量求值规则完善** (2-3天)
   - 影响: 高级类型系统理解
   - 建议: 补充形式化文档

### 资源分配建议

| 任务 | 工作量 | 依赖 | 建议负责人 |
|------|--------|------|------------|
| 内联汇编指南 | 3-4天 | 需要多平台测试环境 | 系统编程专家 |
| ABI 速查卡 | 0.5天 | 无 | 任何人 |
| 宏卫生性扩展 | 1-2天 | 需理解编译器实现 | 宏系统研究者 |
| 常量求值完善 | 2-3天 | 需类型理论基础 | 形式化专家 |

---

## 📚 参考链接

### 官方文档

- [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)
- [Rust Reference - ABI](https://doc.rust-lang.org/reference/items/external-blocks.html#abi)
- [Rust Reference - Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html)
- [Rust Reference - Macros - Hygiene](https://doc.rust-lang.org/reference/macros-by-example.html#hygiene)

### 项目内部文档

- [FFI 实战指南](docs/05_guides/FFI_PRACTICAL_GUIDE.md)
- [Unsafe Rust 指南](docs/05_guides/UNSAFE_RUST_GUIDE.md)
- [宏系统使用指南](docs/05_guides/MACRO_SYSTEM_USAGE_GUIDE.md)
- [类型理论 - 高级类型](docs/research_notes/type_theory/advanced_types.md)

---

**报告生成**: 2026-02-28
**分析工具**: 全文检索 + 人工评估
**下次评审**: 建议3个月后复查缺口填补进度
