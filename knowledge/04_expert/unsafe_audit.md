# Unsafe Code Auditing (不安全代码审计)

> **Bloom 层级**: 理解

> 学习如何在生产环境中审计和验证 `unsafe` Rust 代码的安全性，掌握系统级的代码审查技能与工具链。
>
> **难度**: Expert ⭐⭐⭐⭐⭐
> **预计学习时间**: 6-8 小时
> **适用场景**: 安全关键系统审计、开源代码审查、unsafe 代码重构

**变更日志**:

- v1.1 (2026-05-19): 补全权威来源标注（Rust Reference、Rustonomicon、Unsafe Code Guidelines、Miri、Ralf Jung）

---

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

完成本章学习后，你将能够：

- ✅ 建立系统化的 `unsafe` 代码审计流程
- ✅ 识别常见的 unsoundness 模式与安全隐患
- ✅ 使用 Miri 验证代码的未定义行为
- ✅ 运用 Fuzzing 技术发现边界安全问题
- ✅ 编写清晰、可验证的 Safety 文档
- ✅ 使用专业工具辅助安全审计

---

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

在开始学习本章之前，请确保你已掌握：

- [Unsafe Rust](../03_advanced/unsafe/unsafe_rust.md) - 深入理解 `unsafe` 块、裸指针、FFI
- [内存模型与 Tree Borrows](../04_expert/miri/tree_borrows.md) - 理解 Rust 的内存模型
- [FFI 与外部调用](../03_advanced/unsafe/ffi.md) - 了解 C 互操作基础
- [生命周期与借用检查](../01_fundamentals/lifetimes.md) - 掌握生命周期系统

**推荐工具准备**:

```bash
# 安装审计工具链
cargo install cargo-geiger
cargo install cargo-fuzz
cargo install cargo-san
cargo install miri  # 或 rustup component add miri
```

---

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**Unsafe Code Auditing（不安全代码审计）** 是对 Rust 代码中 `unsafe` 块及其周边安全契约进行系统性审查的工程实践。其目标是识别可能导致未定义行为（Undefined Behavior, UB）的代码模式，验证 `SAFETY` 注释中的假设是否成立，并确保 unsafe 抽象对外暴露的 API 保持内存安全与线程安全。

> **[来源: Rust Reference: Unsafe Rust]** `unsafe` 块允许使用五种 unsafe 操作：解引用裸指针、调用 unsafe 函数、访问或修改可变静态变量、访问 `union` 字段、调用 `extern` 函数。 ✅
> **[来源: Rustonomicon]** "Safe Rust is the language you use 99% of the time. Unsafe Rust gives you five new superpowers..." 审计即验证这些 superpowers 的使用是否安全。 ✅
> **[来源: Unsafe Code Guidelines]** Rust 官方不安全代码指南定义了未定义行为（UB）的边界和内存模型规则。 ✅

直观上，审计如同为代码中的"安全漏洞"做体检——不是检查代码能否编译（编译器已做），而是检查代码在运行时的假设是否始终成立。

#### 1.2 操作定义
>
> **[来源: Rust Official Docs]**

| 维度 | 审计 (Auditing) | 代码审查 (Code Review) | 测试 (Testing) |
|------|-----------------|------------------------|----------------|
| **目标** | 发现潜在的 UB 和 unsoundness | 发现逻辑错误、风格问题 | 验证功能正确性 |
| **范围** | 聚焦 `unsafe` 块及边界 | 全代码库 | 全代码库（可执行路径） |
| **方法** | 静态分析 + 形式化推理 + 工具验证 | 人工阅读 + 讨论 | 运行时执行 + 断言 |
| **完备性** | 理论上可证明无 UB（结合 Miri） | 无法保证无 UB | 无法覆盖所有执行路径 |

#### 1.3 形式化直觉

Rust 的安全保证基于一个核心契约：**编译器保证 safe 代码不会触发 UB，前提是所有 `unsafe` 块的实现者正确维护了类型系统和内存模型的不变量。**

审计的本质就是验证这个契约的右侧——即 `unsafe` 实现者是否确实维护了这些不变量。形式化地说，审计试图回答：

> 对于每一个 `unsafe` 块，是否存在一组前置条件 `P` 和后置条件 `Q`，使得当 `P` 成立时执行该块，结束时 `Q` 必然成立，且整个过程不违反 Rust 的内存模型？

---

### 模块 2: 核心原理

#### 原理一：不变量（Invariant）是审计的锚点

Rust 的安全建立在**不变量**之上。审计的核心不是找 "bug"，而是验证不变量：

- **类型不变量**：`T` 的位模式始终合法（如 `bool` 只能是 0 或 1）
- **生命周期不变量**：引用始终指向有效内存
- **别名不变量**：`&mut T` 独占访问，`&T` 共享只读访问
- **线程安全不变量**：`Send`/`Sync` 的实现与类型的实际并发行为一致

#### 原理二：`unsafe` 是信任边界

`unsafe` 块是一个**信任边界**（Trust Boundary）：

```rust
// 边界内侧（unsafe）：实现者承担安全责任
pub fn safe_wrapper(data: &[u8]) -> Option<u8> {
    if data.is_empty() {
        return None;
    }
    // 边界外侧（safe）：调用者无需关心内部 unsafe
    unsafe { Some(*data.as_ptr()) }
}
```

审计必须验证：**边界内侧的实现是否对得起边界外侧的信任。**

#### 原理三：局部化原则

Rust 的 unsafe 设计遵循**局部化原则**：unsafe 的影响应当被限制在最小范围内，且通过安全 API 封装后，外部无法通过 safe 代码触发 UB。

审计时遵循"洋葱模型"——从外向内逐层验证：

```
Safe API 层 → 安全契约检查 → Unsafe 实现层 → 不变量验证 → 底层操作
```

---

## 🧠 核心概念

### 不安全代码审计流程

系统化的审计流程是发现问题的关键。一个完整的审计应包含以下阶段：

#### 1. 静态分析阶段

```rust
// ❌ 危险示例：缺少边界检查的裸指针解引用
pub unsafe fn read_buffer(ptr: *const u8, offset: usize) -> u8 {
    *ptr.add(offset)  // 危险：未验证 offset 是否越界
}

// ✅ 修正版本：添加安全检查
pub unsafe fn read_buffer_safe(ptr: *const u8, len: usize, offset: usize) -> Option<u8> {
    if offset >= len {
        return None;  // 显式边界检查
    }
    Some(*ptr.add(offset))
}
```

**审计检查点**:

- [ ] 所有 `unsafe` 块是否都有 `// SAFETY:` 注释
- [ ] 前置条件是否明确记录在文档中
- [ ] 不变量（invariants）是否在调用前后保持一致

#### 2. 不变量验证阶段

```rust
/// # Safety
/// - `ptr` 必须对齐且非空
/// - `ptr` 必须指向有效的 `T` 实例
/// - 调用后 `ptr` 不再有效（所有权转移）
pub unsafe fn take_ownership<T>(ptr: *mut T) -> T {
    // SAFETY: 调用者保证 ptr 有效且对齐
    ptr.read()
}
```

### 安全检查清单

#### 裸指针使用检查

| 检查项 | 风险等级 | 验证方法 |
|--------|----------|----------|
| 解引用前验证非空 | 🔴 严重 | 显式 `is_null()` 检查 |
| 验证内存对齐 | 🔴 严重 | 使用 `align_of::<T>()` 比对 |
| 验证生命周期有效性 | 🔴 严重 | 文档追溯引用来源 |
| 避免悬垂指针 | 🟠 高 | Miri 检测 |
| 防止数据竞争 | 🔴 严重 | 代码审查 + 工具检测 |

#### FFI 边界检查

```rust
// ❌ 问题代码：未验证 C 字符串有效性
pub unsafe fn c_string_to_rust(ptr: *const c_char) -> String {
    CStr::from_ptr(ptr).to_string_lossy().into_owned()  // 可能 panic
}

// ✅ 安全版本：验证后再转换
pub unsafe fn c_string_to_rust_safe(ptr: *const c_char) -> Option<String> {
    if ptr.is_null() {
        return None;
    }
    CStr::from_ptr(ptr)
        .to_str()
        .ok()
        .map(|s| s.to_owned())
}
```

### 模块 5: 正例集

#### 5.1 Minimal（最小正例）

正确使用 `unsafe` 的最小示例——通过裸指针读取已知有效的内存：

```rust
fn get_first_byte(data: &[u8]) -> Option<u8> {
    if data.is_empty() {
        return None;
    }
    // SAFETY: 前面已检查 data 非空，as_ptr() 返回的指针有效
    unsafe { Some(*data.as_ptr()) }
}
```

#### 5.2 Realistic（真实场景）

安全地封装 FFI 调用，将 C 接口转换为 Rust 安全 API：

```rust
use std::ffi::CStr;
use std::os::raw::c_char;

/// 将 C 字符串安全地转换为 Rust `&str`
///
/// # Safety
/// - `ptr` 必须指向以 null 结尾的有效 UTF-8 字节序列
/// - `ptr` 在函数执行期间保持有效
pub unsafe fn c_str_to_str<'a>(ptr: *const c_char) -> Option<&'a str> {
    if ptr.is_null() {
        return None;
    }
    CStr::from_ptr(ptr).to_str().ok()
}

// Safe 包装：调用者无需写 unsafe
pub fn get_config_name(ptr: *const c_char) -> Option<String> {
    unsafe { c_str_to_str(ptr).map(|s| s.to_owned()) }
}
```

#### 5.3 Production-grade（生产级）

标准库中 `Vec::set_len` 的安全封装——`truncate` 和 `split_off` 的实现：

```rust
impl<T> Vec<T> {
    /// 安全地截断 Vec 到指定长度，丢弃多余元素
    pub fn truncate(&mut self, len: usize) {
        if len > self.len {
            return;
        }
        // 先 drop 多余元素（安全操作）
        while self.len > len {
            self.len -= 1;
            // SAFETY: self.len 始终指向已初始化元素
            unsafe {
                std::ptr::drop_in_place(self.as_mut_ptr().add(self.len));
            }
        }
    }
}
```

---

### 模块 6: 反例集

#### 6.1 别名规则违反 (Aliasing Violation)

#### 1. 别名规则违反 (Aliasing Violation)

```rust
// ❌ 严重问题：同时存在可变引用和不可变引用
pub fn aliasing_violation() {
    let mut x = 5;
    let r1 = &mut x as *mut i32;
    let r2 = &x as *const i32;  // 与 r1 别名！

    unsafe {
        *r1 = 10;  // 通过裸指针写入
        println!("{}", *r2);  // 读取 - 未定义行为！
    }
}

// ✅ 修正：确保无别名期不重叠
pub fn no_aliasing() {
    let mut x = 5;
    {
        let r1 = &mut x as *mut i32;
        unsafe { *r1 = 10; }
    }  // r1 作用域结束
    let r2 = &x;
    println!("{}", r2);  // 安全
}
```

#### 6.2 未初始化内存读取

```rust
// ❌ 危险：读取未初始化值
pub unsafe fn read_uninit() -> i32 {
    let x: i32 = std::mem::uninitialized();  // 已废弃，但类似模式仍存在
    x  // 返回未初始化值 - 立即 UB！
}

// ✅ 正确做法：使用 MaybeUninit
use std::mem::MaybeUninit;

pub fn properly_init() -> i32 {
    let mut x = MaybeUninit::<i32>::uninit();
    // ... 初始化 x ...
    unsafe { x.assume_init() }  // 确保初始化后才 assume_init
}
```

#### 6.3 类型混淆 (Type Confusion)

```rust
// ❌ 严重错误：错误解释内存布局
#[repr(C)]
struct Header { magic: u32, len: usize }

pub unsafe fn parse_header(bytes: &[u8]) -> &Header {
    // 危险：未检查字节长度和对齐
    &*(bytes.as_ptr() as *const Header)
}

// ✅ 修正版本：验证所有前提条件
pub unsafe fn parse_header_safe(bytes: &[u8]) -> Option<&Header> {
    // 检查长度
    if bytes.len() < std::mem::size_of::<Header>() {
        return None;
    }

    // 检查对齐
    if bytes.as_ptr().align_offset(std::mem::align_of::<Header>()) != 0 {
        return None;
    }

    Some(&*(bytes.as_ptr() as *const Header))
}
```

#### 6.4 Send/Sync 错误实现

```rust
// ❌ 危险：错误标记 Send/Sync
pub struct RawPtrWrapper(*const u8);

unsafe impl Send for RawPtrWrapper {}  // 危险：裸指针可能不线程安全
unsafe impl Sync for RawPtrWrapper {}  // 同上

// ✅ 仅在真正安全时实现
use std::sync::Arc;

pub struct SafeWrapper(Arc<str>);  // Arc<str> 已是 Send + Sync
// 无需 unsafe impl，编译器自动推导
```

### Miri 在审计中的应用

Miri 是检测未定义行为的强大工具：

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 运行特定示例
cargo miri run --example unsafe_demo
```

#### Miri 检测能力

```rust
// 这段代码会被 Miri 捕获
pub fn miri_catches_this() {
    let mut x = 0u8;
    let ptr = &mut x as *mut u8;

    unsafe {
        let r1 = &mut *ptr;
        let r2 = &mut *ptr;  // Miri: 错误！重复可变借用
        *r1 = 1;
        *r2 = 2;
    }
}
```

**Miri 限制**:

- 不支持所有平台 API
- 执行速度较慢（解释执行）
- 某些 FFI 调用无法检测

### Fuzzing Unsafe 代码

使用 `cargo-fuzz` 发现边界问题：

```bash
# 初始化 fuzz 项目
cargo fuzz init

# 创建 fuzz target
cargo fuzz add parse_header
```

```rust
// fuzz/fuzz_targets/parse_header.rs
#![no_main]
use libfuzzer_sys::fuzz_target;
use my_crate::parse_header_safe;

fuzz_target!(|data: &[u8]| {
    // 使用 unsafe 函数处理随机数据
    let _ = unsafe { parse_header_safe(data) };
});
```

**Fuzzing 最佳实践**:

- 针对解析函数和数据结构
- 关注 FFI 边界
- 结合 AddressSanitizer 使用

### 模块 4: 语法规则

#### 4.1 `unsafe` 块的语法边界

`unsafe` 关键字在 Rust 中有两种用法，审计时必须区分：

| 用法 | 语法 | 审计重点 |
|------|------|----------|
| `unsafe` 块 | `unsafe { ... }` | 块内操作的安全性 |
| `unsafe` 函数 | `unsafe fn foo() { ... }` | 调用者契约 + 实现安全性 |
| `unsafe` trait | `unsafe trait Foo {}` | 实现者的不变量保证 |
| `unsafe impl` | `unsafe impl Foo for Bar {}` | 实现是否满足 trait 的不变量 |

**关键规则**：`unsafe` 块的语义边界是**词法作用域**，不是控制流边界：

```rust
// ❌ 错误：unsafe 块跨分支，难以审计
unsafe {
    if condition {
        *ptr = 1;
    }
    // ptr 可能在此已被释放，但仍在 unsafe 块内
    *ptr2 = 2;
}

// ✅ 正确：每个 unsafe 操作独立成块，明确边界
if condition {
    unsafe { *ptr = 1; }
}
unsafe { *ptr2 = 2; }
```

#### 4.2 `SAFETY` 注释规范

每个 `unsafe` 块**必须**包含 `// SAFETY:` 注释，说明为什么该操作是安全的。标准格式：

```rust
// SAFETY: [前提条件] + [推理过程] → [安全结论]
unsafe { *ptr.add(offset) }
```

**审计检查清单**：

- [ ] `SAFETY` 注释是否明确列出了所有前置条件？
- [ ] 前置条件是否可由调用者验证？
- [ ] 是否有后置条件需要调用者遵守？
- [ ] 注释中的假设是否在代码中得到了验证？

#### 4.3 FFI 声明语法

FFI 边界是审计的重点区域，函数声明必须精确匹配 C 端的 ABI：

```rust
// ❌ 危险：缺少 repr(C) 且类型不匹配
extern "C" {
    fn c_api(data: *mut u8, len: usize) -> i32;
}

// ✅ 正确：精确匹配 C 签名，使用合适的类型
#[repr(C)]
pub struct Buffer {
    ptr: *mut u8,
    len: usize,
}

extern "C" {
    /// # Safety
    /// - `buf.ptr` 必须指向至少 `buf.len` 字节的有效内存
    /// - `buf.ptr` 必须对 C 端写入操作有效
    fn c_api(buf: *mut Buffer) -> c_int;
}
```

---

### 模块 3: 概念依赖图

```mermaid
graph TD
    A[Safe Rust Code] --> B[Unsafe Block]
    B --> C[Raw Pointers]
    B --> D[FFI Calls]
    B --> E[Union Access]
    C --> F[Aliasing Rules]
    C --> G[Uninit Memory]
    D --> H[ABI Mismatch]
    D --> I[Lifetime Bridging]
    F --> J[Miri UB Detection]
    G --> J
    H --> K[Sanitizers]
    I --> K
    J --> L[Systematic Audit]
    K --> L
    L --> M[Safety Documentation]
    M --> N[CI Integration]

    style B fill:#f9f,stroke:#333,stroke-width:2px
    style J fill:#bbf,stroke:#333,stroke-width:2px
    style L fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **Unsafe Rust** | `03_advanced/unsafe/unsafe_rust.md` | `unsafe` 块的 5 种能力、SAFETY 注释规范 |
| **Tree Borrows** | `04_expert/miri/tree_borrows.md` | Miri 使用 TB 模型检测别名违规 |
| **FFI** | `03_advanced/ffi/ffi.md` | FFI 边界的不变量验证是审计重点 |
| **Send/Sync** | `03_advanced/concurrency/threads.md` | `unsafe impl Send/Sync` 的 soundness 论证 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **Safety Critical** | `04_expert/safety_critical/` | 高完整性系统的审计流程与认证 |
| **Compiler Internals** | `04_expert/compiler_internals.md` | 理解 MIR 以分析 unsafe 代码的编译器视角 |
| **Safety Critical Audit** | `04_expert/safety_critical/09_reference/SECURITY_AUDIT_GUIDE.md` | 高完整性系统的系统化安全审计流程与认证标准 |

---

### Safety 文档规范

清晰的安全文档是审计的基础：

```rust
/// 将裸指针转换为引用
///
/// # Safety
///
/// 调用者必须确保：
///
/// 1. **有效性**: `ptr` 指向已分配的、有效的 `T` 类型内存
/// 2. **对齐**: `ptr` 必须按 `T` 的对齐要求对齐
/// 3. **别名**: 在返回引用的生命周期内，不得有其他可变引用或修改
/// 4. **生命周期**: 返回引用的生命周期不能超过所指向数据的有效期
///
/// # Examples
///
/// ```
/// let mut x = 42;
/// let ptr = &mut x as *mut i32;
/// unsafe {
///     let r = my_crate::as_ref_unchecked(ptr);
///     assert_eq!(*r, 42);
/// }
/// ```
pub unsafe fn as_ref_unchecked<'a, T>(ptr: *const T) -> &'a T {
    // SAFETY: 前置条件已由调用者保证
    &*ptr
}
```

### 审计工具链

#### cargo-geiger: 检测不安全代码分布

```bash
# 统计 unsafe 代码
cargo geiger

# 输出详细报告
cargo geiger --output-format json > unsafe_report.json
```

**解读报告**:

- 🔴 `unsafe fn`: 函数声明为 unsafe
- 🟠 `unsafe trait`: trait 声明为 unsafe
- 🟡 `unsafe impl`: trait 实现使用 unsafe
- ⚪ `unsafe block`: unsafe 代码块

#### Sanitizers

```bash
# AddressSanitizer - 检测内存错误
RUSTFLAGS="-Z sanitizer=address" cargo test

# MemorySanitizer - 检测未初始化读取
RUSTFLAGS="-Z sanitizer=memory" cargo test

# ThreadSanitizer - 检测数据竞争
RUSTFLAGS="-Z sanitizer=thread" cargo test
```

---

## 💡 最佳实践

### 1. 最小化 unsafe 范围

```rust
// ❌ 过度使用 unsafe
unsafe fn process_data(ptr: *mut u8, len: usize) {
    // 大量业务逻辑都在 unsafe 块中
    // ... 100 行代码 ...
}

// ✅ 最小化 unsafe 边界
fn process_data_safe(buffer: &mut [u8]) {
    // 安全检查在 safe 区域完成
    if buffer.len() < HEADER_SIZE {
        return;
    }

    unsafe {
        // 只有真正需要 unsafe 的操作在此进行
        raw_operation(buffer.as_mut_ptr())
    }
}
```

### 2. 封装 unsafe 为安全 API

```rust
/// 安全的包装器，内部使用 unsafe
pub struct SafeBuffer {
    ptr: NonNull<u8>,
    len: usize,
    capacity: usize,
}

impl SafeBuffer {
    pub fn new(size: usize) -> Option<Self> {
        if size == 0 {
            return None;
        }

        let layout = Layout::array::<u8>(size).ok()?;
        // SAFETY: size > 0 且 layout 已验证
        let ptr = unsafe { alloc(layout) };

        Some(Self {
            ptr: NonNull::new(ptr)?,
            len: 0,
            capacity: size,
        })
    }
}

impl Drop for SafeBuffer {
    fn drop(&mut self) {
        let layout = Layout::array::<u8>(self.capacity).unwrap();
        // SAFETY: ptr 由 alloc 分配，layout 匹配
        unsafe { dealloc(self.ptr.as_ptr(), layout) };
    }
}
```

### 3. 使用类型系统表达不变量

```rust
// 使用类型而非注释表达状态
pub struct Initialized<T>(T);
pub struct Uninitialized<T>(MaybeUninit<T>);

impl<T> Uninitialized<T> {
    pub fn write(self, value: T) -> Initialized<T> {
        Initialized(value)
    }
}

impl<T> Initialized<T> {
    pub fn into_inner(self) -> T {
        self.0
    }
}
```

### 4. 审计记录模板

```markdown
## Unsafe 审计记录

### 函数信息
- **名称**: `parse_header_safe`
- **文件**: src/parser.rs:42
- **unsafe 原因**: 裸指针转换

### 安全检查
| 检查项 | 状态 | 备注 |
|--------|------|------|
| 前置条件文档化 | ✅ | 完整 Safety 注释 |
| 边界检查 | ✅ | 长度验证 |
| 对齐检查 | ✅ | align_offset 验证 |
| Miri 通过 | ✅ | `cargo miri test` |
| Fuzz 测试 | ✅ | 100万+ 随机输入 |

### 审计结论
- **状态**: 通过
- **日期**: 2024-01-15
- **审计人**: @reviewer
```

---

## 🗺️ 模块 7: 思维表征套件

### 表征 A: Unsafe 审计决策树

```text
开始审计 unsafe 代码
│
├─► 1. 定位所有 unsafe 边界
│   ├─► 统计 unsafe fn / unsafe block / unsafe impl
│   │   └── 工具: cargo-geiger
│   │
│   └─► 评估 unsafe 密度 (unsafe LOC / total LOC)
│       └── 阈值: > 5% 需重点审计
│
├─► 2. 静态分析检查
│   ├─► 每个 unsafe block 是否有 SAFETY 注释?
│   │   ├─► 否 → 要求补充 ← 阻塞项
│   │   └─► 是 → 验证注释是否覆盖所有前提条件
│   │
│   ├─► 裸指针使用检查
│   │   ├─► 解引用前是否验证非空?
│   │   ├─► 是否验证对齐?
│   │   ├─► 是否验证生命周期?
│   │   └─► 是否有数据竞争风险?
│   │
│   └─► FFI 边界检查
│       ├─► C 结构体布局是否匹配 #[repr(C)]?
│       ├─► 字符串是否验证 null 终止?
│       └─► 回调函数生命周期是否安全?
│
├─► 3. 动态验证
│   ├─► Miri 测试
│   │   ├─► `cargo miri test` 通过?
│   │   ├─► 覆盖所有 unsafe 路径?
│   │   └─► Tree Borrows 模式?
│   │
│   ├─► Fuzzing
│   │   ├─► 针对解析/转换函数
│   │   ├─► 运行时间: ≥ 1小时或 ≥ 100万次输入
│   │   └─► 结合 AddressSanitizer?
│   │
│   └─► Sanitizers
│       ├─► AddressSanitizer (内存错误)
│       ├─► MemorySanitizer (未初始化读取)
│       └─► ThreadSanitizer (数据竞争)
│
└─► 4. 审计结论
    ├─► 通过 → 记录审计日志，集成 CI
    ├─► 有条件通过 → 标记风险，制定修复计划
    └─► 不通过 → 重构或增加安全防护层
```

### 表征 B: Unsoundness 模式严重度矩阵

| 模式 | 发生频率 | 检测难度 | 影响范围 | 修复成本 | 综合风险 |
|------|---------|---------|---------|---------|---------|
| **别名规则违反** | 高 | 中（Miri 可捕） | 局部/全局 | 中 | 🔴 严重 |
| **未初始化内存读取** | 中 | 低（MSan 可捕） | 局部 | 低 | 🟠 高 |
| **类型混淆（FFI）** | 中 | 高（需人工审计） | 全局 | 高 | 🔴 严重 |
| **Send/Sync 错误实现** | 低 | 高（并发 bug 难复现） | 全局 | 中 | 🔴 严重 |
| **悬垂指针** | 中 | 中（Miri/ASan 可捕） | 局部 | 低 | 🟠 高 |
| **双重释放** | 低 | 中（ASan 可捕） | 局部 | 低 | 🟠 高 |
| **整数溢出（release）** | 中 | 高（需特定输入） | 局部 | 低 | 🟡 中 |

### 表征 C: 工具覆盖范围维恩图（ASCII）

```text
UB 检测工具覆盖范围
═══════════════════════════════════════════════════════════════════

  ┌─────────────────────────────────────────────────────────┐
  │                    所有可能的行为                        │
  │  ┌─────────────────────────────────────────────────┐   │
  │  │              编译器可检测的错误                    │   │
  │  │  ┌─────────────┐  ┌─────────────────────────┐  │   │
  │  │  │  Miri (TB)  │  │      Sanitizers         │  │   │
  │  │  │             │  │  ┌─────┐  ┌───────────┐ │  │   │
  │  │  │ • 悬垂指针  │  │  │ ASan│  │   MSan    │ │  │   │
  │  │  │ • 别名违规  │──┤  │     │  │           │ │  │   │
  │  │  │ • 双重释放  │  │  │ • 越界│  │ • 未初始化│ │  │   │
  │  │  │ • 未对齐访问│  │  │ • UAF│  │ • 未定义  │ │  │   │
  │  │  │             │  │  └─────┘  └───────────┘ │  │   │
  │  │  └─────────────┘  └─────────────────────────┘  │   │
  │  │           │                                    │   │
  │  │           └─────── 重叠: 内存错误 ──────────────┘   │
  │  └─────────────────────────────────────────────────┘   │
  │                                                         │
  │  外部: Fuzzing（扩大输入空间覆盖）                        │
  │  外部: 人工审计（逻辑错误、业务规则）                      │
  └─────────────────────────────────────────────────────────┘

关键洞察: 没有单一工具能覆盖所有 UB。Miri 检测 Rust 特有的别名规则违规，
ASan/MSan 检测底层内存错误，Fuzzing 扩大输入空间，人工审计覆盖逻辑漏洞。
```

---

## ⚠️ 常见陷阱

### 1. 误用 `as` 转换指针

```rust
// ❌ 错误：丢失引用信息
let ptr = &x as *const _ as *mut _;  // 通过裸指针绕过借用检查

// ✅ 正确：使用 cast 保持清晰
let ptr: *mut T = (&raw mut x);  // Rust 1.82+ 的显式裸指针语法
```

### 2. 忽略 Drop 语义

```rust
// ❌ 危险：忘记处理析构
pub unsafe fn forget_drop<T>(val: T) {
    std::mem::forget(val);  // 危险：资源泄漏
}

// ✅ 正确：显式管理资源
pub unsafe fn into_raw<T>(val: T) -> *mut T {
    let ptr = &val as *const T as *mut T;
    std::mem::forget(val);  // SAFETY: 所有权已转移给调用者
    ptr
}
```

### 3. 信任外部输入

```rust
// ❌ 永远不要信任 FFI 输入
pub unsafe fn process_c_struct(ptr: *const CStruct) {
    let s = &*ptr;  // 危险：可能指向无效内存
}

// ✅ 验证所有输入
pub unsafe fn process_c_struct_safe(ptr: *const CStruct) -> Option<&'static CStruct> {
    if ptr.is_null() {
        return None;
    }
    // 进一步验证结构体字段...
    Some(&*ptr)
}
```

---

## 📚 模块 8: 国际化对齐

### 8.1 官方来源

| 来源 | 类型 | 对应章节/条目 | 本文档对应点 |
|------|------|---------------|--------------|
| [The Rustonomicon](https://doc.rust-lang.org/nomicon/) | 官方 | 全书 | 模块 1-2 |
| [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | 官方 | Stacked Borrows, validity invariants | 模块 2（别名规则） |
| [Miri 文档](https://github.com/rust-lang/miri) | 官方 | UB 检测范围 | 模块 3.2 |

### 8.2 学术来源

| 论文/来源 | 会议/机构 | 核心论证 | 本文档对应点 |
|-----------|-----------|----------|--------------|
| **"Stacked Borrows"** | POPL 2019 (Jung et al.) | Rust 别名模型的形式化定义，为 Miri 提供理论基础 | 模块 2.1 |
| **"Tree Borrows"** | PLDI 2025 (Villani et al.) | 下一代别名模型，降低 54% 误报 | 模块 3.2 |
| **"RustBelt"** | POPL 2018 | 用 Iris 证明 Rust 类型系统安全性 | 模块 2（unsafe 代码的证明责任） |

### 8.3 社区权威

| 作者 | 文章/演讲 | 核心观点 | 本文档对应点 |
|------|-----------|----------|--------------|
| **Ralf Jung** | [Miri 与内存模型](https://www.ralfj.de/blog/) | Miri 的设计哲学与内存模型演进 | 模块 3.2 |
| **Rust Secure Code WG** | [cargo-geiger, cargo-audit](https://github.com/rust-secure-code) | unsafe 代码审计工具链的最佳实践 | 模块 3.4 |
| **Mara Bos** | [Rust 安全实践](https://marabos.nl/) | 生产环境 unsafe 代码的审计经验 | 模块 5 |

### 8.4 跨语言对比

| 维度 | Rust (unsafe audit) | C/C++ (code review) | Go (unsafe package) | Swift |
|------|---------------------|---------------------|---------------------|-------|
| **审计工具** | Miri + sanitizers + fuzzing | Valgrind/ASan/UBSan | 有限（无 Miri 等价物） | Address Sanitizer |
| **别名模型** | Stacked/Tree Borrows（形式化） | 无（依赖开发者） | 无 | 无 |
| **UB 定义** | 明确（Unsafe Code Guidelines） | 部分定义（C11 后改进） | 有限定义 | 明确 |
| **社区审计文化** | 强（RustSec, Safety Dance） | 中（CVE 数据库） | 弱 | 弱 |
| **形式化验证** | RustBelt + Miri | 无 | 无 | 无 |

> **关键差异**: Rust 是唯一围绕 unsafe 代码建立了**系统化审计文化**和**专用工具链**（Miri + cargo-geiger + RustSec）的语言。C/C++ 虽有 AddressSanitizer，但缺少针对语言特有 UB（如别名规则）的精确检测工具。

---

## ⚖️ 模块 9: 设计权衡分析

### 9.1 为什么 Rust 采用 "unsafe 块" 而非 "安全子集" 设计？

替代方案是像 SPARK Ada 那样定义一个可证明安全的子集，禁止所有不安全操作。Rust 选择保留 `unsafe` 关键字的原因：

1. **系统编程需求**: 操作系统、嵌入式、性能关键代码需要直接内存操作，完全禁止不现实。
2. **FFI 必要性**: 与 C/C++ 生态的互操作是系统语言的刚需。
3. **抽象能力**: `unsafe` 允许库作者实现零成本抽象（如 `Vec`、`HashMap`），用户以安全 API 使用。

代价：审计负担落在 unsafe 代码的作者和维护者身上。

### 9.2 该设计的成本

**审计成本**: 每个 unsafe 块都需要 SAFETY 注释、不变量文档和工具验证。对于大型 unsafe 代码库（如 `std` 内部），审计成本极高。

**工具限制**: Miri 不支持所有平台 API，执行速度慢，无法替代所有测试。Sanitizers 需要 nightly 编译器，增加了 CI 复杂度。

**知识门槛**: 理解 Tree Borrows、validity invariant、niche optimization 等概念需要深厚的 Rust 知识，新手难以参与 unsafe 代码审计。

### 9.3 什么场景下 "最小化 unsafe" 策略是次优的？

1. **极端性能优化**: 某些算法（如无锁数据结构、SIMD 优化）必须用 unsafe 才能达到理论最优性能。过度封装可能引入额外开销。
2. **操作系统内核**: 内核代码大量涉及裸指针、内存映射、中断处理，unsafe 密度天然很高。此时重点是**系统化审计**而非**最小化 unsafe**。
3. **FFI 密集项目**: 与大型 C 库（如 OpenSSL、TensorFlow）绑定时，unsafe 代码量与 C API 表面积成正比，无法避免。

---

## 📝 模块 10: 自我检测与练习

### 概念性问题

1. **Miri 与 AddressSanitizer (ASan) 的检测范围有何重叠和差异？** 为什么两者都需要在审计流程中使用？

2. **Tree Borrows 相比 Stacked Borrows 对 Miri 审计的影响是什么？** 如果项目之前用 SB 通过了 Miri，切换到 TB 后可能需要修复哪些"新发现"的代码？

3. **为什么说 `unsafe impl Send/Sync` 是"最危险的 unsafe 操作"之一？** 它与 alias violation、uninit read 等模式在检测难度上有何不同？

### 代码修复题

**题 1**: 以下代码存在多个安全问题。请识别所有问题并用 Miri + SAFETY 注释修复：

```rust
pub struct Buffer {
    ptr: *mut u8,
    len: usize,
}

impl Buffer {
    pub fn new(len: usize) -> Self {
        let layout = std::alloc::Layout::array::<u8>(len).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        Self { ptr, len }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    pub fn resize(&mut self, new_len: usize) {
        self.len = new_len;
    }
}
```

<details>
<summary>参考答案</summary>

**问题识别**:

1. `alloc` 可能返回 null，未检查
2. `len` 可能为 0，`Layout::array` 可能 panic
3. `as_slice` 未检查 ptr 是否为 null
4. `resize` 改变 len 但不重新分配，可能导致越界访问
5. 缺少 `Drop` 实现，内存泄漏

**修复版本**:

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

pub struct Buffer {
    ptr: NonNull<u8>,
    len: usize,
    capacity: usize,
}

impl Buffer {
    /// # Errors
    /// 如果 `len == 0` 或内存分配失败，返回 `None`
    pub fn new(len: usize) -> Option<Self> {
        if len == 0 {
            return None;
        }
        let layout = Layout::array::<u8>(len).ok()?;
        // SAFETY: layout 非零大小，已验证
        let ptr = unsafe { NonNull::new(alloc(layout))? };
        Some(Self { ptr, len: 0, capacity: len })
    }

    /// # Safety
    /// `self.ptr` 必须指向有效内存且 `self.len` 不超过分配大小
    pub unsafe fn as_slice_unchecked(&self) -> &[u8] {
        // SAFETY: 调用者保证 ptr 有效且 len 正确
        std::slice::from_raw_parts(self.ptr.as_ptr(), self.len)
    }

    pub fn as_slice(&self) -> Option<&[u8]> {
        if self.len == 0 {
            return Some(&[]);
        }
        // SAFETY: ptr 由 alloc 分配，len 已验证
        Some(unsafe { self.as_slice_unchecked() })
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        let layout = Layout::array::<u8>(self.capacity).unwrap();
        // SAFETY: ptr 由 alloc 分配，layout 匹配
        unsafe { dealloc(self.ptr.as_ptr(), layout) };
    }
}
```

</details>

**题 2**: 以下 FFI 绑定存在类型安全问题。请分析并修复：

```rust
extern "C" {
    fn process_data(data: *const u8, len: usize) -> i32;
}

pub fn safe_process(data: &[u8]) -> i32 {
    unsafe { process_data(data.as_ptr(), data.len()) }
}
```

<details>
<summary>参考答案</summary>

**问题**: C 函数 `process_data` 的返回值 `i32` 被假设为"成功/失败"码，但 Rust 侧未验证。C 函数可能通过返回值传递指针（如错误码指针），导致类型混淆。此外，C 函数可能在内部修改数据（尽管签名是 `*const`）。

**修复**:

```rust
use std::ffi::c_int;

extern "C" {
    /// 处理数据，返回 0 表示成功，负值表示错误码
    fn process_data(data: *const u8, len: usize) -> c_int;
}

#[derive(Debug)]
pub enum ProcessError {
    InvalidInput,
    CError(i32),
}

pub fn safe_process(data: &[u8]) -> Result<(), ProcessError> {
    if data.is_empty() {
        return Err(ProcessError::InvalidInput);
    }
    // SAFETY: data.as_ptr() 非空，len 匹配，C 函数签名正确
    let ret = unsafe { process_data(data.as_ptr(), data.len()) };
    if ret == 0 {
        Ok(())
    } else {
        Err(ProcessError::CError(ret))
    }
}
```

</details>

### 开放设计题

**题 3**: 你的团队维护一个包含 50,000 行 Rust 代码的 crate，其中 3%（1,500 行）是 unsafe 代码，分布在 12 个 `unsafe` 块中。你刚加入团队，需要建立 unsafe 代码审计流程。请设计一个可持续的审计策略，考虑：

- **工具链**: Miri、Sanitizers、Fuzzing、cargo-geiger 的优先级和使用频率
- **CI 集成**: 哪些检查必须阻塞合并？哪些可以异步运行？
- **人力审计**: 如何分配审计责任？新提交的 unsafe 代码与存量代码的不同策略？
- **度量指标**: 如何跟踪审计覆盖率和 unsafe 代码质量？

> 💡 提示：参考模块 7 的审计决策树和模块 3 的工具矩阵。

---

## 🎮 动手练习

### 练习 1: 审计 Unsafe 代码

找到以下代码中的安全问题并修复：

```rust
pub struct Buffer {
    ptr: *mut u8,
    len: usize,
}

impl Buffer {
    pub fn new(len: usize) -> Self {
        let ptr = unsafe { libc::malloc(len) as *mut u8 };
        Self { ptr, len }
    }

    pub fn get(&self, idx: usize) -> u8 {
        unsafe { *self.ptr.add(idx) }
    }
}
```

<details>
<summary>点击查看答案</summary>

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

pub struct Buffer {
    ptr: NonNull<u8>,
    len: usize,
    capacity: usize,
}

impl Buffer {
    /// # Errors
    /// 返回 `None` 如果 len 为 0 或内存分配失败
    pub fn new(len: usize) -> Option<Self> {
        if len == 0 {
            return None;
        }
        let layout = Layout::array::<u8>(len).ok()?;
        // SAFETY: layout 非零大小
        let ptr = unsafe { NonNull::new(alloc(layout))? };
        Some(Self { ptr, len: 0, capacity: len })
    }

    /// # Safety
    /// idx 必须小于 self.len
    pub unsafe fn get_unchecked(&self, idx: usize) -> u8 {
        // SAFETY: 调用者保证 idx 在范围内
        *self.ptr.as_ptr().add(idx)
    }

    pub fn get(&self, idx: usize) -> Option<u8> {
        if idx >= self.len {
            return None;
        }
        // SAFETY: 已通过边界检查
        Some(unsafe { *self.ptr.as_ptr().add(idx) })
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        let layout = Layout::array::<u8>(self.capacity).unwrap();
        // SAFETY: ptr 由 alloc 分配，layout 匹配
        unsafe { dealloc(self.ptr.as_ptr(), layout) };
    }
}
```

</details>

### 练习 2: Safety 文档编写

为以下函数编写完整的安全文档：

```rust
pub unsafe fn transmute_slice<T, U>(slice: &[T]) -> &[U] {
    let ptr = slice.as_ptr() as *const U;
    let len = slice.len() * std::mem::size_of::<T>() / std::mem::size_of::<U>();
    std::slice::from_raw_parts(ptr, len)
}
```

### 练习 3: Miri 验证

使用 Miri 验证以下代码，找出其中的未定义行为：

```rust
fn main() {
    let mut x = 42;
    let ptr = &mut x as *mut i32;

    unsafe {
        let r1 = &mut *ptr;
        let r2 = &*ptr;  // 问题在哪？
        println!("{} {}", r1, r2);
    }
}
```

---

### 补充: Rust 1.95+ Layout API 更新

Rust 1.95 为 `std::alloc::Layout` 新增多个辅助方法，简化自定义分配器实现：

```rust
use std::alloc::Layout;

// dangling_ptr: 获取对齐的悬空指针（用于占位，不实际分配）
let ptr = Layout::new::<i32>().dangling_ptr();

// repeat: 计算 N 个副本的布局（含填充）
let (layout, offset) = Layout::new::<u64>().repeat(10).unwrap();

// repeat_packed / extend_packed: 紧凑排列（无填充）
let packed = Layout::new::<u8>().repeat_packed(100);
let combined = Layout::new::<u32>().extend_packed(Layout::new::<u8>()).unwrap();
```

> 详见 [Rust 1.95 新特性 - Layout API](../06_ecosystem/emerging/rust_1_95.md)

---

## 📖 延伸阅读

### 必读资料

1. [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Rust 不安全代码权威指南
2. [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) - 官方 unsafe 代码指南
3. [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) - Rust 别名模型论文
4. [Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) - 下一代别名模型

### 审计工具

- [cargo-geiger](https://github.com/rust-secure-code/cargo-geiger) - 不安全代码统计
- [Miri](https://github.com/rust-lang/miri) - Rust 解释器与 UB 检测
- [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz) - Fuzzing 框架
- [cargo-audit](https://github.com/RustSec/cargo-audit) - 依赖安全审计

### 案例研究

- [RustSec 公告数据库](https://rustsec.org/) - 真实安全漏洞案例
- [Safety Dance](https://github.com/rust-secure-code/safety-dance) - 移除 unsafe 代码的倡议
- [Rust Safety Critical Consortium](https://rrsa.rs/) - 安全关键 Rust 实践

---

## 📖 权威来源与延伸阅读

### 官方文档（一级来源）

- [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html) —— `unsafe` 块的精确语义
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) —— 不安全 Rust 的高级教程
- [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) —— UB 边界与内存模型官方指南
- [Miri 文档](https://github.com/rust-lang/miri) —— 解释执行与 UB 检测工具

### 学术来源（一级来源）

- **Ralf Jung et al., "Stacked Borrows: An Aliasing Model for Rust"**, *POPL 2021* —— Miri 的内存模型基础。
- **Ralf Jung, "Tree Borrows: Or, How I Learned to Stop Worrying and Love the Alias"**, *arXiv 2023* —— 下一代 Miri 内存模型。
- **RustBelt: POPL 2018** —— Safe Rust 内存安全的形式化验证。

### 社区权威（二级来源）

- **Ralf Jung 博客**: <https://www.ralfj.de/blog/> —— 内存模型、Miri、unsafe 边界的深度分析
- **Rust Secure Code WG**: <https://github.com/rust-secure-code/wg> —— 安全编码指南与工具链

---

> 💡 **核心原则**: 每一行 `unsafe` 代码都必须能够被证明是安全的，且这种证明应该对审阅者显而易见。

---

> **权威来源**: [Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/), [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/), [Miri](https://github.com/rust-lang/miri)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、Rustonomicon、Unsafe Code Guidelines、Miri、Ralf Jung） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

*贡献者: Rust 中文知识库维护团队*
