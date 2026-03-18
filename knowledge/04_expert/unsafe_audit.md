# Unsafe Code Auditing (不安全代码审计)

> 学习如何在生产环境中审计和验证 `unsafe` Rust 代码的安全性，掌握系统级的代码审查技能与工具链。
>
> **难度**: Expert ⭐⭐⭐⭐⭐
> **预计学习时间**: 6-8 小时
> **适用场景**: 安全关键系统审计、开源代码审查、unsafe 代码重构

---

## 🎯 学习目标

完成本章学习后，你将能够：

- ✅ 建立系统化的 `unsafe` 代码审计流程
- ✅ 识别常见的 unsoundness 模式与安全隐患
- ✅ 使用 Miri 验证代码的未定义行为
- ✅ 运用 Fuzzing 技术发现边界安全问题
- ✅ 编写清晰、可验证的 Safety 文档
- ✅ 使用专业工具辅助安全审计

---

## 📋 先决条件

在开始学习本章之前，请确保你已掌握：

- [Unsafe Rust](../02_intermediate/unsafe_rust.md) - 深入理解 `unsafe` 块、裸指针、FFI
- [内存模型与布局](../03_advanced/memory_model.md) - 理解 Rust 的内存模型
- [FFI 与外部调用](../03_advanced/ffi_bindings.md) - 了解 C 互操作基础
- [生命周期与借用检查](../../guides/ownership_lifetime.md) - 掌握生命周期系统

**推荐工具准备**:

```bash
# 安装审计工具链
cargo install cargo-geiger
cargo install cargo-fuzz
cargo install cargo-san
cargo install miri  # 或 rustup component add miri
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

### 常见 Unsoundness 模式

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

#### 2. 未初始化内存读取

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

#### 3. 类型混淆 (Type Confusion)

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

#### 4. Send/Sync 错误实现

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

> 💡 **核心原则**: 每一行 `unsafe` 代码都必须能够被证明是安全的，且这种证明应该对审阅者显而易见。

---

*最后更新: 2026-03-19*
*贡献者: Rust 中文知识库维护团队*
