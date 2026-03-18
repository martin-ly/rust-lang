# Unsafe Rust - 不安全 Rust

> **⚠️ 警告**: 本章节涉及 Rust 的最底层特性。Unsafe Rust 赋予你强大的能力，同时也要求你承担维护内存安全的责任。

**预计学习时间**: 90-120 分钟
**难度级别**: 高级 (Advanced)
**前置知识**: 精通所有权、生命周期、原始指针基础

---

## 🎯 学习目标

完成本章节后，你将能够：

1. **理解** `unsafe` 的确切含义及其在 Rust 安全模型中的位置
2. **掌握** 五种只能在 `unsafe` 上下文中执行的操作
3. **区分** `unsafe fn` 和 `unsafe` 块的不同使用场景
4. **安全地** 使用原始指针进行底层内存操作
5. **编写** 带有完整安全文档的不安全代码
6. **识别** 常见的 unsafe 代码陷阱并避免它们

---

## 📋 先决条件

- ✅ **所有权系统**: 移动语义、借用规则、生命周期
- ✅ **智能指针**: `Box<T>`, `Rc<T>`, `Arc<T>`, `RefCell<T>`
- ✅ **trait 系统**: 泛型、trait bounds
- ✅ **内存布局**: 栈与堆、内存对齐

---

## 🧠 核心概念

### 什么是 Unsafe Rust

Unsafe Rust 是 Rust 语言的一个**子集**，它允许你执行编译器无法完全验证安全性的操作：

> **Unsafe Rust 并不意味着代码一定危险。它只是意味着编译器无法自动保证内存安全——这个责任现在落到了程序员身上。**

```rust
unsafe {
    // 在这里可以执行不安全操作
}
```

---

### Unsafe 能做什么 (5种能力)

| 能力 | 描述 | 典型用例 |
|------|------|----------|
| **1. 解引用原始指针** | 访问 `*const T` / `*mut T` 指向的数据 | 与 C 库交互 |
| **2. 调用 unsafe 函数** | 调用 `unsafe fn` | FFI 调用 |
| **3. 实现 unsafe trait** | 实现 `unsafe trait` | 自定义同步原语 |
| **4. 访问 mutable static** | 读写 `static mut` | 全局状态（极少使用）|
| **5. 访问 union 字段** | 读取 union 字段 | 与 C 代码交互 |

```rust
static mut COUNTER: u32 = 0;
union IntOrFloat { i: i32, f: f32 }
unsafe trait DangerousTrait { fn method(&self); }
unsafe fn dangerous(ptr: *const i32) -> i32 { *ptr }

fn demo() {
    let x = 42;
    let ptr = &x as *const i32;
    unsafe {
        let _ = *ptr;                    // 1. 解引用原始指针
        let _ = dangerous(ptr);          // 2. 调用 unsafe 函数
        COUNTER += 1;                    // 4. 修改 static mut
        let u = IntOrFloat { i: 42 };
        let _ = u.f;                     // 5. 访问 union
    }
}
struct MyType;
unsafe impl DangerousTrait for MyType { fn method(&self) {} } // 3.
```

---

### `unsafe fn` 与 `unsafe` 块的区别

#### `unsafe fn` - 定义不安全函数

```rust
/// # Safety
/// - `ptr` 必须是非空有效指针
/// - `ptr` 必须正确对齐
unsafe fn read_value(ptr: *const i32) -> i32 { *ptr }
```

- **含义**: 函数包含编译器无法验证安全的操作
- **责任**: **调用者**必须确保满足安全前置条件
- **文档**: 必须包含 `# Safety` 章节

#### `unsafe` 块 - 执行不安全操作

```rust
fn safe_wrapper(ptr: *const i32) -> Option<i32> {
    if ptr.is_null() { return None; }
    // SAFETY: 已检查 ptr 不是 null
    unsafe { Some(*ptr) }
}
```

- **含义**: 块内可以执行不安全操作
- **责任**: **作者**必须确保内部操作的安全性
- **文档**: 使用 `// SAFETY:` 注释

---

### 原始指针 (Raw Pointers)

#### 原始指针 vs 引用

| 特性 | 引用 `&T` | 原始指针 `*const T` |
|------|-----------|---------------------|
| 生命周期检查 | ✅ 是 | ❌ 否 |
| 自动解引用 | ✅ 是 | ❌ 需 unsafe |
| 可为 null | ❌ 否 | ✅ 可以 |
| 别名规则 | ✅ 严格执行 | ❌ 不检查 |
| 算术运算 | ❌ 否 | ✅ 可以 |

#### 原始指针的使用

```rust
fn raw_pointer_demo() {
    let mut num = 5;
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;

    // 安全操作
    if r1.is_null() { }

    unsafe {
        // SAFETY: 指针来自有效引用
        println!("{}", *r1);
        *r2 = 10;
    }
}
```

#### 原始指针算术

```rust
fn pointer_arithmetic() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();

    unsafe {
        assert_eq!(*ptr, 1);
        assert_eq!(*ptr.add(1), 2);
        // ptr.add(100) 是未定义行为，即使不解引用！
    }
}
```

---

### 调用 Unsafe 函数

```rust
use std::slice;

/// # Safety
/// - `bytes` 长度必须是 4 的倍数
/// - `bytes` 必须正确对齐到 4 字节
unsafe fn bytes_to_i32s(bytes: &[u8]) -> &[i32] {
    slice::from_raw_parts(bytes.as_ptr() as *const i32, bytes.len() / 4)
}

fn safe_wrapper(bytes: &[u8]) -> Option<&[i32]> {
    if bytes.len() % 4 != 0 || bytes.as_ptr() as usize % 4 != 0 {
        return None;
    }
    Some(unsafe { bytes_to_i32s(bytes) })  // SAFETY: 已验证
}
```

#### FFI 调用示例

```rust
extern "C" { fn strlen(s: *const u8) -> usize; }

use std::ffi::CStr;
fn get_len(c_str: &CStr) -> usize {
    // SAFETY: CStr 保证包含有效的 null 结尾字符串
    unsafe { strlen(c_str.as_ptr()) }
}
```

---

### 实现 Unsafe Trait

```rust
use std::marker::PhantomData;

/// # Safety: 实现者必须保证线程安全
unsafe trait MySend {}

struct MyType { data: *mut u8, _m: PhantomData<*mut u8> }

// SAFETY: 指针实际由 C 库管理
unsafe impl MySend for MyType {}
```

---

### 访问/修改可变静态变量

```rust
static mut GLOBAL: u64 = 0;

fn increment() {
    unsafe { GLOBAL += 1; }  // SAFETY: 单线程程序
}

// 更好的替代方案
use std::sync::atomic::{AtomicU64, Ordering};
static GLOBAL_SAFE: AtomicU64 = AtomicU64::new(0);
fn increment_safe() {
    GLOBAL_SAFE.fetch_add(1, Ordering::SeqCst);  // 无需 unsafe
}
```

> **最佳实践**: 尽量避免 `static mut`，使用原子类型或同步原语。

---

### 使用 Union

```rust
union Value {
    int: i32,
    float: f32,
    bytes: [u8; 4],
}

fn union_demo() {
    let mut v = Value { int: 42 };
    unsafe {
        println!("{}", v.int);  // SAFETY: 刚用 int 初始化
        v.float = 3.14;
        // 现在读取 v.int 合法但值未定义！
    }
}
```

---

### Unsafe 的不变量契约

#### 内存安全不变量

```rust
// ✅ 正确
unsafe { let _ = Box::from_raw(ptr); }  // ptr 来自 Box::into_raw

// ❌ 错误：双重释放
unsafe {
    let ptr = Box::into_raw(Box::new(42));
    drop(Box::from_raw(ptr));
    drop(Box::from_raw(ptr));  // UB!
}
```

#### 类型安全不变量

```rust
// ✅ 正确
use std::mem::MaybeUninit;
let _ = MaybeUninit::<i32>::uninit();

// ❌ 错误：未初始化值
let _: i32 = unsafe { MaybeUninit::uninit().assume_init() };  // UB!
```

#### 别名规则不变量

```rust
// ❌ 错误
let mut x = 42;
let ptr = &mut x as *mut i32;
let _ref = &x;
unsafe { *ptr = 0; }  // 同时存在引用和原始指针访问！
```

---

## 💡 最佳实践

### 1. 最小化 unsafe 范围

```rust
fn example(data: &[u8]) -> &[u8] {
    let (ptr, len) = (data.as_ptr(), data.len());
    unsafe { std::slice::from_raw_parts(ptr, len) }
}
```

### 2. 编写安全文档

```rust
/// # Safety
/// - `ptr` 指向有效的 UTF-8 字符串
/// - `capacity` >= `length`
unsafe fn string_from_parts(ptr: *mut u8, len: usize, cap: usize) -> String {
    String::from_raw_parts(ptr, len, cap)
}
```

### 3. 封装 unsafe，提供安全 API

```rust
pub struct SafeBuffer {
    ptr: *mut u8,
    cap: usize,
}

impl SafeBuffer {
    pub fn new(cap: usize) -> Option<Self> {
        if cap == 0 { return None; }
        let layout = std::alloc::Layout::array::<u8>(cap).ok()?;
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() { return None; }
        Some(Self { ptr, cap })
    }

    pub fn get(&self, idx: usize) -> Option<u8> {
        if idx >= self.cap { return None; }
        Some(unsafe { *self.ptr.add(idx) })
    }
}

impl Drop for SafeBuffer {
    fn drop(&mut self) {
        let layout = std::alloc::Layout::array::<u8>(self.cap).unwrap();
        unsafe { std::alloc::dealloc(self.ptr, layout) };
    }
}
```

### 4. 使用 `// SAFETY:` 注释

```rust
unsafe {
    // SAFETY: ptr 非 null、正确对齐、指向已初始化内存
    *ptr = value;
}
```

---

## ⚠️ 常见陷阱

### 1. 悬垂指针

```rust
// ❌ 错误
fn dangling() -> *const i32 {
    let x = 42;
    &x as *const i32  // x 在返回时被释放
}

// ✅ 正确
fn valid() -> Box<i32> { Box::new(42) }
```

### 2. 未初始化内存

```rust
// ❌ 错误
let _: i32 = unsafe { std::mem::uninitialized() };  // UB!

// ✅ 正确
let _ = std::mem::MaybeUninit::<i32>::uninit();
```

### 3. 违反别名规则

```rust
let mut x = 5;
let raw = &mut x as *mut i32;
unsafe {
    *raw = 10;
    println!("{}", x);  // ❌ 同时使用引用和原始指针
}
```

### 4. 错误使用 `from_raw_parts`

```rust
// ❌ 错误：无效地址或长度
let _ = unsafe { std::slice::from_raw_parts(0x1 as *const u8, 1000000) };
```

### 5. 数据竞争

```rust
static mut COUNTER: i32 = 0;
// ❌ 错误：无同步的多线程访问
std::thread::spawn(|| unsafe { COUNTER += 1 });

// ✅ 正确：使用原子操作
use std::sync::atomic::{AtomicI32, Ordering};
static SAFE: AtomicI32 = AtomicI32::new(0);
```

---

## 🎮 动手练习

### 练习 1: 安全的原始指针包装器

```rust
pub struct Unique<T> {
    ptr: *mut T,
    _marker: std::marker::PhantomData<T>,
}

impl<T> Unique<T> {
    pub fn new(value: T) -> Self {
        Self { ptr: Box::into_raw(Box::new(value)), _marker: std::marker::PhantomData }
    }
    pub fn get(&self) -> &T { todo!() }
    pub fn get_mut(&mut self) -> &mut T { todo!() }
}
impl<T> Drop for Unique<T> {
    fn drop(&mut self) { todo!() }
}
```

### 练习 2: 找出问题

```rust
unsafe fn problematic(ptr: *mut i32, offset: isize) -> i32 {
    *ptr.offset(offset)
}
```

<details>
<summary>答案</summary>

1. 未检查 `ptr` 是否为 null
2. 未验证偏移量范围
3. 缺少 `# Safety` 文档
4. 缺少 `SAFETY` 注释

</details>

---

## 📖 延伸阅读

- **The Rustonomicon**: <https://doc.rust-lang.org/nomicon/>
- **Rust Book - Unsafe**: <https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html>
- **Rust Reference - UB**: <https://doc.rust-lang.org/reference/behavior-considered-undefined.html>
- **Miri**: `cargo +nightly miri test`
- **案例**: `Vec<T>` 源码, `hashbrown` crate

---

## 总结

**关键原则**：

> 1. 尽可能使用安全 Rust
> 2. 封装 unsafe，提供安全 API
> 3. 文档化安全前提 (`# Safety`)
> 4. 内联解释安全原因 (`// SAFETY:`)
> 5. 使用 Miri 测试

**Unsafe Rust 不是 inherently 危险的**。只要你严格维护安全不变量，unsafe 代码可以和 safe 代码一样可靠。
