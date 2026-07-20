# repr(packed) 安全注意事项

## 📋 目录

- [repr(packed) 安全注意事项](#reprpacked-安全注意事项)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [⚠️ 核心危险](#️-核心危险)
  - [内存对齐基础](#内存对齐基础)
    - [什么是内存对齐？](#什么是内存对齐)
    - [为什么需要对齐？](#为什么需要对齐)
    - [默认结构体布局](#默认结构体布局)
  - [repr(packed) 详解](#reprpacked-详解)
    - [基本语法](#基本语法)
    - [内存布局对比](#内存布局对比)
    - [repr(packed(N)) - 指定对齐](#reprpackedn---指定对齐)
  - [未对齐引用的 UB 问题](#未对齐引用的-ub-问题)
    - [为什么未对齐引用是 UB？](#为什么未对齐引用是-ub)
    - [❌ 错误示例](#-错误示例)
    - [Rust 1.90 的改进](#rust-190-的改进)
  - [安全使用方法](#安全使用方法)
    - [方法 1: 按值复制 ✅ 推荐](#方法-1-按值复制--推荐)
    - [方法 2: ptr::read\_unaligned ✅](#方法-2-ptrread_unaligned-)
    - [方法 3: 使用辅助库 ✅ 最佳实践](#方法-3-使用辅助库--最佳实践)
  - [常见陷阱](#常见陷阱)
    - [陷阱 1: 隐式引用创建](#陷阱-1-隐式引用创建)
    - [陷阱 2: 模式匹配](#陷阱-2-模式匹配)
    - [陷阱 3: 泛型函数](#陷阱-3-泛型函数)
    - [陷阱 4: 嵌套结构](#陷阱-4-嵌套结构)
  - [最佳实践](#最佳实践)
    - [1. 优先使用 repr(C) 而非 packed](#1-优先使用-reprc-而非-packed)
    - [2. 使用辅助库](#2-使用辅助库)
    - [3. 封装访问方法](#3-封装访问方法)
    - [4. 使用 MaybeUninit 处理未初始化](#4-使用-maybeuninit-处理未初始化)
    - [5. 文档化警告](#5-文档化警告)
  - [实战示例](#实战示例)
    - [示例 1: 网络协议解析](#示例-1-网络协议解析)
    - [示例 2: 文件格式读取](#示例-2-文件格式读取)
    - [示例 3: FFI 数据交换](#示例-3-ffi-数据交换)
  - [📊 性能对比](#-性能对比)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [推荐库](#推荐库)
    - [相关文档](#相关文档)

---

## 概述

`#[repr(packed)]` 是 Rust 提供的一个强大但危险的特性，它会移除结构体字段的对齐填充，使数据按字节紧凑排列。这在 FFI、网络协议、文件格式解析等场景中很有用，但如果使用不当会导致**未定义行为 (UB)**。

### ⚠️ 核心危险

**直接获取 packed 字段的引用可能导致未对齐引用，这是 UB！**

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,  // ⚠️ 可能未对齐
}

let p = Packed { a: 1, b: 2 };
let ptr = &p.b;  // ❌ UB! 可能创建未对齐引用
```

---

## 内存对齐基础

### 什么是内存对齐？

**内存对齐**是指数据在内存中的存储位置必须是其类型大小的倍数。

```text
对齐要求:
- u8:  对齐到 1 字节边界
- u16: 对齐到 2 字节边界
- u32: 对齐到 4 字节边界
- u64: 对齐到 8 字节边界
```

### 为什么需要对齐？

1. **性能**: 现代 CPU 访问对齐的数据更快
2. **硬件要求**: 某些 CPU 架构不支持未对齐访问
3. **原子操作**: 原子操作通常要求对齐的地址

### 默认结构体布局

```rust
// 默认布局 (repr(Rust))
struct Normal {
    a: u8,      // offset: 0, size: 1
    // padding: 3 bytes
    b: u32,     // offset: 4, size: 4
    c: u16,     // offset: 8, size: 2
    // padding: 6 bytes (for alignment to 8)
}

// 总大小: 16 bytes (包含填充)
assert_eq!(std::mem::size_of::<Normal>(), 16);
```

**内存布局可视化**:

```text
Offset: 0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15
Data:  [a][·][·][·][b  b  b  b][c  c][·][·][·][·][·][·]
        ^  padding  ^           ^     padding           ^
```

---

## repr(packed) 详解

### 基本语法

```rust
// 移除所有填充
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

// 指定对齐值
#[repr(packed(2))]  // 对齐到 2 字节
struct PackedAlign2 {
    a: u8,
    b: u32,
}
```

### 内存布局对比

```rust
// repr(packed) - 无填充
#[repr(packed)]
struct Packed {
    a: u8,      // offset: 0, size: 1
    b: u32,     // offset: 1, size: 4 ⚠️ 未对齐!
    c: u16,     // offset: 5, size: 2
}

// 总大小: 7 bytes (无填充)
assert_eq!(std::mem::size_of::<Packed>(), 7);
```

**内存布局可视化**:

```text
Offset: 0  1  2  3  4  5  6
Data:  [a][b  b  b  b][c  c]
        ^  ^           ^
        1  未对齐!     未对齐!
```

### repr(packed(N)) - 指定对齐

```rust
#[repr(packed(2))]
struct PackedAlign2 {
    a: u8,      // offset: 0
    // padding: 1 byte (对齐到 2)
    b: u32,     // offset: 2
    c: u16,     // offset: 6
}

// 总大小: 8 bytes
assert_eq!(std::mem::size_of::<PackedAlign2>(), 8);
```

**内存布局**:

```text
Offset: 0  1  2  3  4  5  6  7
Data:  [a][·][b  b  b  b][c  c]
        ^  ^  ^           ^
           2字节对齐
```

---

## 未对齐引用的 UB 问题

### 为什么未对齐引用是 UB？

Rust 的引用类型 `&T` 和 `&mut T` **保证**指向的数据是正确对齐的。创建未对齐引用违反了这个不变量，导致 UB。

### ❌ 错误示例

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

fn unsafe_access() {
    let p = Packed { a: 1, b: 0x12345678 };
    
    // ❌ UB! 创建未对齐引用
    let b_ref: &u32 = &p.b;
    println!("{}", b_ref);
    
    // ❌ UB! 隐式创建引用
    let value = p.b;  // 编译器可能创建临时引用
}
```

### Rust 1.90 的改进

Rust 1.90 增强了对未对齐引用的检测：

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

fn check() {
    let p = Packed { a: 1, b: 2 };
    
    // ⚠️ 编译器警告
    let x = &p.b;  // warning: reference to packed field
    
    // ✅ Rust 1.90 允许，但需要 unsafe
    let x = unsafe { &p.b };  // 明确标记
}
```

---

## 安全使用方法

### 方法 1: 按值复制 ✅ 推荐

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

impl Packed {
    // ✅ 安全: 按值返回
    fn get_b(&self) -> u32 {
        self.b  // 编译器生成安全的复制代码
    }
    
    // ✅ 安全: 按值设置
    fn set_b(&mut self, value: u32) {
        self.b = value;
    }
}

fn safe_usage() {
    let mut p = Packed { a: 1, b: 2, c: 3 };
    
    // ✅ 安全操作
    let b_value = p.get_b();
    p.set_b(42);
    
    println!("b = {}", b_value);
}
```

### 方法 2: ptr::read_unaligned ✅

```rust
use std::ptr;

#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

impl Packed {
    // ✅ 使用 read_unaligned
    fn read_b(&self) -> u32 {
        unsafe {
            ptr::read_unaligned(&self.b as *const u32)
        }
    }
    
    // ✅ 使用 write_unaligned
    fn write_b(&mut self, value: u32) {
        unsafe {
            ptr::write_unaligned(&mut self.b as *mut u32, value);
        }
    }
}
```

### 方法 3: 使用辅助库 ✅ 最佳实践

```toml
# Cargo.toml
[dependencies]
bytemuck = "1.14"
zerocopy = "0.7"
```

```rust
use bytemuck::{Pod, Zeroable};

#[repr(packed)]
#[derive(Copy, Clone, Pod, Zeroable)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

fn use_with_bytemuck() {
    let bytes = [1u8, 0, 0, 0, 42, 0, 1, 0];
    
    // ✅ 安全: bytemuck 处理对齐问题
    let p: &Packed = bytemuck::from_bytes(&bytes[..7]);
    
    // ✅ 按值读取
    let b = p.b;
    println!("b = {}", b);
}
```

---

## 常见陷阱

### 陷阱 1: 隐式引用创建

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

// ❌ 陷阱: 方法调用可能创建引用
impl Packed {
    fn process_b(&self) {
        // ❌ 这可能创建临时引用
        some_function(&self.b);
    }
}

// ✅ 正确方式
impl Packed {
    fn process_b(&self) {
        // ✅ 先复制值
        let b_copy = self.b;
        some_function(&b_copy);
    }
}
```

### 陷阱 2: 模式匹配

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

// ❌ 模式匹配可能创建引用
fn match_field(p: &Packed) {
    match p.b {  // ⚠️ 可能有问题
        0 => println!("zero"),
        _ => println!("non-zero"),
    }
}

// ✅ 正确方式
fn match_field_safe(p: &Packed) {
    let b = p.b;  // 先复制
    match b {
        0 => println!("zero"),
        _ => println!("non-zero"),
    }
}
```

### 陷阱 3: 泛型函数

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

// ❌ 泛型函数可能创建引用
fn print<T: std::fmt::Display>(value: &T) {
    println!("{}", value);
}

fn use_generic(p: &Packed) {
    // ❌ UB!
    print(&p.b);
}

// ✅ 正确方式
fn use_generic_safe(p: &Packed) {
    let b = p.b;
    print(&b);
}
```

### 陷阱 4: 嵌套结构

```rust
#[repr(packed)]
struct Inner {
    x: u32,
}

#[repr(packed)]
struct Outer {
    a: u8,
    inner: Inner,  // ⚠️ 嵌套的 packed 结构
}

fn access_nested(o: &Outer) {
    // ❌ UB! 双重未对齐
    let x_ref = &o.inner.x;
    
    // ✅ 正确
    let inner_copy = o.inner;
    let x = inner_copy.x;
}
```

---

## 最佳实践

### 1. 优先使用 repr(C) 而非 packed

```rust
// ✅ 推荐: 使用 repr(C) 获得可预测的布局
#[repr(C)]
struct Protocol {
    header: u8,
    length: u16,
    data: u32,
}

// ⚠️ 仅在必要时使用 packed
#[repr(packed)]
struct CompactProtocol {
    header: u8,
    length: u16,
    data: u32,
}
```

### 2. 使用辅助库

```rust
use bytemuck::{Pod, Zeroable};

// ✅ bytemuck 提供安全抽象
#[repr(C)]
#[derive(Copy, Clone, Pod, Zeroable)]
struct SafeProtocol {
    header: u8,
    _pad: [u8; 3],  // 手动填充
    length: u32,
}
```

### 3. 封装访问方法

```rust
#[repr(packed)]
pub struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

impl Packed {
    // ✅ 提供安全的访问接口
    pub fn a(&self) -> u8 { self.a }
    pub fn b(&self) -> u32 { self.b }
    pub fn c(&self) -> u16 { self.c }
    
    pub fn set_a(&mut self, v: u8) { self.a = v; }
    pub fn set_b(&mut self, v: u32) { self.b = v; }
    pub fn set_c(&mut self, v: u16) { self.c = v; }
}
```

### 4. 使用 MaybeUninit 处理未初始化

```rust
use std::mem::MaybeUninit;

#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
}

fn safe_init() -> Packed {
    let mut buf = MaybeUninit::<Packed>::uninit();
    
    unsafe {
        let ptr = buf.as_mut_ptr();
        std::ptr::addr_of_mut!((*ptr).a).write(1);
        std::ptr::addr_of_mut!((*ptr).b).write_unaligned(42);
        buf.assume_init()
    }
}
```

### 5. 文档化警告

```rust
/// ⚠️ WARNING: This struct uses `repr(packed)`.
/// 
/// # Safety
/// 
/// Never take references to fields! Always copy values.
/// 
/// ```
/// let p = Packed { ... };
/// let value = p.b;  // ✅ OK
/// let ref_b = &p.b; // ❌ UB!
/// ```
#[repr(packed)]
pub struct Packed {
    pub a: u8,
    pub b: u32,
}
```

---

## 实战示例

### 示例 1: 网络协议解析

```rust
use bytemuck::{Pod, Zeroable};

// 网络数据包头部 (固定 8 字节)
#[repr(packed)]
#[derive(Copy, Clone, Pod, Zeroable)]
struct PacketHeader {
    magic: u16,      // 2 bytes
    version: u8,     // 1 byte
    flags: u8,       // 1 byte
    length: u32,     // 4 bytes
}

impl PacketHeader {
    /// 从字节流解析
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < std::mem::size_of::<Self>() {
            return None;
        }
        Some(*bytemuck::from_bytes(&bytes[..8]))
    }
    
    /// 安全访问字段
    pub fn magic(&self) -> u16 { self.magic }
    pub fn version(&self) -> u8 { self.version }
    pub fn flags(&self) -> u8 { self.flags }
    pub fn length(&self) -> u32 { self.length }
    
    /// 验证魔数
    pub fn is_valid(&self) -> bool {
        self.magic() == 0x1234
    }
}

fn parse_packet(data: &[u8]) {
    if let Some(header) = PacketHeader::from_bytes(data) {
        if header.is_valid() {
            println!("Version: {}", header.version());
            println!("Length: {}", header.length());
        }
    }
}
```

### 示例 2: 文件格式读取

```rust
use std::fs::File;
use std::io::{self, Read};

#[repr(packed)]
#[derive(Copy, Clone)]
struct BitmapFileHeader {
    signature: [u8; 2],  // "BM"
    file_size: u32,
    reserved: u32,
    data_offset: u32,
}

impl BitmapFileHeader {
    fn from_file(file: &mut File) -> io::Result<Self> {
        let mut buffer = [0u8; 14];
        file.read_exact(&mut buffer)?;
        
        unsafe {
            // ✅ 使用 ptr::read_unaligned
            Ok(std::ptr::read_unaligned(buffer.as_ptr() as *const Self))
        }
    }
    
    fn signature(&self) -> &[u8; 2] {
        &self.signature
    }
    
    fn file_size(&self) -> u32 {
        // ✅ 按值返回
        self.file_size
    }
    
    fn data_offset(&self) -> u32 {
        self.data_offset
    }
}
```

### 示例 3: FFI 数据交换

```rust
// C 结构体 (紧凑布局)
// struct CData {
//     uint8_t type;
//     uint32_t value;
//     uint16_t checksum;
// };

#[repr(packed)]
struct CData {
    type_: u8,
    value: u32,
    checksum: u16,
}

extern "C" {
    fn process_c_data(data: *const CData) -> i32;
}

impl CData {
    fn new(type_: u8, value: u32) -> Self {
        let mut data = Self {
            type_,
            value,
            checksum: 0,
        };
        data.checksum = data.calculate_checksum();
        data
    }
    
    fn calculate_checksum(&self) -> u16 {
        // ✅ 按值读取
        let type_val = self.type_ as u16;
        let value_val = self.value;
        (type_val ^ (value_val as u16)) & 0xFFFF
    }
    
    unsafe fn send_to_c(&self) -> i32 {
        process_c_data(self as *const Self)
    }
}
```

---

## 📊 性能对比

```rust
use std::time::Instant;

#[repr(C)]
struct Normal {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

fn benchmark() {
    let normal = Normal { a: 1, b: 2, c: 3 };
    let packed = Packed { a: 1, b: 2, c: 3 };
    
    // 对齐访问 - 快速
    let start = Instant::now();
    for _ in 0..1_000_000 {
        let _ = normal.b;
    }
    println!("Normal: {:?}", start.elapsed());
    
    // 未对齐访问 - 可能较慢
    let start = Instant::now();
    for _ in 0..1_000_000 {
        let _ = packed.b;
    }
    println!("Packed: {:?}", start.elapsed());
}
```

**性能影响**:

- x86_64: 未对齐访问可能慢 2-3 倍
- ARM: 某些架构不支持未对齐访问（会崩溃）
- 空间节省: 通常能减少 10-30% 的内存占用

---

## 🔗 相关资源

### 官方文档

- [Rust Reference - Type Layout](https://doc.rust-lang.org/reference/type-layout.html)
- [Rustonomicon - repr(Rust)](https://doc.rust-lang.org/nomicon/other-reprs.html)

### 推荐库

- [bytemuck](https://docs.rs/bytemuck/) - 类型安全的字节转换
- [zerocopy](https://docs.rs/zerocopy/) - 零复制序列化
- [packed_struct](https://docs.rs/packed_struct/) - 声明式打包结构

### 相关文档

- [内存安全](./01_memory_safety.md)
- [类型安全](./02_type_safety.md)
- [FFI/ABI 与 repr](./ffi_abi_repr.md)

---

**维护状态**: 🟢 活跃维护中  
**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

*示例与测试：见 `examples/repr_packed_safety.rs` 与 `tests/repr_packed_safety_tests.rs`* 🦀
