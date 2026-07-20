# Rust 1.82.0 &raw 指针操作符深度分析


## 📊 目录

- [Rust 1.82.0 \&raw 指针操作符深度分析](#rust-1820-raw-指针操作符深度分析)
  - [📊 目录](#-目录)
  - [1. 特性概览与历史演进](#1-特性概览与历史演进)
    - [1.1 原始指针操作的演进历程](#11-原始指针操作的演进历程)
    - [1.2 技术架构分析](#12-技术架构分析)
      - [1.2.1 语法语义设计](#121-语法语义设计)
      - [1.2.2 编译器实现机制](#122-编译器实现机制)
  - [2. 形式化内存模型分析](#2-形式化内存模型分析)
    - [2.1 地址计算语义](#21-地址计算语义)
      - [2.1.1 数学模型定义](#211-数学模型定义)
    - [2.2 内存安全性模型](#22-内存安全性模型)
      - [2.2.1 安全性不变量](#221-安全性不变量)
    - [2.3 内存布局兼容性](#23-内存布局兼容性)
      - [2.3.1 对齐敏感分析](#231-对齐敏感分析)
  - [3. 编译器实现机制深度剖析](#3-编译器实现机制深度剖析)
    - [3.1 HIR到MIR的降级过程](#31-hir到mir的降级过程)
      - [3.1.1 AST转换流程](#311-ast转换流程)
      - [3.1.2 MIR生成优化](#312-mir生成优化)
    - [3.2 LLVM IR生成策略](#32-llvm-ir生成策略)
      - [3.2.1 优化的代码生成](#321-优化的代码生成)
      - [3.2.2 性能优化分析](#322-性能优化分析)
  - [4. 实际应用场景与最佳实践](#4-实际应用场景与最佳实践)
    - [4.1 FFI边界安全操作](#41-ffi边界安全操作)
      - [4.1.1 C结构体互操作](#411-c结构体互操作)
      - [4.1.2 内存映射文件操作](#412-内存映射文件操作)
    - [4.2 高性能数据结构实现](#42-高性能数据结构实现)
      - [4.2.1 自定义内存分配器](#421-自定义内存分配器)
    - [4.3 嵌入式系统内存操作](#43-嵌入式系统内存操作)
      - [4.3.1 硬件寄存器映射](#431-硬件寄存器映射)


**特性版本**: Rust 1.82.0 (2024-10-17稳定化)
**重要性等级**: ⭐⭐⭐⭐⭐ (系统编程基础设施)
**影响范围**: 不安全代码、FFI、内存布局、性能优化
**技术深度**: 🔒 内存安全 + ⚡ 零开销 + 🔧 系统级编程

---

## 1. 特性概览与历史演进

### 1.1 原始指针操作的演进历程

Rust 1.82.0引入的`&raw`操作符解决了长期存在的未定义行为风险：

**传统问题**:

```rust
// 问题1: 通过引用创建原始指针可能触发UB
#[repr(C)]
struct PackedStruct {
    a: u8,
    b: u32,  // 可能未对齐
}

let s = PackedStruct { a: 1, b: 2 };
let ptr = &s.b as *const u32;  // 潜在UB：创建未对齐引用
```

**革命性解决方案**:

```rust
// &raw直接创建原始指针，避免中间引用
let s = PackedStruct { a: 1, b: 2 };
let ptr = &raw const s.b;  // 安全：直接获取原始指针
let ptr_mut = &raw mut s.b;  // 可变版本
```

### 1.2 技术架构分析

#### 1.2.1 语法语义设计

```mathematical
Raw指针操作符语法:

&raw const PLACE_EXPR → *const T
&raw mut PLACE_EXPR → *mut T

语义约束:
1. PLACE_EXPR必须是有效的place表达式
2. 不创建中间引用，直接计算地址
3. 绕过借用检查器的对齐要求
4. 保持原始的内存布局语义
```

#### 1.2.2 编译器实现机制

```rust
// HIR (High-level IR) 表示
#[derive(Debug, Clone)]
pub enum ExprKind {
    // 现有变体...
    AddressOf {
        mutability: Mutability,
        arg: ExprId,
    },
}

// MIR (Mid-level IR) 降级
impl<'tcx> Builder<'_, 'tcx> {
    fn expr_as_rvalue(&mut self, block: BasicBlock, expr: &Expr<'tcx>) -> Rvalue<'tcx> {
        match expr.kind {
            ExprKind::AddressOf { mutability, arg } => {
                let place = self.expr_as_place(block, arg);
                Rvalue::AddressOf(mutability, place)
            }
            // 其他情况...
        }
    }
}
```

---

## 2. 形式化内存模型分析

### 2.1 地址计算语义

#### 2.1.1 数学模型定义

**定义1 (地址计算函数)**:

```mathematical
设内存模型 M = (Locations, Values, Layout)

地址计算函数: addr: PlaceExpr → MemoryAddress

对于 &raw const place_expr:
addr(place_expr) = base_addr + offset(field_path)

其中:
- base_addr ∈ Locations
- offset: FieldPath → ℕ (字节偏移)
- 无对齐要求约束
```

**定理1 (地址计算确定性)**:

```mathematical
∀ place_expr P, ∀ 程序状态 S₁, S₂:
layout_compatible(S₁, S₂) ⟹ addr_S₁(P) = addr_S₂(P)

证明:
1. &raw仅依赖内存布局，不依赖值
2. 相同布局保证相同偏移计算
3. 地址计算是纯函数，无副作用
∴ 地址计算具有确定性 ∎
```

### 2.2 内存安全性模型

#### 2.2.1 安全性不变量

**定理2 (引用创建安全性)**:

```mathematical
∀ 内存位置 loc, ∀ 类型 T:
safe(&raw const loc) ⟺ ¬creates_intermediate_reference(loc)

对比传统方式:
unsafe(&loc as *const T) ⟺ ∃ intermediate_ref: may_be_invalid(intermediate_ref)
```

**证明**:

```mathematical
&raw操作的安全性保证:

1. 直接地址计算: 无中间引用创建
2. 绕过对齐检查: 允许未对齐访问
3. 保持所有权语义: 不违反借用规则
4. 编译时验证: 静态保证类型安全

传统&...as *const的风险:
1. 创建临时引用: 可能违反对齐要求
2. 借用检查干扰: 可能创建无效引用
3. 未定义行为风险: 编译器优化依赖

∴ &raw严格更安全 ∎
```

### 2.3 内存布局兼容性

#### 2.3.1 对齐敏感分析

```rust
// 内存布局分析框架
#[repr(C)]
struct LayoutAnalyzer<T> {
    phantom: std::marker::PhantomData<T>,
}

impl<T> LayoutAnalyzer<T> {
    const fn alignment() -> usize {
        std::mem::align_of::<T>()
    }

    const fn size() -> usize {
        std::mem::size_of::<T>()
    }

    // 检查字段对齐情况
    fn check_field_alignment<F>(&self, offset: usize) -> AlignmentStatus
    where
        F: Copy,
    {
        let field_align = std::mem::align_of::<F>();
        if offset % field_align == 0 {
            AlignmentStatus::Aligned
        } else {
            AlignmentStatus::Misaligned {
                required: field_align,
                actual: offset % field_align,
            }
        }
    }
}

#[derive(Debug, PartialEq)]
enum AlignmentStatus {
    Aligned,
    Misaligned { required: usize, actual: usize },
}

// 应用示例：packed结构体分析
#[repr(C, packed)]
struct PackedExample {
    flag: u8,     // offset: 0, align: 1 ✓
    data: u64,    // offset: 1, align: 8 ✗ (misaligned)
    count: u32,   // offset: 9, align: 4 ✗ (misaligned)
}

fn analyze_packed_layout() {
    let example = PackedExample { flag: 1, data: 0x123456789ABCDEF0, count: 42 };

    // 传统方式 - 潜在UB
    // let data_ptr = &example.data as *const u64;  // UB！

    // 安全方式 - 使用&raw
    let data_ptr = &raw const example.data;  // 安全！
    let count_ptr = &raw const example.count;  // 安全！

    // 可以安全地使用这些指针
    unsafe {
        let data_value = std::ptr::read_unaligned(data_ptr);
        let count_value = std::ptr::read_unaligned(count_ptr);
        println!("Data: 0x{:X}, Count: {}", data_value, count_value);
    }
}
```

---

## 3. 编译器实现机制深度剖析

### 3.1 HIR到MIR的降级过程

#### 3.1.1 AST转换流程

```rust
// AST节点定义
#[derive(Debug, Clone)]
pub struct AddrOf {
    pub mutability: Mutability,
    pub expr: P<Expr>,
}

// HIR降级实现
impl<'tcx> ExprBuilder<'tcx> {
    fn build_addr_of(&mut self, addr_of: &AddrOf) -> ExprId {
        let target_expr = self.mirror_expr(&addr_of.expr);

        // 验证目标是有效的place表达式
        self.validate_place_expr(target_expr);

        self.expr(ExprKind::AddressOf {
            mutability: addr_of.mutability,
            arg: target_expr,
        })
    }

    fn validate_place_expr(&self, expr_id: ExprId) -> Result<(), PlaceError> {
        let expr = &self.exprs[expr_id];
        match expr.kind {
            ExprKind::Field { .. } |
            ExprKind::Index { .. } |
            ExprKind::Deref { .. } |
            ExprKind::VarRef { .. } => Ok(()),
            _ => Err(PlaceError::NotAPlace),
        }
    }
}

#[derive(Debug)]
enum PlaceError {
    NotAPlace,
    InvalidDereference,
    TemporaryValue,
}
```

#### 3.1.2 MIR生成优化

```rust
// MIR Rvalue扩展
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Rvalue<'tcx> {
    // 现有变体...
    AddressOf(Mutability, Place<'tcx>),
}

// 代码生成优化
impl<'tcx> CodegenCx<'tcx> {
    fn codegen_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> OperandRef<'tcx> {
        match rvalue {
            Rvalue::AddressOf(mutability, place) => {
                // 直接计算地址，无需创建临时引用
                let place_ref = self.codegen_place(place);
                let ptr_ty = self.tcx.mk_ptr(place.ty(&self.mir, self.tcx).ty, *mutability);

                // 生成优化的地址计算指令
                self.builder.struct_gep(place_ref.llval, place_ref.layout)
            }
            // 其他情况...
        }
    }
}
```

### 3.2 LLVM IR生成策略

#### 3.2.1 优化的代码生成

```llvm
; 传统&...as *const的LLVM IR (可能有UB)
define i32* @traditional_approach(%PackedStruct* %s) {
entry:
  %field_ref = getelementptr inbounds %PackedStruct, %PackedStruct* %s, i32 0, i32 1
  ; 这里假设了对齐，可能产生UB
  ret i32* %field_ref
}

; &raw const的LLVM IR (安全)
define i32* @raw_approach(%PackedStruct* %s) {
entry:
  %field_ptr = getelementptr %PackedStruct, %PackedStruct* %s, i32 0, i32 1
  ; 不假设对齐，直接计算偏移
  ret i32* %field_ptr
}
```

#### 3.2.2 性能优化分析

```mathematical
性能对比模型:

传统方式开销:
Cost_traditional = Reference_creation + Alignment_check + Cast_operation
                 ≈ 2-3个CPU周期 + 潜在UB风险

&raw方式开销:
Cost_raw = Direct_address_calculation
         ≈ 1个CPU周期 + 零UB风险

性能提升: (Cost_traditional - Cost_raw) / Cost_traditional ≈ 50-66%
```

---

## 4. 实际应用场景与最佳实践

### 4.1 FFI边界安全操作

#### 4.1.1 C结构体互操作

```rust
// 场景1: 与C库的结构体互操作
use std::ffi::c_void;

#[repr(C)]
struct CCompatibleStruct {
    version: u32,
    #[cfg(target_pointer_width = "64")]
    _padding: u32,  // 确保8字节对齐
    data_ptr: *mut c_void,
    data_len: usize,
}

#[repr(C, packed)]
struct NetworkPacket {
    magic: u16,
    packet_type: u8,
    flags: u8,
    payload_length: u32,  // 可能未对齐
    payload: [u8; 1024],
}

// 安全的C互操作
extern "C" {
    fn process_packet(packet: *const NetworkPacket) -> i32;
    fn get_payload_length(length_ptr: *const u32) -> u32;
}

fn safe_ffi_operations() -> Result<u32, FFIError> {
    let packet = NetworkPacket {
        magic: 0xCAFE,
        packet_type: 1,
        flags: 0x80,
        payload_length: 256,
        payload: [0; 1024],
    };

    // 安全地获取可能未对齐字段的指针
    let length_ptr = &raw const packet.payload_length;
    let packet_ptr = &raw const packet;

    unsafe {
        // 安全的FFI调用
        let result = process_packet(packet_ptr);
        if result < 0 {
            return Err(FFIError::ProcessingFailed(result));
        }

        // 安全地读取未对齐数据
        let length = std::ptr::read_unaligned(length_ptr);

        // 验证通过C函数读取的长度
        let c_length = get_payload_length(length_ptr);
        if length != c_length {
            return Err(FFIError::LengthMismatch { rust: length, c: c_length });
        }

        Ok(length)
    }
}

#[derive(Debug)]
enum FFIError {
    ProcessingFailed(i32),
    LengthMismatch { rust: u32, c: u32 },
    NullPointer,
}

// C兼容的回调接口
type PacketCallback = extern "C" fn(packet: *const NetworkPacket, context: *mut c_void) -> i32;

extern "C" fn rust_packet_handler(packet: *const NetworkPacket, context: *mut c_void) -> i32 {
    if packet.is_null() || context.is_null() {
        return -1;
    }

    unsafe {
        // 安全地访问可能未对齐的字段
        let length_ptr = &raw const (*packet).payload_length;
        let length = std::ptr::read_unaligned(length_ptr);

        // 处理数据包
        if length > 1024 {
            return -2; // 长度无效
        }

        // 通过context传递结果
        let result_ptr = context as *mut u32;
        std::ptr::write_unaligned(result_ptr, length);

        0 // 成功
    }
}
```

#### 4.1.2 内存映射文件操作

```rust
// 场景2: 内存映射文件的安全操作
use std::fs::File;
use std::io::Result as IoResult;
use std::slice;

#[repr(C, packed)]
struct FileHeader {
    signature: [u8; 4],
    version: u32,
    entry_count: u64,
    data_offset: u64,
}

#[repr(C, packed)]
struct DataEntry {
    id: u32,
    timestamp: u64,
    data_size: u32,
    checksum: u32,
}

struct MemoryMappedFile {
    data: *const u8,
    size: usize,
}

impl MemoryMappedFile {
    fn new(file: File) -> IoResult<Self> {
        // 简化的内存映射实现
        let metadata = file.metadata()?;
        let size = metadata.len() as usize;

        // 实际实现会使用mmap
        let data = Box::into_raw(vec![0u8; size].into_boxed_slice()) as *const u8;

        Ok(Self { data, size })
    }

    fn header(&self) -> Option<&FileHeader> {
        if self.size < std::mem::size_of::<FileHeader>() {
            return None;
        }

        unsafe {
            Some(&*(self.data as *const FileHeader))
        }
    }

    fn read_entry(&self, index: usize) -> Option<DataEntry> {
        let header = self.header()?;

        // 安全地读取可能未对齐的字段
        let entry_count_ptr = &raw const header.entry_count;
        let data_offset_ptr = &raw const header.data_offset;

        unsafe {
            let entry_count = std::ptr::read_unaligned(entry_count_ptr);
            let data_offset = std::ptr::read_unaligned(data_offset_ptr);

            if index >= entry_count as usize {
                return None;
            }

            let entry_size = std::mem::size_of::<DataEntry>();
            let entry_offset = data_offset as usize + index * entry_size;

            if entry_offset + entry_size > self.size {
                return None;
            }

            let entry_ptr = self.data.add(entry_offset) as *const DataEntry;
            Some(std::ptr::read_unaligned(entry_ptr))
        }
    }

    fn validate_checksum(&self, entry: &DataEntry) -> bool {
        // 计算校验和并验证
        let id_ptr = &raw const entry.id;
        let timestamp_ptr = &raw const entry.timestamp;
        let data_size_ptr = &raw const entry.data_size;

        unsafe {
            let id = std::ptr::read_unaligned(id_ptr);
            let timestamp = std::ptr::read_unaligned(timestamp_ptr);
            let data_size = std::ptr::read_unaligned(data_size_ptr);

            let calculated = (id as u64)
                .wrapping_add(timestamp)
                .wrapping_add(data_size as u64) as u32;

            calculated == entry.checksum
        }
    }
}

// 使用示例
fn process_memory_mapped_file(file: File) -> IoResult<Vec<DataEntry>> {
    let mapped_file = MemoryMappedFile::new(file)?;
    let mut valid_entries = Vec::new();

    if let Some(header) = mapped_file.header() {
        let entry_count_ptr = &raw const header.entry_count;
        let entry_count = unsafe { std::ptr::read_unaligned(entry_count_ptr) };

        for i in 0..entry_count as usize {
            if let Some(entry) = mapped_file.read_entry(i) {
                if mapped_file.validate_checksum(&entry) {
                    valid_entries.push(entry);
                }
            }
        }
    }

    Ok(valid_entries)
}
```

### 4.2 高性能数据结构实现

#### 4.2.1 自定义内存分配器

```rust
// 场景3: 高性能内存分配器
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

#[repr(C)]
struct BlockHeader {
    size: usize,
    next: Option<NonNull<BlockHeader>>,
    magic: u32,  // 用于调试
}

struct CustomAllocator {
    free_list: Option<NonNull<BlockHeader>>,
    total_allocated: usize,
}

impl CustomAllocator {
    const MAGIC_VALUE: u32 = 0xDEADBEEF;

    fn new() -> Self {
        Self {
            free_list: None,
            total_allocated: 0,
        }
    }

    fn allocate(&mut self, size: usize, align: usize) -> Option<NonNull<u8>> {
        let total_size = size + std::mem::size_of::<BlockHeader>();
        let layout = Layout::from_size_align(total_size, align).ok()?;

        unsafe {
            let ptr = alloc(layout);
            if ptr.is_null() {
                return None;
            }

            // 初始化块头
            let header_ptr = ptr as *mut BlockHeader;

            // 使用&raw安全地设置可能未对齐的字段
            let size_ptr = &raw mut (*header_ptr).size;
            let next_ptr = &raw mut (*header_ptr).next;
            let magic_ptr = &raw mut (*header_ptr).magic;

            std::ptr::write_unaligned(size_ptr, size);
            std::ptr::write_unaligned(next_ptr, None);
            std::ptr::write_unaligned(magic_ptr, Self::MAGIC_VALUE);

            self.total_allocated += total_size;

            Some(NonNull::new_unchecked(ptr.add(std::mem::size_of::<BlockHeader>())))
        }
    }

    fn deallocate(&mut self, ptr: NonNull<u8>, size: usize, align: usize) {
        unsafe {
            let header_ptr = ptr.as_ptr().sub(std::mem::size_of::<BlockHeader>()) as *mut BlockHeader;

            // 验证魔数
            let magic_ptr = &raw const (*header_ptr).magic;
            let magic = std::ptr::read_unaligned(magic_ptr);
            assert_eq!(magic, Self::MAGIC_VALUE, "Corrupted block header");

            // 验证大小
            let stored_size_ptr = &raw const (*header_ptr).size;
            let stored_size = std::ptr::read_unaligned(stored_size_ptr);
            assert_eq!(stored_size, size, "Size mismatch");

            // 添加到空闲链表
            let next_ptr = &raw mut (*header_ptr).next;
            std::ptr::write_unaligned(next_ptr, self.free_list);
            self.free_list = Some(NonNull::new_unchecked(header_ptr));

            self.total_allocated -= size + std::mem::size_of::<BlockHeader>();
        }
    }

    fn debug_info(&self) -> AllocatorStats {
        let mut free_blocks = 0;
        let mut free_bytes = 0;
        let mut current = self.free_list;

        while let Some(block) = current {
            unsafe {
                let header_ptr = block.as_ptr();
                let size_ptr = &raw const (*header_ptr).size;
                let next_ptr = &raw const (*header_ptr).next;

                let size = std::ptr::read_unaligned(size_ptr);
                let next = std::ptr::read_unaligned(next_ptr);

                free_blocks += 1;
                free_bytes += size;
                current = next;
            }
        }

        AllocatorStats {
            total_allocated: self.total_allocated,
            free_blocks,
            free_bytes,
        }
    }
}

#[derive(Debug)]
struct AllocatorStats {
    total_allocated: usize,
    free_blocks: usize,
    free_bytes: usize,
}

// 使用示例
fn test_custom_allocator() {
    let mut allocator = CustomAllocator::new();

    // 分配一些内存块
    let ptr1 = allocator.allocate(64, 8).expect("分配失败");
    let ptr2 = allocator.allocate(128, 16).expect("分配失败");
    let ptr3 = allocator.allocate(256, 32).expect("分配失败");

    println!("分配后统计: {:?}", allocator.debug_info());

    // 释放内存块
    allocator.deallocate(ptr2, 128, 16);
    allocator.deallocate(ptr1, 64, 8);

    println!("部分释放后统计: {:?}", allocator.debug_info());

    allocator.deallocate(ptr3, 256, 32);

    println!("全部释放后统计: {:?}", allocator.debug_info());
}
```

### 4.3 嵌入式系统内存操作

#### 4.3.1 硬件寄存器映射

```rust
// 场景4: 嵌入式系统硬件寄存器访问
#[repr(C, packed)]
struct HardwareRegisters {
    control: u32,      // 0x00: 控制寄存器
    status: u32,       // 0x04: 状态寄存器
    data_in: u32,      // 0x08: 数据输入
    data_out: u32,     // 0x0C: 数据输出
    interrupt_mask: u16, // 0x10: 中断屏蔽
    _reserved1: u16,   // 0x12: 保留
    timer_config: u32, // 0x14: 定时器配置
    _reserved2: [u32; 2], // 0x18-0x1F: 保留
}

struct HardwareDriver {
    registers: *mut HardwareRegisters,
    base_addr: usize,
}

impl HardwareDriver {
    // 内存映射的寄存器基地址
    const REGISTER_BASE: usize = 0x4000_0000;

    fn new() -> Self {
        Self {
            registers: Self::REGISTER_BASE as *mut HardwareRegisters,
            base_addr: Self::REGISTER_BASE,
        }
    }

    // 安全的寄存器读取
    fn read_control(&self) -> u32 {
        unsafe {
            let control_ptr = &raw const (*self.registers).control;
            std::ptr::read_volatile(control_ptr)
        }
    }

    fn read_status(&self) -> u32 {
        unsafe {
            let status_ptr = &raw const (*self.registers).status;
            std::ptr::read_volatile(status_ptr)
        }
    }

    // 安全的寄存器写入
    fn write_control(&mut self, value: u32) {
        unsafe {
            let control_ptr = &raw mut (*self.registers).control;
            std::ptr::write_volatile(control_ptr, value);
        }
    }

    fn write_data(&mut self, value: u32) {
        unsafe {
            let data_ptr = &raw mut (*self.registers).data_in;
            std::ptr::write_volatile(data_ptr, value);
        }
    }

    // 原子性的寄存器操作
    fn set_control_bits(&mut self, mask: u32) {
        unsafe {
            let control_ptr = &raw mut (*self.registers).control;
            let current = std::ptr::read_volatile(control_ptr);
            std::ptr::write_volatile(control_ptr, current | mask);
        }
    }

    fn clear_control_bits(&mut self, mask: u32) {
        unsafe {
            let control_ptr = &raw mut (*self.registers).control;
            let current = std::ptr::read_volatile(control_ptr);
            std::ptr::write_volatile(control_ptr, current & !mask);
        }
    }

    // 复杂的设备初始化序列
    fn initialize_device(&mut self) -> Result<(), DeviceError> {
        // 1. 重置设备
        self.write_control(0x0000_0001); // 重置位

        // 2. 等待重置完成
        let mut timeout = 1000;
        while self.read_status() & 0x8000_0000 != 0 && timeout > 0 {
            timeout -= 1;
            // 在实际系统中会使用延时函数
        }

        if timeout == 0 {
            return Err(DeviceError::ResetTimeout);
        }

        // 3. 配置设备
        self.write_control(0x0000_0010); // 启用设备

        // 4. 设置中断屏蔽
        unsafe {
            let mask_ptr = &raw mut (*self.registers).interrupt_mask;
            std::ptr::write_volatile(mask_ptr, 0xFFFF); // 屏蔽所有中断
        }

        // 5. 配置定时器
        unsafe {
            let timer_ptr = &raw mut (*self.registers).timer_config;
            std::ptr::write_volatile(timer_ptr, 0x0001_0000); // 1MHz时钟
        }

        Ok(())
    }

    // DMA传输设置
    fn setup_dma_transfer(&mut self, src: *const u8, dst: *mut u8, len: usize) -> Result<(), DeviceError> {
        if len > 0xFFFF {
            return Err(DeviceError::InvalidLength);
        }

        // 设置源地址 (分多个32位寄存器)
        let src_addr = src as usize;
        self.write_register_at_offset(0x20, (src_addr & 0xFFFF_FFFF) as u32);

        // 设置目标地址
        let dst_addr = dst as usize;
        self.write_register_at_offset(0x24, (dst_addr & 0xFFFF_FFFF) as u32);

        // 设置传输长度
        self.write_register_at_offset(0x28, len as u32);

        // 启动DMA传输
        self.set_control_bits(0x0000_0100);

        Ok(())
    }

    fn write_register_at_offset(&mut self, offset: usize, value: u32) {
        unsafe {
            let reg_ptr = (self.base_addr + offset) as *mut u32;
            std::ptr::write_volatile(reg_ptr, value);
        }
    }
}

#[derive(Debug)]
enum DeviceError {
    ResetTimeout,
    InvalidLength,
    TransferFailed,
    HardwareFault,
}

// 中断处理
extern "C" fn hardware_interrupt_handler() {
    static mut DRIVER: Option<HardwareDriver> = None;

    unsafe {
        if let Some(ref mut driver) = DRIVER {
            let status = driver.read_status();

            // 处理不同类型的中断
            if status & 0x0001 != 0 {
                // 数据就绪中断
                handle_data_ready_interrupt(driver);
            }

            if status & 0x0002 != 0 {
                // DMA完成中断
                handle_dma_complete_interrupt(driver);
            }

            if status & 0x0004 != 0 {
                // 错误中断
                handle_error_interrupt(driver);
            }
        }
    }
}

fn handle_data_ready_interrupt(driver: &mut HardwareDriver) {
    unsafe {
        let data_ptr = &raw const (*driver.registers).data_out;
        let data = std::ptr::read_volatile(data_ptr);

        // 处理接收到的数据
        process_received_data(data);

        // 清除中断标志
        driver.write_register_at_offset(0x30, 0x0001);
    }
}

fn handle_dma_complete_interrupt(driver: &mut HardwareDriver) {
    // 清除DMA完成标志
    driver.clear_control_bits(0x0000_0100);

    // 清除中断标志
    driver.write_register_at_offset(0x30, 0x0002);

    // 通知应用程序DMA完成
    notify_dma_complete();
}

fn handle_error_interrupt(driver: &mut HardwareDriver) {
    let status = driver.read_status();
    let error_code = (status >> 16) & 0xFF;

    // 记录错误信息
    log_hardware_error(error_code);

    // 清除错误状态
    driver.write_register_at_offset(0x30, 0x0004);
}

fn process_received_data(_data: u32) {
    // 处理接收到的数据
}

fn notify_dma_complete() {
    // 通知应用程序
}

fn log_hardware_error(_error_code: u32) {
    // 记录硬件错误
}
