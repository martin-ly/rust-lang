# Rust 系统编程

系统编程是 Rust 的核心应用领域之一。
Rust 的设计目标就是成为 C/C++ 的现代替代品，在保证同等性能的同时提供内存安全和线程安全保证。
本文档将深入探讨 Rust 在系统编程领域的应用。

## 目录

- [Rust 系统编程](#rust-系统编程)
  - [目录](#目录)
  - [系统编程概述](#系统编程概述)
    - [什么是系统编程](#什么是系统编程)
    - [Rust 在系统编程中的优势](#rust-在系统编程中的优势)
    - [系统编程核心概念](#系统编程核心概念)
  - [内存管理](#内存管理)
    - [物理内存管理](#物理内存管理)
    - [虚拟内存管理](#虚拟内存管理)
  - [操作系统开发](#操作系统开发)
    - [引导加载程序](#引导加载程序)
  - [设备驱动](#设备驱动)
    - [字符设备驱动](#字符设备驱动)
    - [块设备驱动](#块设备驱动)
  - [文件系统](#文件系统)
    - [简单文件系统实现](#简单文件系统实现)
  - [网络协议栈](#网络协议栈)
    - [TCP/IP 实现](#tcpip-实现)
  - [虚拟化与容器](#虚拟化与容器)
    - [OCI 容器运行时](#oci-容器运行时)
  - [性能优化](#性能优化)
    - [零拷贝技术](#零拷贝技术)
    - [SIMD 优化](#simd-优化)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 内存安全模式](#2-内存安全模式)
    - [3. 并发安全](#3-并发安全)
  - [总结](#总结)
  - [参考资源](#参考资源)

---

## 系统编程概述

### 什么是系统编程

系统编程是指开发直接与计算机硬件交互或与操作系统内核紧密集成的软件。
典型的系统编程任务包括：

- 操作系统内核开发
- 设备驱动程序
- 文件系统实现
- 网络协议栈
- 虚拟化技术
- 嵌入式系统固件

### Rust 在系统编程中的优势

| 特性 | Rust 实现 | C/C++ 对比 |
|------|-----------|------------|
| 内存安全 | 编译时所有权检查 | 运行时错误/手动管理 |
| 数据竞争防护 | 编译时检测 | 难以检测，依赖运行时 |
| 零成本抽象 | 无运行时开销 | 类似，但缺乏安全检查 |
| 错误处理 | Result/Option 强制处理 | 容易忽略错误码 |
| 跨平台 | 优秀的跨平台支持 | 需要大量条件编译 |

### 系统编程核心概念

```rust
//! 系统编程基础示例

use std::ptr::NonNull;
use std::alloc::{alloc, dealloc, Layout};
use std::mem;

/// 安全的内存分配包装器
pub struct SystemBuffer {
    ptr: NonNull<u8>,
    layout: Layout,
    size: usize,
}

impl SystemBuffer {
    /// 分配指定大小的内存
    pub fn new(size: usize) -> Option<Self> {
        let layout = Layout::array::<u8>(size).ok()?;

        unsafe {
            let ptr = alloc(layout);
            if ptr.is_null() {
                return None;
            }

            Some(Self {
                ptr: NonNull::new_unchecked(ptr),
                layout,
                size,
            })
        }
    }

    /// 获取原始指针
    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// 获取切片视图
    pub fn as_slice(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(self.ptr.as_ptr(), self.size)
        }
    }

    /// 获取可变切片视图
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe {
            std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.size)
        }
    }

    /// 清零内存
    pub fn zero(&mut self) {
        unsafe {
            std::ptr::write_bytes(self.ptr.as_ptr(), 0, self.size);
        }
    }
}

impl Drop for SystemBuffer {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.ptr.as_ptr(), self.layout);
        }
    }
}

// 确保线程安全
unsafe impl Send for SystemBuffer {}
unsafe impl Sync for SystemBuffer {}
```

---

## 内存管理

### 物理内存管理

```rust
//! 物理内存分配器示例

use std::collections::BTreeMap;
use std::sync::Mutex;

/// 物理内存帧
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhysFrame {
    number: usize,
}

impl PhysFrame {
    pub const SIZE: usize = 4096; // 4KB 页

    pub fn new(number: usize) -> Self {
        Self { number }
    }

    pub fn start_address(&self) -> usize {
        self.number * Self::SIZE
    }
}

/// 物理内存分配器
pub struct FrameAllocator {
    free_frames: Vec<PhysFrame>,
    used_frames: BTreeMap<usize, PhysFrame>,
    total_frames: usize,
}

impl FrameAllocator {
    pub fn new(total_memory: usize) -> Self {
        let total_frames = total_memory / PhysFrame::SIZE;
        let mut free_frames = Vec::with_capacity(total_frames);

        for i in 0..total_frames {
            free_frames.push(PhysFrame::new(i));
        }

        Self {
            free_frames,
            used_frames: BTreeMap::new(),
            total_frames,
        }
    }

    /// 分配一个物理帧
    pub fn allocate(&mut self) -> Option<PhysFrame> {
        let frame = self.free_frames.pop()?;
        self.used_frames.insert(frame.number, frame);
        Some(frame)
    }

    /// 分配连续的多个帧
    pub fn allocate_contiguous(&mut self, count: usize) -> Option<Vec<PhysFrame>> {
        // 查找连续的可用帧
        for window in self.free_frames.windows(count) {
            let first = window[0].number;
            if window.iter().enumerate().all(|(i, f)| f.number == first + i) {
                let start_idx = self.free_frames.iter()
                    .position(|f| f.number == first)?;

                let mut frames = Vec::with_capacity(count);
                for _ in 0..count {
                    let frame = self.free_frames.remove(start_idx);
                    self.used_frames.insert(frame.number, frame);
                    frames.push(frame);
                }
                return Some(frames);
            }
        }
        None
    }

    /// 释放物理帧
    pub fn deallocate(&mut self, frame: PhysFrame) {
        if self.used_frames.remove(&frame.number).is_some() {
            self.free_frames.push(frame);
        }
    }

    /// 获取使用统计
    pub fn stats(&self) -> FrameStats {
        FrameStats {
            total: self.total_frames,
            used: self.used_frames.len(),
            free: self.free_frames.len(),
        }
    }
}

#[derive(Debug)]
pub struct FrameStats {
    pub total: usize,
    pub used: usize,
    pub free: usize,
}

/// 线程安全的帧分配器包装
pub struct ThreadSafeFrameAllocator {
    inner: Mutex<FrameAllocator>,
}

impl ThreadSafeFrameAllocator {
    pub fn new(total_memory: usize) -> Self {
        Self {
            inner: Mutex::new(FrameAllocator::new(total_memory)),
        }
    }

    pub fn allocate(&self) -> Option<PhysFrame> {
        self.inner.lock().ok()?.allocate()
    }

    pub fn deallocate(&self, frame: PhysFrame) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.deallocate(frame);
        }
    }
}
```

### 虚拟内存管理

```rust
//! 虚拟内存管理

use std::collections::HashMap;

/// 虚拟地址
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VirtAddr(usize);

impl VirtAddr {
    pub fn new(addr: usize) -> Self {
        Self(addr)
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }

    pub fn page_number(&self) -> usize {
        self.0 / PageTableEntry::PAGE_SIZE
    }

    pub fn page_offset(&self) -> usize {
        self.0 % PageTableEntry::PAGE_SIZE
    }
}

/// 页表项标志
#[derive(Debug, Clone, Copy, Default)]
pub struct PageFlags {
    pub present: bool,
    pub writable: bool,
    pub user_accessible: bool,
    pub write_through: bool,
    pub cache_disabled: bool,
    pub accessed: bool,
    pub dirty: bool,
    pub huge_page: bool,
    pub global: bool,
}

impl PageFlags {
    pub fn read_only() -> Self {
        Self {
            present: true,
            writable: false,
            ..Default::default()
        }
    }

    pub fn read_write() -> Self {
        Self {
            present: true,
            writable: true,
            ..Default::default()
        }
    }

    pub fn user() -> Self {
        Self {
            present: true,
            writable: true,
            user_accessible: true,
            ..Default::default()
        }
    }
}

/// 页表项
#[derive(Debug, Clone, Copy)]
pub struct PageTableEntry {
    pub frame: PhysFrame,
    pub flags: PageFlags,
}

impl PageTableEntry {
    pub const PAGE_SIZE: usize = 4096;

    pub fn new(frame: PhysFrame, flags: PageFlags) -> Self {
        Self { frame, flags }
    }

    pub fn is_present(&self) -> bool {
        self.flags.present
    }
}

/// 页表
pub struct PageTable {
    entries: HashMap<usize, PageTableEntry>,
}

impl PageTable {
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// 映射虚拟页到物理帧
    pub fn map(&mut self, virt_page: usize, frame: PhysFrame, flags: PageFlags) {
        self.entries.insert(virt_page, PageTableEntry::new(frame, flags));
    }

    /// 取消映射
    pub fn unmap(&mut self, virt_page: usize) -> Option<PageTableEntry> {
        self.entries.remove(&virt_page)
    }

    /// 查找页表项
    pub fn lookup(&self, virt_page: usize) -> Option<&PageTableEntry> {
        self.entries.get(&virt_page)
    }

    /// 虚拟地址转物理地址
    pub fn translate(&self, virt_addr: VirtAddr) -> Option<usize> {
        let entry = self.lookup(virt_addr.page_number())?;
        if !entry.is_present() {
            return None;
        }
        Some(entry.frame.start_address() + virt_addr.page_offset())
    }

    /// 获取所有映射
    pub fn mappings(&self) -> &HashMap<usize, PageTableEntry> {
        &self.entries
    }
}

/// 地址空间
pub struct AddressSpace {
    page_table: PageTable,
    heap_start: VirtAddr,
    heap_end: VirtAddr,
}

impl AddressSpace {
    pub fn new() -> Self {
        Self {
            page_table: PageTable::new(),
            heap_start: VirtAddr::new(0x1000),
            heap_end: VirtAddr::new(0x1000),
        }
    }

    /// 分配虚拟内存区域
    pub fn allocate(&mut self, size: usize, allocator: &mut FrameAllocator) -> Option<VirtAddr> {
        let pages_needed = (size + PageTableEntry::PAGE_SIZE - 1) / PageTableEntry::PAGE_SIZE;
        let start_addr = self.heap_end;

        for i in 0..pages_needed {
            let frame = allocator.allocate()?;
            let virt_page = (self.heap_end.as_usize() / PageTableEntry::PAGE_SIZE) + i;
            self.page_table.map(virt_page, frame, PageFlags::read_write());
        }

        self.heap_end = VirtAddr::new(self.heap_end.as_usize() + pages_needed * PageTableEntry::PAGE_SIZE);
        Some(start_addr)
    }

    /// 释放虚拟内存区域
    pub fn deallocate(&mut self, addr: VirtAddr, size: usize, allocator: &mut FrameAllocator) {
        let pages = (size + PageTableEntry::PAGE_SIZE - 1) / PageTableEntry::PAGE_SIZE;
        let start_page = addr.page_number();

        for i in 0..pages {
            if let Some(entry) = self.page_table.unmap(start_page + i) {
                allocator.deallocate(entry.frame);
            }
        }
    }
}
```

---

## 操作系统开发

### 引导加载程序

```rust
//! 操作系统引导代码示例

#![no_std]
#![no_main]

use core::panic::PanicInfo;

/// 内核入口点
#[no_mangle]
pub extern "C" fn _start() -> ! {
    init_vga_buffer();
    println!("Kernel booting...");

    unsafe { init_memory(); }
    init_interrupts();
    init_scheduler();

    println!("Kernel initialized successfully!");
    start_init_process();

    loop { hlt(); }
}

/// VGA 文本缓冲区
const VGA_BUFFER: *mut u8 = 0xb8000 as *mut u8;
const VGA_WIDTH: usize = 80;
const VGA_HEIGHT: usize = 25;

static mut VGA_ROW: usize = 0;
static mut VGA_COL: usize = 0;

fn init_vga_buffer() {
    unsafe {
        for i in 0..(VGA_WIDTH * VGA_HEIGHT) {
            let offset = i * 2;
            core::ptr::write_volatile(VGA_BUFFER.add(offset), b' ');
            core::ptr::write_volatile(VGA_BUFFER.add(offset + 1), 0x0f);
        }
    }
}

pub fn _print(args: core::fmt::Arguments) {
    use core::fmt::Write;
    unsafe { VGA_WRITER.write_fmt(args).unwrap(); }
}

struct VgaWriter;

impl core::fmt::Write for VgaWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for byte in s.bytes() { write_byte(byte); }
        Ok(())
    }
}

fn write_byte(byte: u8) {
    unsafe {
        match byte {
            b'\n' => { VGA_ROW += 1; VGA_COL = 0; }
            byte => {
                let offset = (VGA_ROW * VGA_WIDTH + VGA_COL) * 2;
                core::ptr::write_volatile(VGA_BUFFER.add(offset), byte);
                core::ptr::write_volatile(VGA_BUFFER.add(offset + 1), 0x0f);
                VGA_COL += 1;
                if VGA_COL >= VGA_WIDTH { VGA_COL = 0; VGA_ROW += 1; }
            }
        }
        if VGA_ROW >= VGA_HEIGHT { scroll(); }
    }
}

fn scroll() {
    unsafe {
        for row in 1..VGA_HEIGHT {
            for col in 0..VGA_WIDTH {
                let src = (row * VGA_WIDTH + col) * 2;
                let dst = ((row - 1) * VGA_WIDTH + col) * 2;
                let ch = core::ptr::read_volatile(VGA_BUFFER.add(src));
                let attr = core::ptr::read_volatile(VGA_BUFFER.add(src + 1));
                core::ptr::write_volatile(VGA_BUFFER.add(dst), ch);
                core::ptr::write_volatile(VGA_BUFFER.add(dst + 1), attr);
            }
        }
        for col in 0..VGA_WIDTH {
            let offset = ((VGA_HEIGHT - 1) * VGA_WIDTH + col) * 2;
            core::ptr::write_volatile(VGA_BUFFER.add(offset), b' ');
            core::ptr::write_volatile(VGA_BUFFER.add(offset + 1), 0x0f);
        }
        VGA_ROW = VGA_HEIGHT - 1;
    }
}

static mut VGA_WRITER: VgaWriter = VgaWriter;

unsafe fn init_memory() {}
fn init_interrupts() {}
fn init_scheduler() {}
fn start_init_process() {}
fn hlt() { unsafe { core::arch::asm!("hlt", options(nomem, nostack)); } }

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    println!("Kernel panic: {}", info);
    loop { hlt(); }
}
```

---

## 设备驱动

### 字符设备驱动

```rust
//! 串口驱动示例

use core::fmt;

/// UART 寄存器偏移
#[repr(usize)]
enum UartRegister {
    Data = 0,
    InterruptEnable = 1,
    FifoControl = 2,
    LineControl = 3,
    ModemControl = 4,
    LineStatus = 5,
    ModemStatus = 6,
    Scratch = 7,
}

pub struct SerialPort {
    base: usize,
}

impl SerialPort {
    pub const COM1: usize = 0x3F8;
    pub const BAUD_115200: u16 = 1;

    pub fn init(base: usize) -> Option<Self> {
        let port = Self { base };
        unsafe {
            port.write_register(UartRegister::InterruptEnable, 0x00);
            port.write_register(UartRegister::LineControl, 0x80);
            port.write_register(UartRegister::Data, (Self::BAUD_115200 & 0xFF) as u8);
            port.write_register(UartRegister::InterruptEnable, ((Self::BAUD_115200 >> 8) & 0xFF) as u8);
            port.write_register(UartRegister::LineControl, 0x03);
            port.write_register(UartRegister::FifoControl, 0xC7);
            port.write_register(UartRegister::ModemControl, 0x0B);
            port.write_register(UartRegister::ModemControl, 0x1E);
            port.write_register(UartRegister::Data, 0xAE);
            if port.read_register(UartRegister::Data) != 0xAE { return None; }
            port.write_register(UartRegister::ModemControl, 0x0F);
        }
        Some(port)
    }

    pub fn is_transmit_empty(&self) -> bool {
        unsafe { self.read_register(UartRegister::LineStatus) & 0x20 != 0 }
    }

    pub fn send(&self, data: u8) {
        unsafe { while !self.is_transmit_empty() {} self.write_register(UartRegister::Data, data); }
    }

    pub fn is_data_available(&self) -> bool {
        unsafe { self.read_register(UartRegister::LineStatus) & 0x01 != 0 }
    }

    pub fn receive(&self) -> Option<u8> {
        unsafe { if self.is_data_available() { Some(self.read_register(UartRegister::Data)) } else { None } }
    }

    unsafe fn read_register(&self, reg: UartRegister) -> u8 {
        core::ptr::read_volatile((self.base + reg as usize) as *const u8)
    }

    unsafe fn write_register(&self, reg: UartRegister, value: u8) {
        core::ptr::write_volatile((self.base + reg as usize) as *mut u8, value);
    }
}

impl fmt::Write for SerialPort {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for byte in s.bytes() { self.send(byte); }
        Ok(())
    }
}
```

### 块设备驱动

```rust
//! 块设备驱动示例

use alloc::vec::Vec;

#[repr(C)]
struct AhciRegisters {
    host_capabilities: u32,
    global_host_control: u32,
    interrupt_status: u32,
    ports_implemented: u32,
    version: u32,
    _reserved: [u8; 0x74],
    vendor_specific: [u8; 0x60],
    ports: [AhciPortRegisters; 32],
}

#[repr(C)]
struct AhciPortRegisters {
    command_list_base: u64,
    fis_base: u64,
    interrupt_status: u32,
    interrupt_enable: u32,
    command_status: u32,
    _reserved1: u32,
    task_file_data: u32,
    signature: u32,
    sata_status: u32,
    sata_control: u32,
    sata_error: u32,
    sata_active: u32,
    command_issue: u32,
    sata_notification: u32,
    fis_switch_control: u32,
    _reserved2: [u32; 11],
    vendor_specific: [u32; 4],
}

pub struct AhciController {
    registers: &'static mut AhciRegisters,
    ports: Vec<AhciPort>,
}

pub struct AhciPort {
    index: usize,
    registers: *mut AhciPortRegisters,
}

pub enum AhciError {
    InvalidPort,
    DeviceError,
}

impl AhciController {
    pub unsafe fn init(mmio_base: usize) -> Result<Self, AhciError> {
        let registers = &mut *(mmio_base as *mut AhciRegisters);
        let ports_implemented = registers.ports_implemented;
        let port_count = ports_implemented.count_ones() as usize;

        registers.global_host_control |= 0x80000000;
        registers.global_host_control |= 0x00000001;
        while registers.global_host_control & 0x00000001 != 0 {}

        let mut ports = Vec::with_capacity(port_count);
        for i in 0..32 {
            if ports_implemented & (1 << i) != 0 {
                ports.push(AhciPort { index: i, registers: &mut registers.ports[i] });
            }
        }

        Ok(Self { registers, ports })
    }

    pub fn read_block(&mut self, port_idx: usize, lba: u64, buffer: &mut [u8]) -> Result<(), AhciError> {
        let _port = self.ports.get_mut(port_idx).ok_or(AhciError::InvalidPort)?;
        Ok(())
    }
}
```

---

## 文件系统

### 简单文件系统实现

```rust
//! 简单的日志结构文件系统

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::mem::size_of;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SuperBlock {
    pub magic: u32,
    pub block_size: u32,
    pub block_count: u64,
    pub inode_count: u64,
    pub free_blocks: u64,
    pub free_inodes: u64,
    pub root_inode: u64,
    pub journal_start: u64,
    pub journal_size: u32,
}

impl SuperBlock {
    pub const MAGIC: u32 = 0x52555354;

    pub fn new(block_size: u32, block_count: u64) -> Self {
        Self {
            magic: Self::MAGIC,
            block_size,
            block_count,
            inode_count: block_count / 4,
            free_blocks: block_count - 1,
            free_inodes: block_count / 4 - 1,
            root_inode: 1,
            journal_start: 1,
            journal_size: 1024,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InodeType { File = 1, Directory = 2, Symlink = 3, BlockDevice = 4, CharDevice = 5, Fifo = 6, Socket = 7 }

#[repr(C)]
#[derive(Debug, Clone)]
pub struct Inode {
    pub number: u64,
    pub inode_type: u32,
    pub mode: u16,
    pub uid: u32,
    pub gid: u32,
    pub size: u64,
    pub atime: u64,
    pub mtime: u64,
    pub ctime: u64,
    pub links: u32,
    pub blocks: u64,
    pub direct_blocks: [u64; 12],
    pub indirect_block: u64,
    pub double_indirect: u64,
}

impl Inode {
    pub fn new(number: u64, inode_type: InodeType) -> Self {
        Self { number, inode_type: inode_type as u32, mode: 0o644, uid: 0, gid: 0, size: 0,
               atime: 0, mtime: 0, ctime: 0, links: 1, blocks: 0,
               direct_blocks: [0; 12], indirect_block: 0, double_indirect: 0 }
    }
    pub fn is_directory(&self) -> bool { self.inode_type == InodeType::Directory as u32 }
    pub fn is_file(&self) -> bool { self.inode_type == InodeType::File as u32 }
}

pub struct FileSystem {
    superblock: SuperBlock,
    inode_cache: BTreeMap<u64, Inode>,
}

impl FileSystem {
    pub fn new(block_size: u32, block_count: u64) -> Self {
        Self { superblock: SuperBlock::new(block_size, block_count), inode_cache: BTreeMap::new() }
    }

    pub fn create_file(&mut self, parent: u64, name: &str) -> Result<Inode, FsError> {
        let inode_num = self.allocate_inode()?;
        let inode = Inode::new(inode_num, InodeType::File);
        self.inode_cache.insert(inode_num, inode.clone());
        Ok(inode)
    }

    pub fn create_directory(&mut self, parent: u64, name: &str) -> Result<Inode, FsError> {
        let inode_num = self.allocate_inode()?;
        let mut inode = Inode::new(inode_num, InodeType::Directory);
        inode.mode = 0o755;
        self.inode_cache.insert(inode_num, inode.clone());
        Ok(inode)
    }

    fn allocate_inode(&mut self) -> Result<u64, FsError> {
        static mut NEXT_INODE: u64 = 2;
        unsafe { let inode = NEXT_INODE; NEXT_INODE += 1; Ok(inode) }
    }
}

#[derive(Debug)]
pub enum FsError { InvalidMagic, InodeNotFound, BlockNotFound, NoSpace, NotImplemented }
```

---

## 网络协议栈

### TCP/IP 实现

```rust
//! 简化的 TCP/IP 协议栈

use alloc::collections::VecDeque;
use alloc::vec::Vec;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct EthernetHeader {
    pub dst_mac: [u8; 6],
    pub src_mac: [u8; 6],
    pub ether_type: u16,
}

impl EthernetHeader { pub const SIZE: usize = 14; pub const TYPE_IP: u16 = 0x0800; }

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct IpHeader {
    pub version_ihl: u8,
    pub tos: u8,
    pub total_len: u16,
    pub id: u16,
    pub flags_frag: u16,
    pub ttl: u8,
    pub protocol: u8,
    pub checksum: u16,
    pub src_ip: [u8; 4],
    pub dst_ip: [u8; 4],
}

impl IpHeader {
    pub const SIZE: usize = 20;
    pub const PROTO_TCP: u8 = 6;
    pub fn version(&self) -> u8 { self.version_ihl >> 4 }
    pub fn header_len(&self) -> usize { ((self.version_ihl & 0x0F) as usize) * 4 }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct TcpHeader {
    pub src_port: u16,
    pub dst_port: u16,
    pub seq_num: u32,
    pub ack_num: u32,
    pub data_offset: u8,
    pub flags: u8,
    pub window: u16,
    pub checksum: u16,
    pub urgent_ptr: u16,
}

impl TcpHeader {
    pub const SIZE: usize = 20;
    pub const FIN: u8 = 0x01;
    pub const SYN: u8 = 0x02;
    pub const ACK: u8 = 0x10;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpState { Closed, Listen, SynSent, SynReceived, Established, FinWait1, FinWait2, CloseWait, Closing, LastAck, TimeWait }

pub struct TcpConnection {
    state: TcpState,
    snd_una: u32, snd_nxt: u32, snd_wnd: u16,
    rcv_nxt: u32, rcv_wnd: u16,
    send_buffer: VecDeque<u8>,
    recv_buffer: VecDeque<u8>,
}

impl TcpConnection {
    pub fn new() -> Self {
        Self { state: TcpState::Closed, snd_una: 0, snd_nxt: 0, snd_wnd: 65535,
               rcv_nxt: 0, rcv_wnd: 65535, send_buffer: VecDeque::new(), recv_buffer: VecDeque::new() }
    }

    pub fn handle_packet(&mut self, header: &TcpHeader, data: &[u8]) -> Option<TcpPacket> {
        match self.state {
            TcpState::Listen => {
                if header.flags & TcpHeader::SYN != 0 {
                    self.state = TcpState::SynReceived;
                    self.rcv_nxt = header.seq_num.wrapping_add(1);
                    self.snd_nxt = 1000;
                    self.snd_una = self.snd_nxt;
                    Some(self.build_packet(TcpHeader::SYN | TcpHeader::ACK, &[]))
                } else { None }
            }
            TcpState::Established => {
                Some(self.build_packet(TcpHeader::ACK, &[]))
            }
            _ => None,
        }
    }

    fn build_packet(&mut self, flags: u8, data: &[u8]) -> TcpPacket {
        let header = TcpHeader {
            src_port: 0, dst_port: 0,
            seq_num: self.snd_nxt,
            ack_num: self.rcv_nxt,
            data_offset: (TcpHeader::SIZE as u8 / 4) << 4,
            flags, window: self.rcv_wnd, checksum: 0, urgent_ptr: 0,
        };
        TcpPacket { header, data: data.to_vec() }
    }
}

pub struct TcpPacket { header: TcpHeader, data: Vec<u8> }
```

---

## 虚拟化与容器

### OCI 容器运行时

```rust
//! OCI 容器运行时核心实现

use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RuntimeConfig {
    pub oci_version: String,
    pub root: RootConfig,
    pub process: ProcessConfig,
    pub hostname: Option<String>,
    pub linux: LinuxConfig,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RootConfig { pub path: String, pub readonly: Option<bool> }

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ProcessConfig { pub terminal: Option<bool>, pub user: UserConfig, pub args: Vec<String>, pub env: Vec<String>, pub cwd: String }

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct UserConfig { pub uid: u32, pub gid: u32 }

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct LinuxConfig {
    pub namespaces: Vec<NamespaceConfig>,
    pub cgroups_path: Option<String>,
    pub resources: Option<ResourcesConfig>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct NamespaceConfig { pub namespace_type: String, pub path: Option<String> }

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ResourcesConfig {
    pub memory: Option<MemoryConfig>,
    pub cpu: Option<CpuConfig>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MemoryConfig { pub limit: Option<i64>, pub swap: Option<i64> }

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CpuConfig { pub shares: Option<u64>, pub quota: Option<i64> }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContainerState { Creating, Created, Running, Stopped }

pub struct Container {
    pub id: String,
    pub bundle: String,
    pub rootfs: String,
    pub state: ContainerState,
    pub config: RuntimeConfig,
}

impl Container {
    pub fn create(id: &str, bundle: &str) -> Result<Self, ContainerError> {
        let config_path = Path::new(bundle).join("config.json");
        let config_data = fs::read_to_string(config_path)?;
        let config: RuntimeConfig = serde_json::from_str(&config_data)?;
        let rootfs = Path::new(bundle).join(&config.root.path);

        Ok(Self { id: id.to_string(), bundle: bundle.to_string(),
                  rootfs: rootfs.to_string_lossy().to_string(),
                  state: ContainerState::Creating, config })
    }

    pub fn start(&mut self) -> Result<(), ContainerError> {
        let mut cmd = Command::new(&self.config.process.args[0]);
        cmd.args(&self.config.process.args[1..])
            .env_clear()
            .stdin(Stdio::inherit())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());

        let mut child = cmd.spawn()?;
        child.wait()?;
        self.state = ContainerState::Running;
        Ok(())
    }

    pub fn stop(&mut self) -> Result<(), ContainerError> {
        self.state = ContainerState::Stopped;
        Ok(())
    }

    pub fn delete(&self) -> Result<(), ContainerError> {
        Ok(())
    }
}

#[derive(Debug)]
pub enum ContainerError { Io(std::io::Error), Json(serde_json::Error), InvalidState, ContainerRunning }

impl From<std::io::Error> for ContainerError {
    fn from(e: std::io::Error) -> Self { ContainerError::Io(e) }
}

impl From<serde_json::Error> for ContainerError {
    fn from(e: serde_json::Error) -> Self { ContainerError::Json(e) }
}
```

---

## 性能优化

### 零拷贝技术

```rust
//! 零拷贝 I/O 实现

use std::fs::File;
use std::io;
use std::os::unix::io::AsRawFd;

/// sendfile 系统调用封装
pub fn sendfile(out_fd: &File, in_fd: &File, offset: Option<&mut i64>, count: usize) -> io::Result<usize> {
    let mut off = offset.map(|o| *o).unwrap_or(0);
    let off_ptr = offset.map(|_| &mut off as *mut _).unwrap_or(std::ptr::null_mut());

    let result = unsafe {
        libc::sendfile(out_fd.as_raw_fd(), in_fd.as_raw_fd(), off_ptr, count)
    };

    if result < 0 { return Err(io::Error::last_os_error()); }
    if let Some(o) = offset { *o = off; }
    Ok(result as usize)
}

/// 内存映射 I/O
use memmap2::Mmap;

pub struct ZeroCopyReader {
    mmap: Mmap,
    position: usize,
}

impl ZeroCopyReader {
    pub fn new(file: &File) -> io::Result<Self> {
        let mmap = unsafe { Mmap::map(file)? };
        Ok(Self { mmap, position: 0 })
    }

    pub fn as_slice(&self) -> &[u8] { &self.mmap[self.position..] }
    pub fn entire_file(&self) -> &[u8] { &self.mmap[..] }

    pub fn find(&self, pattern: &[u8]) -> Option<usize> {
        self.mmap.windows(pattern.len()).position(|w| w == pattern)
    }
}
```

### SIMD 优化

```rust
//! SIMD 并行处理

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// 使用 SIMD 进行字节扫描
#[cfg(target_arch = "x86_64")]
pub fn simd_find(haystack: &[u8], needle: u8) -> Option<usize> {
    if haystack.len() < 32 {
        return haystack.iter().position(|&b| b == needle);
    }

    unsafe {
        let needle_vec = _mm256_set1_epi8(needle as i8);
        let chunks = haystack.chunks_exact(32);
        let remainder = chunks.remainder();

        for (i, chunk) in chunks.enumerate() {
            let chunk_vec = _mm256_loadu_si256(chunk.as_ptr() as *const __m256i);
            let cmp = _mm256_cmpeq_epi8(chunk_vec, needle_vec);
            let mask = _mm256_movemask_epi8(cmp);

            if mask != 0 {
                let bit_index = mask.trailing_zeros() as usize;
                return Some(i * 32 + bit_index);
            }
        }

        haystack.len() - remainder.len() + remainder.iter().position(|&b| b == needle)?
    }
}

/// SIMD 向量加法
#[cfg(target_arch = "x86_64")]
pub fn simd_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), result.len());

    unsafe {
        let chunks = a.len() / 8;
        for i in 0..chunks {
            let a_vec = _mm256_loadu_ps(a.as_ptr().add(i * 8));
            let b_vec = _mm256_loadu_ps(b.as_ptr().add(i * 8));
            let sum = _mm256_add_ps(a_vec, b_vec);
            _mm256_storeu_ps(result.as_mut_ptr().add(i * 8), sum);
        }

        for i in (chunks * 8)..a.len() {
            result[i] = a[i] + b[i];
        }
    }
}
```

---

## 最佳实践

### 1. 错误处理

```rust
//! 系统编程中的错误处理

use std::fmt;

#[derive(Debug)]
pub enum KernelError {
    OutOfMemory,
    InvalidAddress,
    PermissionDenied,
    DeviceNotFound,
    IoError { device: String, code: i32 },
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfMemory => write!(f, "Out of memory"),
            Self::InvalidAddress => write!(f, "Invalid memory address"),
            Self::PermissionDenied => write!(f, "Permission denied"),
            Self::DeviceNotFound => write!(f, "Device not found"),
            Self::IoError { device, code } => write!(f, "I/O error on {}: {}", device, code),
        }
    }
}

impl std::error::Error for KernelError {}

pub type KernelResult<T> = Result<T, KernelError>;
```

### 2. 内存安全模式

```rust
//! 安全的内存访问模式

/// 使用 RAII 管理资源
pub struct MappedRegion {
    addr: *mut u8,
    size: usize,
}

impl MappedRegion {
    pub fn new(size: usize) -> Option<Self> {
        let addr = unsafe {
            libc::mmap(std::ptr::null_mut(), size, libc::PROT_READ | libc::PROT_WRITE,
                       libc::MAP_PRIVATE | libc::MAP_ANONYMOUS, -1, 0)
        };

        if addr == libc::MAP_FAILED {
            return None;
        }

        Some(Self { addr: addr as *mut u8, size })
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.addr, self.size) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.addr, self.size) }
    }
}

impl Drop for MappedRegion {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.addr as *mut _, self.size); }
    }
}

unsafe impl Send for MappedRegion {}
unsafe impl Sync for MappedRegion {}
```

### 3. 并发安全

```rust
//! 内核级并发原语

use core::sync::atomic::{AtomicBool, Ordering};
use core::cell::UnsafeCell;

/// 自旋锁
pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for SpinLock<T> {}
unsafe impl<T: Send> Sync for SpinLock<T> {}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> SpinLock<T> {
    pub const fn new(data: T) -> Self {
        Self { locked: AtomicBool::new(false), data: UnsafeCell::new(data) }
    }

    pub fn lock(&self) -> SpinLockGuard<T> {
        while self.locked.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            while self.locked.load(Ordering::Relaxed) {
                core::hint::spin_loop();
            }
        }
        SpinLockGuard { lock: self }
    }
}

impl<'a, T> core::ops::Deref for SpinLockGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { unsafe { &*self.lock.data.get() } }
}

impl<'a, T> core::ops::DerefMut for SpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T { unsafe { &mut *self.lock.data.get() } }
}

impl<'a, T> Drop for SpinLockGuard<'a, T> {
    fn drop(&mut self) { self.lock.locked.store(false, Ordering::Release); }
}
```

---

## 总结

Rust 在系统编程领域提供了独特的优势：

1. **内存安全**: 编译时消除 use-after-free、缓冲区溢出等错误
2. **零成本抽象**: 高级特性不产生运行时开销
3. **并发安全**: 编译时检测数据竞争
4. **跨平台**: 优秀的可移植性
5. **生态丰富**: 完善的嵌入式、操作系统开发工具链

通过本文档介绍的技术和模式，开发者可以构建安全、高效、可靠的系统级软件，从操作系统内核到设备驱动，从虚拟化到网络协议栈，Rust 都是理想的选择。

---

## 参考资源

- [Rust OSDev Wiki](https://wiki.osdev.org/Rust)
- [Writing an OS in Rust](https://os.phil-opp.com/)
- [Rust Embedded Working Group](https://github.com/rust-embedded/wg)
- [Redox OS](https://redox-os.org/)
- [Tock OS](https://tockos.org/)
