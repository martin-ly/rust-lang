# No_std 开发

`no_std` 是 Rust 的一项重要特性，允许在没有标准库的环境下进行开发。
这对于嵌入式系统、操作系统内核和其他资源受限环境至关重要。
本章节深入探讨 no_std 开发的各个方面。

## 目录

- [No_std 开发](#)

## No_std 基础

### 什么是 No_std

`#![no_std]` 属性告诉 Rust 编译器不使用标准库 `std`，而是使用核心库 `core`。
核心库提供了 Rust 的基本类型和基本 trait，但不包含：

- 堆内存分配（需要 `alloc` crate）
- 文件系统操作
- 网络功能
- 线程和进程
- 动态类型（`Box<T>` 等需要 `alloc`）

### 基本配置

**Cargo.toml:**

```toml
[package]
name = "no-std-demo"
version = "0.1.0"
edition = "2021"

[dependencies]
# 核心库，始终可用
core = { version = "1.0.0", optional = true }

# 可选：如果需要堆分配
alloc = { version = "1.0.0", optional = true }

# 嵌入式 HAL
cortex-m = { version = "0.7", optional = true }
cortex-m-rt = { version = "0.7", optional = true }
embedded-hal = { version = "0.2", optional = true }

[features]
default = []
alloc = []
embedded = ["cortex-m", "cortex-m-rt", "embedded-hal"]

[[bin]]
name = "no-std-demo"
```

**src/main.rs:**

```rust
#![no_std]
#![no_main]

// 如果使用 alloc
#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// 主入口点
#[cfg(not(feature = "embedded"))]
#[no_mangle]
pub extern "C" fn main() -> ! {
    // 程序逻辑
    loop {}
}

/// 嵌入式入口点
#[cfg(feature = "embedded")]
#[cortex_m_rt::entry]
fn main() -> ! {
    // 嵌入式程序逻辑
    loop {}
}

/// Panic 处理程序（必须）
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
```

### 语言项（Lang Items）

在 no_std 环境中，某些标准功能需要手动实现：

```rust
#![feature(lang_items)]
#![no_std]

// 提供基本类型的语言项
#[lang = "eh_personality"]
fn rust_eh_personality() {}

// 用于 panic 展开（如果不使用 unwinding）
#[lang = "panic_impl"]
fn rust_begin_panic(info: &core::panic::PanicInfo) -> ! {
    // 记录 panic 信息
    loop {}
}
```

### 错误处理

在 no_std 中实现错误处理：

```rust
#![no_std]

use core::fmt;

/// 无分配的错误类型
pub enum Error {
    InvalidInput,
    BufferOverflow,
    Timeout,
    HardwareError(u32),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidInput => write!(f, "Invalid input"),
            Error::BufferOverflow => write!(f, "Buffer overflow"),
            Error::Timeout => write!(f, "Operation timed out"),
            Error::HardwareError(code) => write!(f, "Hardware error: {}", code),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

// 实现 Error trait（需要 nightly 或自定义）
#[cfg(feature = "nightly")]
impl core::error::Error for Error {}

/// 使用结果类型
pub type Result<T> = core::result::Result<T, Error>;

/// 错误转换 trait
pub trait IntoError {
    fn into_error(self) -> Error;
}

impl IntoError for u32 {
    fn into_error(self) -> Error {
        Error::HardwareError(self)
    }
}
```

## 嵌入式开发

### Cortex-M 开发

**Cargo.toml:**

```toml
[package]
name = "cortex-m-demo"
version = "0.1.0"
edition = "2021"

[dependencies]
cortex-m = { version = "0.7.7", features = ["critical-section-single-core"] }
cortex-m-rt = "0.7"
panic-halt = "0.2"
embedded-hal = "0.2"
nb = "1.1"

# 设备支持（例如 STM32）
stm32f4xx-hal = { version = "0.17", features = ["stm32f407"] }

[profile.release]
opt-level = 'z'
lto = true
```

**memory.x (链接器脚本):**

```
MEMORY
{
  /* FLASH 内存区域 */
  FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 1024K

  /* SRAM 内存区域 */
  RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 128K

  /* CCM 内存（仅数据） */
  CCM (rw) : ORIGIN = 0x10000000, LENGTH = 64K
}

/* 栈顶初始化 */
__stack_bottom = ORIGIN(RAM) + LENGTH(RAM);

ENTRY(Reset)

SECTIONS
{
  .text :
  {
    KEEP(*(.vector_table))
    *(.text*)
    *(.rodata*)
    . = ALIGN(4);
  } > FLASH

  .data : AT(ADDR(.text) + SIZEOF(.text))
  {
    . = ALIGN(4);
    __data_start = .;
    *(.data*)
    . = ALIGN(4);
    __data_end = .;
  } > RAM

  .bss :
  {
    . = ALIGN(4);
    __bss_start = .;
    *(.bss*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end = .;
  } > RAM

  __data_load = LOADADDR(.data);
}
```

**src/main.rs:**

```rust
#![no_std]
#![no_main]

use cortex_m::asm;
use cortex_m_rt::entry;
use panic_halt as _;
use stm32f4xx_hal as hal;

use hal::{pac, prelude::*, delay::Delay};

#[entry]
fn main() -> ! {
    // 获取外设访问
    let dp = pac::Peripherals::take().unwrap();
    let cp = cortex_m::Peripherals::take().unwrap();

    // 配置时钟
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr
        .use_hse(8.MHz())
        .sysclk(168.MHz())
        .freeze();

    // 配置 GPIO
    let gpioa = dp.GPIOA.split();
    let mut led = gpioa.pa5.into_push_pull_output();

    // 创建延迟
    let mut delay = Delay::new(cp.SYST, &clocks);

    // 主循环
    loop {
        led.set_high();
        delay.delay_ms(500u32);

        led.set_low();
        delay.delay_ms(500u32);
    }
}
```

### 硬件抽象层 (HAL)

实现自定义 HAL：

```rust
#![no_std]

use embedded_hal::digital::v2::{InputPin, OutputPin};
use core::marker::PhantomData;

/// GPIO 模式标记
pub struct Input;
pub struct Output;
pub struct AlternateFunction;

/// 通用 GPIO 引脚
pub struct Pin<MODE> {
    port: *mut u32,
    pin: u8,
    _mode: PhantomData<MODE>,
}

// 寄存器地址
const GPIOA_BASE: usize = 0x4002_0000;
const GPIOB_BASE: usize = 0x4002_0400;
const MODER_OFFSET: usize = 0x00;
const ODR_OFFSET: usize = 0x14;
const IDR_OFFSET: usize = 0x10;

impl<MODE> Pin<MODE> {
    /// 创建新的 GPIO 引脚
    ///
    /// # Safety
    /// - 端口地址必须有效
    /// - 引脚号必须在 0-15 范围内
    pub unsafe fn new(port: char, pin: u8) -> Self {
        let port_base = match port {
            'A' => GPIOA_BASE,
            'B' => GPIOB_BASE,
            _ => panic!("Invalid port"),
        };

        Pin {
            port: port_base as *mut u32,
            pin,
            _mode: PhantomData,
        }
    }

    fn moder(&self) -> *mut u32 {
        (self.port as usize + MODER_OFFSET) as *mut u32
    }

    fn odr(&self) -> *mut u32 {
        (self.port as usize + ODR_OFFSET) as *mut u32
    }

    fn idr(&self) -> *mut u32 {
        (self.port as usize + IDR_OFFSET) as *mut u32
    }
}

impl Pin<Output> {
    /// 配置为输出模式
    pub fn into_output(self) -> Pin<Output> {
        unsafe {
            let moder = self.moder();
            let val = core::ptr::read_volatile(moder);
            let mask = 0b11 << (self.pin * 2);
            let new_val = (val & !mask) | (0b01 << (self.pin * 2));
            core::ptr::write_volatile(moder, new_val);
        }

        Pin {
            port: self.port,
            pin: self.pin,
            _mode: PhantomData,
        }
    }

    pub fn set_high(&mut self) {
        unsafe {
            core::ptr::write_volatile(self.odr(), 1 << self.pin);
        }
    }

    pub fn set_low(&mut self) {
        unsafe {
            core::ptr::write_volatile(self.odr(), 0 << self.pin);
        }
    }
}

impl OutputPin for Pin<Output> {
    type Error = ();

    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_high();
        Ok(())
    }

    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.set_low();
        Ok(())
    }
}
```

### 中断处理

```rust
#![no_std]
#![no_main]

use cortex_m::peripheral::NVIC;
use cortex_m_rt::{entry, exception};
use stm32f4xx_hal::{pac, interrupt};

/// 中断服务程序
#[interrupt]
fn TIM2() {
    // 清除中断标志
    unsafe {
        let tim2 = &(*pac::TIM2::ptr());
        tim2.sr.modify(|_, w| w.uif().clear());
    }

    // 中断处理逻辑
    unsafe {
        TICK_COUNT += 1;
    }
}

static mut TICK_COUNT: u32 = 0;

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();

    // 配置定时器 2
    let tim2 = dp.TIM2;

    // 启用 TIM2 中断
    unsafe {
        NVIC::unmask(interrupt::TIM2);
    }

    loop {
        cortex_m::asm::wfi(); // 等待中断
    }
}
```

## 裸机编程

### 引导程序

```rust
#![no_std]
#![no_main]

use core::arch::global_asm;

// 汇编启动代码
global_asm!(
    r#"
    .section .text._start
    .global _start
    .type _start, @function

_start:
    // 设置栈指针
    ldr sp, =__stack_bottom

    // 清零 BSS 段
    ldr r4, =__bss_start
    ldr r5, =__bss_end
    mov r6, #0
1:
    cmp r4, r5
    bge 2f
    str r6, [r4], #4
    b 1b
2:
    // 复制数据段
    ldr r4, =__data_load
    ldr r5, =__data_start
    ldr r6, =__data_end
3:
    cmp r5, r6
    bge 4f
    ldr r7, [r4], #4
    str r7, [r5], #4
    b 3b
4:
    // 跳转到 Rust 主函数
    bl rust_main

    // 如果返回，无限循环
    b .
    "#
);

#[no_mangle]
pub extern "C" fn rust_main() -> ! {
    // 初始化 UART
    uart_init();

    // 打印启动消息
    println!("Bare-metal Rust booted!");

    // 主循环
    loop {
        // 处理任务
    }
}
```

### 内存管理单元 (MMU) 配置

```rust
/// ARMv8-A MMU 配置
pub struct MMU;

impl MMU {
    /// 启用 MMU
    pub unsafe fn enable() {
        // 设置 TTBR0（第一级页表）
        let ttbr0 = PAGE_TABLE_L1.as_ptr() as u64;
        core::arch::asm!(
            "msr ttbr0_el1, {}",
            in(reg) ttbr0,
            options(nostack, preserves_flags)
        );

        // 配置 TCR（翻译控制寄存器）
        let tcr: u64 =
            (0b00 << 0) |      // 4KB 粒度
            (0b11 << 8) |      // 内部可共享
            (0b11 << 10) |     // 外部可共享
            (0b01 << 12) |     // 48 位地址空间
            (0b100 << 32);     // 48 位 TTBR0

        core::arch::asm!(
            "msr tcr_el1, {}",
            in(reg) tcr,
            options(nostack, preserves_flags)
        );

        // 配置 MAIR（内存属性间接寄存器）
        let mair: u64 =
            (0x00 << 0) |      // 设备内存
            (0xFF << 8);       // 普通可缓存内存

        core::arch::asm!(
            "msr mair_el1, {}",
            in(reg) mair,
            options(nostack, preserves_flags)
        );

        // 使 TLB 失效
        core::arch::asm!(
            "tlbi vmalle1is",
            "dsb ish",
            "isb",
            options(nostack, preserves_flags)
        );

        // 启用 MMU
        let sctlr: u64;
        core::arch::asm!(
            "mrs {}, sctlr_el1",
            out(reg) sctlr,
            options(nostack, preserves_flags)
        );

        core::arch::asm!(
            "msr sctlr_el1, {}",
            in(reg) sctlr | 0x1,
            options(nostack, preserves_flags)
        );

        // 执行隔离
        core::arch::asm!("isb", options(nostack, preserves_flags));
    }
}

/// 页表定义（简化版）
#[repr(align(4096))]
static mut PAGE_TABLE_L1: [u64; 512] = [0; 512];

pub unsafe fn setup_page_table() {
    // 身份映射前 1GB
    for i in 0..512 {
        PAGE_TABLE_L1[i] =
            (i << 30) |     // 物理地址
            0b11 |          // 有效且是块描述符
            (0x1 << 2) |    // 索引到 MAIR 0
            (0b11 << 8) |   // 可访问
            (0b01 << 10) |  // 非特权可访问
            (0b11 << 53);   // PXN + UXN
    }
}
```

## 自定义分配器

### 全局分配器实现

```rust
#![feature(allocator_api)]
#![no_std]

use core::alloc::{GlobalAlloc, Layout, Allocator};
use core::ptr::NonNull;
use core::cell::UnsafeCell;

/// 简单的固定块分配器
pub struct FixedBlockAllocator {
    // 内存池
    heap: UnsafeCell<[u8; HEAP_SIZE]>,
    // 空闲列表
    free_list: UnsafeCell<*mut Block>,
}

const HEAP_SIZE: usize = 1024 * 1024; // 1MB 堆
const BLOCK_SIZE: usize = 64;         // 64 字节块
const NUM_BLOCKS: usize = HEAP_SIZE / BLOCK_SIZE;

#[repr(C)]
struct Block {
    next: *mut Block,
}

unsafe impl Sync for FixedBlockAllocator {}
unsafe impl Send for FixedBlockAllocator {}

impl FixedBlockAllocator {
    pub const fn new() -> Self {
        FixedBlockAllocator {
            heap: UnsafeCell::new([0; HEAP_SIZE]),
            free_list: UnsafeCell::new(core::ptr::null_mut()),
        }
    }

    /// 初始化分配器
    ///
    /// # Safety
    /// 必须在任何分配操作之前调用，且只能调用一次
    pub unsafe fn init(&self) {
        let heap_start = (*self.heap.get()).as_mut_ptr();
        let free_list = self.free_list.get();

        *free_list = heap_start as *mut Block;
        let mut current = *free_list;

        for _ in 0..NUM_BLOCKS - 1 {
            let next = (current as *mut u8).add(BLOCK_SIZE) as *mut Block;
            (*current).next = next;
            current = next;
        }

        (*current).next = core::ptr::null_mut();
    }
}

unsafe impl GlobalAlloc for FixedBlockAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // 检查对齐要求
        if layout.align() > BLOCK_SIZE {
            return core::ptr::null_mut();
        }

        // 检查大小
        if layout.size() > BLOCK_SIZE {
            return core::ptr::null_mut();
        }

        let free_list = self.free_list.get();

        if (*free_list).is_null() {
            return core::ptr::null_mut();
        }

        let block = *free_list;
        *free_list = (*block).next;

        block as *mut u8
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let free_list = self.free_list.get();
        let block = ptr as *mut Block;

        (*block).next = *free_list;
        *free_list = block;
    }
}

// 声明全局分配器
#[global_allocator]
static ALLOCATOR: FixedBlockAllocator = FixedBlockAllocator::new();

// OOM 处理
#[alloc_error_handler]
fn alloc_error_handler(layout: Layout) -> ! {
    panic!("Allocation failed: {:?}", layout);
}
```

### 伙伴系统分配器

```rust
use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;

const MIN_BLOCK_SIZE: usize = 16;     // 最小块大小
const MAX_BLOCK_SIZE: usize = 65536;  // 最大块大小
const NUM_ORDERS: usize = 13;         // log2(65536/16) + 1

/// 伙伴系统分配器
pub struct BuddyAllocator {
    // 每个阶数的空闲列表
    free_lists: UnsafeCell<[*mut Block; NUM_ORDERS]>,
    // 内存起始地址
    base: usize,
    // 内存总大小
    size: usize,
}

#[repr(C)]
struct Block {
    next: *mut Block,
    order: u8,
}

impl BuddyAllocator {
    pub const fn new() -> Self {
        BuddyAllocator {
            free_lists: UnsafeCell::new([core::ptr::null_mut(); NUM_ORDERS]),
            base: 0,
            size: 0,
        }
    }

    /// 初始化分配器
    ///
    /// # Safety
    /// - heap_start 必须有效且对齐到 MAX_BLOCK_SIZE
    /// - heap_size 必须是 MAX_BLOCK_SIZE 的倍数
    pub unsafe fn init(&mut self, heap_start: *mut u8, heap_size: usize) {
        self.base = heap_start as usize;
        self.size = heap_size;

        // 初始时整个堆是一个最大块
        let order = NUM_ORDERS - 1;
        let block = heap_start as *mut Block;
        (*block).next = core::ptr::null_mut();
        (*block).order = order as u8;

        (*self.free_lists.get())[order] = block;
    }

    fn size_to_order(size: usize) -> usize {
        let mut order = 0;
        let mut block_size = MIN_BLOCK_SIZE;

        while block_size < size && order < NUM_ORDERS {
            block_size *= 2;
            order += 1;
        }

        order
    }

    fn block_size(order: usize) -> usize {
        MIN_BLOCK_SIZE << order
    }

    fn get_buddy(&self, block: *mut Block, order: usize) -> *mut Block {
        let block_addr = block as usize;
        let size = Self::block_size(order);
        ((block_addr - self.base) ^ size) + self.base as *mut Block
    }
}

unsafe impl GlobalAlloc for BuddyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size().max(layout.align());
        let order = Self::size_to_order(size);

        // 查找合适的块
        let free_lists = self.free_lists.get();

        for search_order in order..NUM_ORDERS {
            if !(*free_lists)[search_order].is_null() {
                // 找到可用块
                let block = (*free_lists)[search_order];
                (*free_lists)[search_order] = (*block).next;

                // 分割块直到达到所需大小
                let mut current_order = search_order;
                while current_order > order {
                    current_order -= 1;
                    let size = Self::block_size(current_order);
                    let buddy = (block as usize + size) as *mut Block;

                    (*buddy).next = (*free_lists)[current_order];
                    (*buddy).order = current_order as u8;
                    (*free_lists)[current_order] = buddy;
                }

                return block as *mut u8;
            }
        }

        core::ptr::null_mut()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let size = layout.size().max(layout.align());
        let order = Self::size_to_order(size);
        let free_lists = self.free_lists.get();

        let mut block = ptr as *mut Block;
        (*block).order = order as u8;

        let mut current_order = order;

        // 尝试合并伙伴
        while current_order < NUM_ORDERS - 1 {
            let buddy = self.get_buddy(block, current_order);

            // 检查伙伴是否空闲且同阶
            let mut prev: *mut Block = core::ptr::null_mut();
            let mut current = (*free_lists)[current_order];
            let mut found = false;

            while !current.is_null() {
                if current == buddy && (*current).order == current_order as u8 {
                    found = true;
                    // 从空闲列表移除伙伴
                    if prev.is_null() {
                        (*free_lists)[current_order] = (*current).next;
                    } else {
                        (*prev).next = (*current).next;
                    }
                    break;
                }
                prev = current;
                current = (*current).next;
            }

            if !found {
                break;
            }

            // 合并
            if buddy < block {
                block = buddy;
            }
            current_order += 1;
        }

        // 将块加入空闲列表
        (*block).next = (*free_lists)[current_order];
        (*block).order = current_order as u8;
        (*free_lists)[current_order] = block;
    }
}
```

## Panic 处理

### 自定义 Panic Handler

```rust
#![no_std]

use core::panic::PanicInfo;
use core::fmt::Write;

/// 串口输出（简化）
struct Uart;

impl Write for Uart {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for byte in s.bytes() {
            unsafe {
                // 假设 UART 数据寄存器在 0x4000_0000
                core::ptr::write_volatile(0x4000_0000 as *mut u8, byte);
            }
        }
        Ok(())
    }
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut uart = Uart;

    // 打印 panic 信息
    let _ = writeln!(uart, "\n!!! PANIC !!!");

    if let Some(location) = info.location() {
        let _ = writeln!(uart, "Location: {}:{}",
            location.file(),
            location.line()
        );
    }

    if let Some(message) = info.message() {
        let _ = write!(uart, "Message: ");
        let _ = core::fmt::write(&mut uart, *message);
        let _ = writeln!(uart);
    }

    // 打印回溯（如果启用）
    print_backtrace();

    // 停止或重启
    loop {
        unsafe { core::arch::asm!("wfe"); }
    }
}

/// 简单的回溯打印
#[cfg(feature = "backtrace")]
fn print_backtrace() {
    // 使用 libunwind 或自定义回溯实现
}

#[cfg(not(feature = "backtrace"))]
fn print_backtrace() {}
```

### 异常处理（ARM Cortex-M）

```rust
use cortex_m_rt::{exception, ExceptionFrame};

#[exception]
unsafe fn HardFault(ef: &ExceptionFrame) -> ! {
    // 打印异常信息
    let _ = writeln!(Uart, "Hard Fault!");
    let _ = writeln!(Uart, "R0:  0x{:08X}", ef.r0);
    let _ = writeln!(Uart, "R1:  0x{:08X}", ef.r1);
    let _ = writeln!(Uart, "R2:  0x{:08X}", ef.r2);
    let _ = writeln!(Uart, "R3:  0x{:08X}", ef.r3);
    let _ = writeln!(Uart, "R12: 0x{:08X}", ef.r12);
    let _ = writeln!(Uart, "LR:  0x{:08X}", ef.lr);
    let _ = writeln!(Uart, "PC:  0x{:08X}", ef.pc);
    let _ = writeln!(Uart, "PSR: 0x{:08X}", ef.xpsr);

    loop {
        core::arch::asm!("wfi");
    }
}

#[exception]
unsafe fn DefaultHandler(irqn: i16) {
    let _ = writeln!(Uart, "Unhandled IRQ: {}", irqn);
}
```

## 硬件抽象层

### 设备驱动框架

```rust
#![no_std]

/// 设备驱动 trait
pub trait Driver {
    type Error;

    fn init(&mut self) -> Result<(), Self::Error>;
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error>;
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error>;
}

/// 平台抽象 trait
pub trait Platform {
    type Serial: Driver;
    type Timer: Timer;
    type Gpio: Gpio;

    fn serial(&mut self) -> &mut Self::Serial;
    fn timer(&mut self) -> &mut Self::Timer;
    fn gpio(&mut self) -> &mut Self::Gpio;
}

pub trait Timer {
    type Error;

    fn now(&self) -> u64;
    fn delay_us(&mut self, us: u32);
    fn delay_ms(&mut self, ms: u32);
}

pub trait Gpio {
    type Error;
    type Pin;

    fn set_high(&mut self, pin: &mut Self::Pin) -> Result<(), Self::Error>;
    fn set_low(&mut self, pin: &mut Self::Pin) -> Result<(), Self::Error>;
    fn is_high(&self, pin: &Self::Pin) -> Result<bool, Self::Error>;
}

/// 平台初始化宏
#[macro_export]
macro_rules! platform_init {
    ($platform:ty) => {
        static mut PLATFORM: Option<$platform> = None;

        pub fn platform() -> &'static mut $platform {
            unsafe { PLATFORM.as_mut().unwrap() }
        }

        pub fn init_platform(p: $platform) {
            unsafe {
                PLATFORM = Some(p);
            }
        }
    };
}
```

### DMA 控制器驱动

```rust
/// DMA 控制器
pub struct DmaController {
    base: *mut u32,
}

impl DmaController {
    pub const fn new(base: usize) -> Self {
        DmaController {
            base: base as *mut u32,
        }
    }

    /// 配置 DMA 传输
    ///
    /// # Safety
    /// - src 和 dst 必须有效
    /// - src 和 dst 必须在传输期间保持有效
    pub unsafe fn transfer(
        &mut self,
        channel: u8,
        src: *const u8,
        dst: *mut u8,
        len: usize,
    ) -> Result<(), DmaError> {
        if channel >= 8 {
            return Err(DmaError::InvalidChannel);
        }

        // 等待通道就绪
        while self.is_busy(channel) {}

        // 配置源地址
        self.write_reg(0x10 + channel as usize * 0x20, src as u32);

        // 配置目标地址
        self.write_reg(0x14 + channel as usize * 0x20, dst as u32);

        // 配置传输数量
        self.write_reg(0x18 + channel as usize * 0x20, len as u32);

        // 启动传输
        self.write_reg(0x08, 1 << channel);

        Ok(())
    }

    fn is_busy(&self, channel: u8) -> bool {
        let status = self.read_reg(0x00);
        (status & (1 << channel)) != 0
    }

    fn read_reg(&self, offset: usize) -> u32 {
        unsafe { core::ptr::read_volatile(self.base.add(offset)) }
    }

    fn write_reg(&mut self, offset: usize, value: u32) {
        unsafe { core::ptr::write_volatile(self.base.add(offset), value) }
    }
}

#[derive(Debug)]
pub enum DmaError {
    InvalidChannel,
    BufferError,
}
```

---

`no_std` 开发是 Rust 在系统编程领域的关键优势。通过掌握这些技术，你可以将 Rust 的安全性保证带到嵌入式系统、操作系统内核和其他资源受限的环境中。记住以下关键点：

1. **最小化 unsafe 代码**：使用硬件抽象层和安全包装器
2. **仔细的内存管理**：考虑使用自定义分配器或避免堆分配
3. **全面的测试**：使用 QEMU 和硬件在环测试
4. **清晰的文档**：记录所有安全契约和假设
5. **工具链熟练使用**：掌握 OpenOCD、GDB 和硬件调试器
