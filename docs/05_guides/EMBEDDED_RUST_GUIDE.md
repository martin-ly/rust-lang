# 嵌入式 Rust 专题指南

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 文档定位

本指南为官方 **Embedded Rust Book** 的入口与项目内导航，帮助在开发嵌入式 Rust 应用时快速定位到本项目的相关模块和官方资源。

---

## 官方 Embedded 资源入口

| 资源 | URL | 说明 |
| :--- | :--- | :--- |
| **Embedded Rust Book** | <https://doc.rust-lang.org/embedded-book/> | 官方嵌入式 Rust 教程 |
| **Discovery Book** | <https://docs.rust-embedded.org/discovery/> | 零基础嵌入式入门 |
| **Embedonomicon** | <https://docs.rust-embedded.org/embedonomicon/> | 嵌入式 Rust 底层细节 |
| **Embedded FAQ** | <https://docs.rust-embedded.org/faq.html> | 常见问题 |
| **Comprehensive Rust: Bare Metal** | <https://google.github.io/comprehensive-rust/bare-metal.html> | Google 裸机开发课程 |

---

## 本项目对应模块

| 嵌入式主题 | 官方 Embedded Book | 本项目对应 |
| :--- | :--- | :--- |
| 所有权与内存安全 | 内存管理、无堆 | [C01 所有权](../../crates/c01_ownership_borrow_scope/) |
| 类型系统与 no_std | 最小运行时 | [C02 类型系统](../../crates/c02_type_system/) |
| 并发与中断 | 临界区、原子操作 | [C05 线程与并发](../../crates/c05_threads/) |
| 进程与系统调用 | - | [C07 进程管理](../../crates/c07_process/) |
| WASM 与边缘计算 | - | [C12 WASM](../../crates/c12_wasm/) |

---

## 快速开始示例

### 1. 最小 no_std 程序

```rust
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 程序入口点
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

### 2. 嵌入式 HAL 示例

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;
use embedded_hal::digital::OutputPin;
use stm32f4xx_hal::{pac, prelude::*};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let gpioc = dp.GPIOC.split();
    
    let mut led = gpioc.pc13.into_push_pull_output();
    
    loop {
        led.set_high().unwrap();
        cortex_m::asm::delay(8_000_000);
        led.set_low().unwrap();
        cortex_m::asm::delay(8_000_000);
    }
}
```

### 3. 中断处理示例

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;
use cortex_m::peripheral::NVIC;
use stm32f4xx_hal::pac::{TIM2, interrupt};
use core::cell::RefCell;
use cortex_m::interrupt::Mutex;

static TIMER: Mutex<RefCell<Option<TIM2>>> = Mutex::new(RefCell::new(None));

#[entry]
fn main() -> ! {
    let cp = cortex_m::Peripherals::take().unwrap();
    let dp = pac::Peripherals::take().unwrap();
    
    // 初始化定时器
    let tim2 = dp.TIM2;
    cortex_m::interrupt::free(|cs| {
        TIMER.borrow(cs).replace(Some(tim2));
    });
    
    // 启用中断
    unsafe {
        NVIC::unmask(interrupt::TIM2);
    }
    
    loop {
        cortex_m::asm::wfi();
    }
}

#[interrupt]
fn TIM2() {
    cortex_m::interrupt::free(|cs| {
        if let Some(ref mut tim2) = TIMER.borrow(cs).borrow_mut().as_mut() {
            // 清除中断标志
            tim2.sr.modify(|_, w| w.uif().clear_bit());
        }
    });
}
```

### 4. 无锁数据结构

```rust
use core::sync::atomic::{AtomicU32, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(0);

fn increment_counter() {
    COUNTER.fetch_add(1, Ordering::Relaxed);
}

fn get_counter() -> u32 {
    COUNTER.load(Ordering::Relaxed)
}
```

### 5. 内存管理技巧

```rust
#![no_std]

use core::alloc::{GlobalAlloc, Layout};

// 自定义分配器（用于有堆环境）
struct EmbeddedAllocator;

unsafe impl GlobalAlloc for EmbeddedAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        // 实现分配逻辑
        core::ptr::null_mut()
    }
    
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // 实现释放逻辑
    }
}

#[global_allocator]
static ALLOCATOR: EmbeddedAllocator = EmbeddedAllocator;

// 静态内存池
static mut BUFFER: [u8; 1024] = [0; 1024];

struct StaticPool {
    used: [bool; 32], // 32 个 32 字节的块
}

impl StaticPool {
    const fn new() -> Self {
        StaticPool { used: [false; 32] }
    }
    
    fn allocate(&mut self, size: usize) -> Option<&'static mut [u8]> {
        let blocks_needed = (size + 31) / 32;
        // 查找连续的块
        for start in 0..(32 - blocks_needed + 1) {
            if self.used[start..start + blocks_needed].iter().all(|&x| !x) {
                for i in start..start + blocks_needed {
                    self.used[i] = true;
                }
                return Some(unsafe { &mut BUFFER[start * 32..start * 32 + size] });
            }
        }
        None
    }
}
```

### 6. RTIC (Real-Time Interrupt-driven Concurrency)

```rust
#![no_std]
#![no_main]

use rtic::app;
use panic_halt as _;

#[app(device = stm32f4xx_hal::pac, peripherals = true)]
mod app {
    use stm32f4xx_hal::prelude::*;
    
    #[shared]
    struct Shared {
        led: LedPin,
    }
    
    #[local]
    struct Local {}
    
    #[init]
    fn init(cx: init::Context) -> (Shared, Local, init::Monotonics) {
        let dp = cx.device;
        let rcc = dp.RCC.constrain();
        let gpioc = dp.GPIOC.split();
        let led = gpioc.pc13.into_push_pull_output();
        
        // 启动任务
        blink::spawn_after(1.secs()).unwrap();
        
        (Shared { led }, Local {}, init::Monotonics())
    }
    
    #[task(shared = [led])]
    fn blink(cx: blink::Context) {
        let led = cx.shared.led;
        // 切换 LED 状态
        led.toggle().unwrap();
        // 重新安排任务
        blink::spawn_after(1.secs()).unwrap();
    }
}
```

---

## 推荐学习路径

1. **前置**: 熟练掌握 C01 所有权、C02 类型系统（本项目核心模块）
2. **入门**: [Discovery Book](https://docs.rust-embedded.org/discovery/)（零嵌入式经验）
3. **进阶**: [Embedded Rust Book](https://doc.rust-lang.org/embedded-book/)（ARM Cortex-M）
4. **深入**: [Embedonomicon](https://docs.rust-embedded.org/embedonomicon/)

---

## 常用嵌入式 Crate

| 用途 | crate | 说明 |
| :--- | :--- | :--- |
| Cortex-M 支持 | cortex-m | Cortex-M 处理器底层支持 |
| Cortex-M RT | cortex-m-rt | 运行时和启动代码 |
| HAL 抽象 | embedded-hal | 硬件抽象层 trait |
| RTOS | rtic | 实时中断驱动并发 |
| 日志 | defmt | 高效嵌入式日志 |
| 测试 | embedded-test | 嵌入式测试框架 |

---

## 最佳实践

### 1. 使用 `const` 进行编译时计算

```rust
const BUFFER_SIZE: usize = 1024;
const SAMPLE_RATE: u32 = 48_000;

static mut BUFFER: [u8; BUFFER_SIZE] = [0; BUFFER_SIZE];
```

### 2. 避免动态分配（无堆环境）

```rust
// 推荐：使用静态缓冲区
static mut TX_BUFFER: [u8; 256] = [0; 256];

// 不推荐（无堆环境）
// let buffer = vec![0; 256];
```

### 3. 中断安全的数据共享

```rust
use core::cell::RefCell;
use cortex_m::interrupt::Mutex;

static SHARED_DATA: Mutex<RefCell<u32>> = Mutex::new(RefCell::new(0));

fn update_data(value: u32) {
    cortex_m::interrupt::free(|cs| {
        *SHARED_DATA.borrow(cs).borrow_mut() = value;
    });
}
```

---

## 相关文档

- [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)
- [C02 类型系统](../../crates/c02_type_system/docs/)
- [C05 线程与并发](../../crates/c05_threads/docs/)
- [C12 WASM](../../crates/c12_wasm/docs/)
- [官方 Embedded Book](https://doc.rust-lang.org/embedded-book/)
- [BEST_PRACTICES.md](./BEST_PRACTICES.md)
