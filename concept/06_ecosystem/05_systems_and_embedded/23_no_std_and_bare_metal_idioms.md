> **内容分级**: [专家级]
> **代码状态**: ⚠️ 裸机/目标平台相关代码标注 `rust,ignore`/`no_run`， host 平台无法直接编译
> **定理链**: N/A — 描述性/工程性文档
>
# `#![no_std]` 与裸机编程惯用法
>
> **EN**: `no_std` and Bare-Metal Idioms
> **Summary**: Practical idioms for `#![no_std]` and bare-metal Rust: crate setup, panic handler, custom alloc, critical-section, memory fences, static safety, build-std, target JSON, linker scripts, cortex-m-rt/riscv-rt entry patterns, Embassy executor, and common anti-patterns.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [专家]
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+A+P** — Structure + Application + Procedure
> **双维定位**: P×Cre — 在资源受限硬件上组装可运行、可维护的裸机 crate
> **前置概念**:
> [Rust 嵌入式系统开发](03_embedded_systems.md) ·
> [裸机启动与链接脚本](13_bare_metal_boot_linker_script.md) ·
> [panic_handler 与 no_std 运行时](18_panic_runtime_no_std.md) ·
> [嵌入式内存分配器](16_embedded_memory_allocators.md) ·
> [no_std 同步原语](15_no_std_synchronization_primitives.md) ·
> [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **后置概念**:
> [PAC 与 HAL 实现](17_pac_hal_implementation.md) ·
> [embedded-hal 与驱动惯用法](24_embedded_hal_and_driver_idioms.md) ·
> [异步 no_std 嵌入式](11_async_no_std_embedded.md) ·
> [no_std 启动流程与运行时深度解析](27_no_std_startup_runtime_deep_dive.md) ·
> [自定义裸机异步执行器](28_custom_bare_metal_async_executor.md) ·
> [嵌入式内存布局与堆安全](29_embedded_memory_layout_and_heap_safety.md) ·
> [安全关键嵌入式 Rust 指南：MISRA-Rust、Ferrocene 与 IEC 61508](30_misra_rust_safety_critical_guidelines.md)

---

> **来源**:
> [The Embedded Rust Book](https://docs.rust-embedded.org/book/) ·
> [The Embedonomicon](https://docs.rust-embedded.org/embedonomicon/) ·
> [cortex-m-rt](https://docs.rs/cortex-m-rt/) ·
> [riscv-rt](https://docs.rs/riscv-rt/) ·
> [critical-section crate](https://docs.rs/critical-section/) ·
> [Embassy Book](https://embassy.dev/book/) · [Ferrous Systems](https://ferrous-systems.com/) ·
> [Knurling](https://knurling.ferrous-systems.com/) ·
> [Rust Reference — no_std](https://doc.rust-lang.org/reference/names/preludes.html#the-no_std-attribute)

---

## 🧠 知识结构图

```mermaid
mindmap
  root((no_std 与裸机惯用法))
    crate 设置
      #![no_std]
      #![no_main]
      panic_handler
      global_allocator
    启动入口
      cortex-m-rt entry
      riscv-rt entry
      自定义 _start
    同步与顺序
      critical-section
      compiler_fence
      fence
      AcquireRelease
    静态安全
      static_mut_refs 禁用
      Mutex<RefCell<T>>
      AtomicXxx
    构建与目标
      build-std
      target JSON
      linker script
    运行时选择
      cortex-m-rt
      riscv-rt
      Embassy executor
    反模式
      static mut
      栈上 DMA 缓冲区
      临界区内阻塞
```

## 📑 目录

- [`#![no_std]` 与裸机编程惯用法](#no_std-与裸机编程惯用法)
  - [🧠 知识结构图](#-知识结构图)
  - [📑 目录](#-目录)
  - [一、权威定义](#一权威定义)
  - [二、最小可启动 `#![no_std]` crate](#二最小可启动-no_std-crate)
  - [三、关键属性矩阵](#三关键属性矩阵)
  - [四、panic handler 与运行时入口模式](#四panic-handler-与运行时入口模式)
    - [4.1 `cortex-m-rt` 入口](#41-cortex-m-rt-入口)
    - [4.2 `riscv-rt` 入口](#42-riscv-rt-入口)
    - [4.3 自定义 `_start` / 链接脚本](#43-自定义-_start--链接脚本)
  - [五、自定义分配器与 `heapless`](#五自定义分配器与-heapless)
  - [六、`critical-section` 与内存屏障](#六critical-section-与内存屏障)
  - [七、`static` vs `static mut` 安全](#七static-vs-static-mut-安全)
  - [八、`build-std` 与自定义 target JSON](#八build-std-与自定义-target-json)
  - [九、链接脚本核心约定](#九链接脚本核心约定)
  - [十、Embassy 裸机执行器](#十embassy-裸机执行器)
  - [十一、常见 no\_std 反模式](#十一常见-no_std-反模式)
  - [十二、反例与失效模式](#十二反例与失效模式)
  - [十三、边界测试](#十三边界测试)
    - [13.1 边界测试：`no_std` 中误用 `std`](#131-边界测试no_std-中误用-std)
    - [13.2 边界测试：缺少 `panic_handler`](#132-边界测试缺少-panic_handler)
    - [13.3 边界测试：直接访问 `static mut`](#133-边界测试直接访问-static-mut)
    - [13.4 边界测试：`Vec` 在未初始化堆上使用](#134-边界测试vec-在未初始化堆上使用)
  - [十四、决策树：裸机技术栈选择](#十四决策树裸机技术栈选择)
  - [十五、相关概念](#十五相关概念)
  - [十六、权威来源索引](#十六权威来源索引)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、权威定义

> **The Embedded Rust Book**: `#![no_std]` tells the Rust compiler not to automatically import the standard library (`std`) prelude. It does not disable the `core` library, and `alloc` can still be used if a global allocator is provided.

**`#![no_std]`**：禁用标准库预导入的 crate 级属性。`core`（无堆）仍然完整可用；`alloc`（`Vec`、`Box`、`String`）在提供全局分配器后可用。

**裸机（bare-metal）**：没有操作系统负责加载、调度、内存映射与设备驱动，程序直接运行在处理器硬件上，复位向量指向用户提供的启动代码。

**build-std**：Cargo 不稳定特性，用于为自定义目标重新编译 `core`、`alloc`、`compiler_builtins`，是大多数裸机/自定义 target 项目的构建前提。

判定依据：能否成功构建并启动一个 `#![no_std]` 裸机 crate，取决于属性组合、`panic_handler`、入口运行时、链接脚本与目标三元组四者是否一致。

---

## 二、最小可启动 `#![no_std]` crate

```rust,ignore
// src/main.rs（Cortex-M 目标）
#![no_std]
#![no_main]

use core::panic::PanicInfo;
use cortex_m_rt::entry;

#[entry]
fn main() -> ! {
    // 用户代码
    loop {
        cortex_m::asm::wfi();
    }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

```toml
# Cargo.toml
[package]
name = "bare_metal_app"
version = "0.1.0"
edition = "2024"

[dependencies]
cortex-m = "0.7"
cortex-m-rt = "0.7"

[profile.release]
panic = "abort"
```

```toml
# .cargo/config.toml
[target.thumbv7em-none-eabihf]
runner = "probe-rs run --chip STM32F407VG"

[build]
target = "thumbv7em-none-eabihf"

[unstable]
build-std = ["core", "compiler_builtins"]
build-std-features = ["compiler-builtins-mem"]
```

> **要点**：`#![no_main]` 表示不使用 Rust 默认的 `main` 入口符号；`cortex-m-rt` 的 `#[entry]` 宏会生成符合向量表要求的复位处理函数并调用用户 `main`。

---

## 三、关键属性矩阵

| 属性 | 作用对象 | 语义 | 裸机典型用途 | 与 `std` 程序的差异 |
|:---|:---|:---|:---|:---|
| `#![no_std]` | crate | 禁用 `std` 预导入 | 所有裸机/嵌入式 crate | `std` 的线程/文件/网络不可用 |
| `#![no_main]` | crate | 不生成默认 `main` 符号 | 由运行时提供入口 | `std` 程序通常自动生成 |
| `#[panic_handler]` | 函数 | 定义 panic 行为 | 必须提供 | `std` 已提供默认 handler |
| `#[global_allocator]` | 静态 `GlobalAlloc` | 启用 `alloc` | 需要堆时配置 | `std` 使用系统分配器 |
| `#[no_mangle]` | 项 | 禁止符号名混淆 | ISR、C ABI、启动符号 | 同样可用，但裸机更依赖 |
| `#[export_name = "..."]` | 项 | 显式设置链接符号名 | 向量表、启动文件 | 比 `#[no_mangle]` 更精确 |
| `#[link_section = ".name"]` | 静态/函数 | 放入指定 section | 向量表、bootloader 标记 | 同样可用 |
| `#[used]` | 静态 | 防止 LLVM 优化删除 | panic 信息表、启动标记 | 同样可用 |
| `#[repr(C)]` | 类型 | C 兼容布局 | MMIO 寄存器映射 | 同样常用 |

判定依据：裸机 crate 中，属性是“编译器与链接器之间的契约”，组合错误通常表现为链接错误（`undefined reference`）或启动崩溃，而非类型错误。

---

## 四、panic handler 与运行时入口模式

### 4.1 `cortex-m-rt` 入口

[cortex-m-rt](https://docs.rs/cortex-m-rt/) 提供 `#[entry]`、`#[exception]`、`#[interrupt]` 三个宏，分别对应主入口、ARM 架构异常和外设中断。

```rust,ignore
#![no_std]
#![no_main]

use cortex_m_rt::{entry, exception, interrupt};
use stm32f4::stm32f407::Peripherals;

#[entry]
fn main() -> ! {
    let _dp = Peripherals::take().unwrap();
    loop { cortex_m::asm::wfi(); }
}

#[exception]
unsafe fn HardFault(_ef: &cortex_m_rt::ExceptionFrame) -> ! {
    loop {}
}

#[interrupt]
fn TIM2() {
    // 处理定时器中断
}
```

### 4.2 `riscv-rt` 入口

[riscv-rt](https://docs.rs/riscv-rt/) 与 `cortex-m-rt` 类似，但向量表与异常模型遵循 RISC-V 规范。

```rust,ignore
#![no_std]
#![no_main]

use riscv_rt::entry;

#[entry]
fn main() -> ! {
    loop { riscv::asm::wfi(); }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
```

### 4.3 自定义 `_start` / 链接脚本

当 `cortex-m-rt`/`riscv-rt` 不满足需求（如自定义启动序列、二级 bootloader、非标准向量表）时，可手写 `_start` 并在链接脚本中指定入口。

```rust,ignore
#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    unsafe extern "C" {
        static mut _sbss: u8;
        static mut _ebss: u8;
        static mut _sdata: u8;
        static mut _edata: u8;
        static _sidata: u8;
    }
    let bss_size = core::ptr::addr_of!(_ebss) as usize - core::ptr::addr_of!(_sbss) as usize;
    unsafe {
        core::ptr::write_bytes(core::ptr::addr_of_mut!(_sbss), 0, bss_size);
    }
    let data_size = core::ptr::addr_of!(_edata) as usize - core::ptr::addr_of!(_sdata) as usize;
    unsafe {
        core::ptr::copy_nonoverlapping(
            core::ptr::addr_of!(_sidata),
            core::ptr::addr_of_mut!(_sdata),
            data_size,
        );
    }
    main()
}

fn main() -> ! {
    loop {}
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

> **注意**：自定义 `_start` 必须手动完成 `.bss` 清零、`.data` 复制、栈指针设置（部分硬件自动设置 SP）以及最终调用 `main`；细节见 [裸机启动与链接脚本](13_bare_metal_boot_linker_script.md)。使用 `core::ptr::addr_of!` / `addr_of_mut!` 可避免直接对 `static mut` 取引用。

---

## 五、自定义分配器与 `heapless`

在 `#![no_std]` 中使用 `alloc` 需要全局分配器；若不想引入堆，可使用 `heapless` 等静态容量容器。

```rust,ignore
#![no_std]
extern crate alloc;

use alloc::boxed::Box;
use embedded_alloc::TlsfHeap;

#[global_allocator]
static HEAP: TlsfHeap = TlsfHeap::empty();

#[entry]
fn main() -> ! {
    // 链接脚本需定义 _heap_start / _heap_end
    extern "C" {
        static mut _heap_start: u8;
        static mut _heap_end: u8;
    }
    unsafe {
        let start = core::ptr::addr_of_mut!(_heap_start);
        let end = core::ptr::addr_of!(_heap_end);
        HEAP.init(start, end as usize - start as usize);
    }
    let _b = Box::new(42);
    loop {}
}
```

```rust,ignore
// 无堆方案：heapless 静态容量容器
use heapless::Vec;

static mut BUFFER: Vec<u8, 64> = Vec::new();

fn push_sample(v: u8) {
    unsafe {
        let _ = BUFFER.push(v); // 满时返回 Err，不会分配
    }
}
```

判定依据：裸机中是否使用堆是早期架构决策。`heapless` 提供最可预测的行为；TLSF 提供确定性动态分配；通用分配器需要持续监控碎片。

---

## 六、`critical-section` 与内存屏障

`critical-section` 是嵌入式临界区的事实标准；内存屏障保证编译器和 CPU 的访问顺序。

```rust,ignore
use critical_section::with;
use core::cell::RefCell;

static COUNTER: critical_section::Mutex<RefCell<u32>> =
    critical_section::Mutex::new(RefCell::new(0));

fn increment() {
    with(|cs| {
        *COUNTER.borrow(cs).borrow_mut() += 1;
    });
}
```

**内存屏障选择**：

| 屏障 | 作用 | 典型场景 |
|:---|:---|:---|
| `compiler_fence(Ordering::Acquire/Release)` | 阻止编译器重排，不插入 CPU 指令 | 中断标志、DMA 描述符 |
| `fence(Ordering::SeqCst)` | 全内存顺序，插入 DMB/fence 指令 | 多核共享变量、外设寄存器 |
| `atomic::fence` | 同 `core::sync::atomic::fence` | 与原子变量配合使用 |

```rust,ignore
// DMA 启动前确保对缓冲区的写入已对外设可见
static mut BUF: [u8; 256] = [0; 256];

unsafe fn start_dma() {
    let buf = &mut BUF;
    buf[0] = 0x55;
    core::sync::atomic::fence(core::sync::atomic::Ordering::Release);
    // 现在写入 DMA 控制寄存器
    (*DMA::ptr()).m0ar.write(|w| w.bits(buf.as_ptr() as u32));
}
```

判定依据：单核裸机中 `compiler_fence` 通常足够；多核或带 cache/DMA 写回的系统需要 `fence`。错误选择会导致“变量已更新但外设看不到”的静默错误。

---

## 七、`static` vs `static mut` 安全

从 Rust 2024 Edition 起，`static_mut_refs` lint 提升为硬错误，直接访问 `static mut` 不再允许。裸机中应改用以下模式：

| 模式 | 适用数据 | 说明 |
|:---|:---|:---|
| `static FOO: AtomicU32` | 整数/标志 | 最安全，零开销 |
| `static FOO: Mutex<RefCell<T>>` | 非 `Sync` 的复合类型 | 中断与主循环共享 |
| `static FOO: UnsafeCell<T>` | 需要裸指针映射 | 需手动保证无竞争 |
| `static mut FOO: T` | 不推荐 | 需要 `unsafe`，2024 Edition 已限制 |

```rust,compile_fail
#![no_std]

static mut COUNTER: u32 = 0;

fn increment() {
    // ❌ Rust 2024 编译错误：use of mutable static is unsafe
    COUNTER += 1;
}
```

```rust,ignore
#![no_std]

use core::sync::atomic::{AtomicU32, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(0);

fn increment() {
    COUNTER.fetch_add(1, Ordering::Relaxed);
}
```

---

## 八、`build-std` 与自定义 target JSON

`build-std` 让 Cargo 为没有预编译 std/core 的目标重新编译核心库。

```toml
# .cargo/config.toml
[unstable]
build-std = ["core", "alloc", "compiler_builtins"]
build-std-features = ["compiler-builtins-mem"]

[build]
target = "thumbv7em-none-eabihf"
```

当官方 target 不满足需求（如自定义 FPU、特殊内存布局、新芯片）时，可编写 target JSON：

```json
{
  "llvm-target": "thumbv7em-none-eabihf",
  "target-endian": "little",
  "target-pointer-width": "32",
  "arch": "arm",
  "cpu": "cortex-m4",
  "features": "+vfp4,-d32",
  "os": "none",
  "vendor": "unknown",
  "linker": "rust-lld",
  "linker-flavor": "ld.lld",
  "pre-link-args": ["-Tlink.x"],
  "panic-strategy": "abort",
  "relocation-model": "static",
  "singlethread": true,
  "max-atomic-width": 32
}
```

> **来源**: [The Embedonomicon — Build a `no_std` program](https://docs.rust-embedded.org/embedonomicon/) · [Rust Target Tier Policy](https://doc.rust-lang.org/rustc/target-tier-policy.html)

---

## 九、链接脚本核心约定

裸机项目通常把链接脚本命名为 `memory.x`（内存布局）和 `link.x`（section 规则），并在 crate 中通过 `cortex-m-rt` 自动包含，或在 `.cargo/config.toml` 中通过 `rustflags = ["-C", "link-arg=-Tlink.x"]` 指定。

```ld
/* memory.x — STM32F407 示例 */
MEMORY
{
  FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 1024K
  RAM   (rwx): ORIGIN = 0x20000000, LENGTH = 128K
}

/* link.x 片段 */
SECTIONS
{
  .text : {
    KEEP(*(.vector_table));
    *(.text .text.*);
    *(.rodata .rodata.*);
    _etext = .;
  } > FLASH

  .data : AT(_etext) {
    _sdata = .;
    *(.data .data.*);
    _edata = .;
  } > RAM

  .bss : {
    _sbss = .;
    *(.bss .bss.*);
    *(COMMON);
    _ebss = .;
  } > RAM

  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
```

判定依据：链接脚本必须与芯片参考手册中的内存映射一致；`_sdata`/`_edata`/`_sbss`/`_ebss`/`_sidata`/`_stack_top` 等符号是启动代码与脚本之间的接口。

---

## 十、Embassy 裸机执行器

[Embassy](https://embassy.dev/) 提供 `no_std`/`no_alloc` 的 async 执行器，任务以 Future 状态机运行，中断即 waker。

```rust,ignore
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::Timer;
use embassy_rp::gpio::{Level, Output};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_rp::init(Default::default());
    let mut led = Output::new(p.PIN_25, Level::Low);

    loop {
        led.set_high();
        Timer::after_secs(1).await;
        led.set_low();
        Timer::after_secs(1).await;
    }
}
```

```toml
[dependencies]
embassy-executor = { version = "0.5", features = ["task-arena-size-98304"] }
embassy-time = "0.5"
embassy-rp = { version = "0.5", features = ["defmt", "time-driver"] }
cortex-m-rt = "0.7"
```

**关键概念**：

| 概念 | 说明 |
|:---|:---|
| `task-arena-size-*` | 静态任务池大小，必须在编译期确定 |
| time driver | 硬件定时器驱动 `Timer::after_*`，执行器依赖它 |
| `WFI`/`WFE` | 无任务时进入低功耗等待 |
| `Spawner` | 用于在 `main` 中派生其它任务 |

判定依据：Embassy 适合 I/O 密集、协议栈复杂的裸机设备；硬实时控制应评估 RTIC 或手写中断。

---

## 十一、常见 no_std 反模式

| 反模式 | 问题 | 惯用修正 |
|:---|:---|:---|
| 在 `#![no_std]` 中直接使用 `std::` | 编译错误 | 使用 `core::` 或引入 `alloc` |
| `static mut` 直接修改 | 数据竞争 / 2024 Edition 硬错误 | `AtomicXxx` 或 `Mutex<RefCell<T>>` |
| 在裸机中使用 `println!` | 无标准输出 | `defmt`、`rtt-target`、UART HAL |
| 栈上数组交给 DMA | 返回后 DMA 写已释放内存 | `'static` 缓冲区或 DMA 安全包装 |
| 临界区内执行耗时/阻塞操作 | 中断延迟恶化 | 缩短临界区，只保护最小状态更新 |
| 未初始化堆就使用 `Box`/`Vec` | 未定义行为 | 先 `HEAP.init(...)` |
| 单核裸机使用自旋锁 | ISR 重入导致死锁 | `critical_section::with` |
| 忽略 HAL 方法返回的 `Result` | 静默错误 | 显式 `unwrap`/`?` 或错误处理 |
| 混合不同 `Ordering` 而不验证 | 内存顺序错误 | 按 happens-before 关系选择 |
| 未开启 `compiler-builtins-mem` | 链接错误 `memcpy` 未定义 | 配置 `build-std-features` |

---

## 十二、反例与失效模式

| 失效模式 | 根因 | 修复方向 |
|:---|:---|:---|
| 链接错误 `undefined reference to rust_eh_personality` | 使用了 `panic = "unwind"` 但无 unwinding 支持 | 改用 `panic = "abort"` |
| 链接错误 `undefined reference to memcpy` | 缺少 `compiler-builtins-mem` | 配置 `build-std-features` |
| 上电 HardFault | 栈顶错误 / 向量表未对齐 / `.data`/`.bss` 未初始化 | 检查链接脚本与启动代码 |
| 全局变量值随机 | `.bss` 未清零 | 启动代码清零整个 `.bss` |
| 中断中访问共享数据崩溃 | 未使用临界区或原子类型 | `critical_section::with` / `AtomicXxx` |
| DMA 数据错误 | 缓冲区在不可见 RAM 或 cache 未清洗 | 放到 DMA 可访问区并维护 cache 一致性 |
| async 任务不运行 | Embassy time driver 未使能或 arena 太小 | 检查 features 与 task-arena-size |
| `Box::new` 死机 | 堆未初始化 | `HEAP.init(...)` |

---

## 十三、边界测试

### 13.1 边界测试：`no_std` 中误用 `std`

```rust,compile_fail
#![no_std]

fn main() {
    // ❌ 编译错误：no_std 中 std 不可用
    let _v = std::vec::Vec::new();
}
```

> **修正**：使用 `heapless::Vec` 或配置全局分配器后使用 `alloc::vec::Vec`。

### 13.2 边界测试：缺少 `panic_handler`

```rust,compile_fail
#![no_std]

fn main() {
    panic!("boom");
}
```

> **修正**：提供 `#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }`。

### 13.3 边界测试：直接访问 `static mut`

```rust,compile_fail
#![no_std]

static mut COUNTER: u32 = 0;

fn increment() {
    COUNTER += 1; // ❌ 编译错误
}
```

> **修正**：改为 `static COUNTER: core::sync::atomic::AtomicU32 = ...`。

### 13.4 边界测试：`Vec` 在未初始化堆上使用

```rust,ignore
#![no_std]
extern crate alloc;
use alloc::vec::Vec;
use embedded_alloc::TlsfHeap;

#[global_allocator]
static HEAP: TlsfHeap = TlsfHeap::empty();

fn main() {
    // ❌ 错误：HEAP 尚未 init
    let mut v = Vec::new();
    v.push(1);
}
```

> **修正**：在 `main` 开头调用 `HEAP.init(...)`。

---

## 十四、决策树：裸机技术栈选择

```mermaid
graph TD
    A[开始裸机项目] --> B{是否需要操作系统服务?}
    B -->|是| C[考虑 Tock / Hubris / FreeRTOS 绑定]
    B -->|否| D{是否需要硬实时抢占调度?}
    D -->|是| E[RTIC 框架]
    D -->|否| F{是否需要复杂协议栈/网络?}
    F -->|是| G[Embassy + embedded-hal-async]
    F -->|否| H{是否使用标准 ARM/RISC-V target?}
    H -->|是| I[cortex-m-rt / riscv-rt + 手写中断]
    H -->|否| J[自定义 target JSON + 手写 _start]
```

---

## 十五、相关概念

- [Rust 嵌入式系统开发](03_embedded_systems.md)
- [裸机启动与链接脚本](13_bare_metal_boot_linker_script.md)
- [panic_handler 与 no_std 运行时](18_panic_runtime_no_std.md)
- [嵌入式内存分配器](16_embedded_memory_allocators.md)
- [no_std 同步原语](15_no_std_synchronization_primitives.md)
- [PAC 与 HAL 实现](17_pac_hal_implementation.md)
- [embedded-hal 与驱动惯用法](24_embedded_hal_and_driver_idioms.md)
- [异步 no_std 嵌入式](11_async_no_std_embedded.md)
- [交叉编译](02_cross_compilation.md)
- [安全关键裸机 OS 与 Rust](19_safety_critical_bare_metal_os.md)

---

## 十六、权威来源索引

- **[The Embedded Rust Book](https://docs.rust-embedded.org/book/)** — Rust Embedded Working Group 官方指南，覆盖 `no_std`、内存映射外设、静态保证、设计模式与移植性。
  - 重点章节：[Introduction](https://docs.rust-embedded.org/book/intro/index.html)、[Peripherals](https://docs.rust-embedded.org/book/peripherals/index.html)、[Static Guarantees](https://docs.rust-embedded.org/book/static-guarantees/index.html)、[Design Patterns](https://docs.rust-embedded.org/book/design-patterns/index.html)。

- **[The Embedonomicon](https://docs.rust-embedded.org/embedonomicon/)** — 裸机底层实现权威，覆盖自定义 target、链接脚本、启动序列与自定义运行时 crate。

- **[Embassy Book](https://embassy.dev/book/)** — Embassy 异步框架官方文档，覆盖 `no_std` async executor、HAL、time driver、网络栈与最佳实践。

- **[Ferrous Systems](https://ferrous-systems.com/)** — Rust 嵌入式培训与咨询，提供 Ferrocene 安全关键工具链、认证路径与生产化经验。

- **[Knurling](https://knurling.ferrous-systems.com/)** — Ferrous Systems 的嵌入式 Rust 项目集，包括 `defmt`、probe-rs 工作流前身、`embedded-test` 模板与硬件开发板支持。

- **[cortex-m-rt](https://docs.rs/cortex-m-rt/)** / **[riscv-rt](https://docs.rs/riscv-rt/)** — ARM Cortex-M 与 RISC-V 的官方运行时入口 crate。

- **[critical-section crate](https://docs.rs/critical-section/)** — 跨平台临界区抽象的事实标准。

- **[Rust Reference — no_std](https://doc.rust-lang.org/reference/names/preludes.html#the-no_std-attribute)** — `#![no_std]` 属性的语言级规范。

- **[probe.rs 文档](https://probe.rs/docs/)** — 基于 CMSIS-DAP / J-Link / ST-Link 的 Rust 嵌入式调试与烧录工作流。

- **[defmt Book](https://defmt.ferrous-systems.com/)** — Ferrous Systems 开发的零开销日志框架，替代 `println!` 的裸机调试方案。

- **[Knurling-rs](https://knurling.ferrous-systems.com/)** — Ferrous Systems 的嵌入式 Rust 项目集，包括 `defmt`、`embedded-test`、probe-rs 工作流模板与硬件支持包。

- **[Ferrous Systems Training — Embedded Rust](https://ferrous-systems.com/training/)** — 面向生产级嵌入式 Rust 的培训与认证路径，覆盖 `no_std`、Embassy、RTIC、安全关键实践。

> **权威来源对齐变更日志**: 2026-07-31 创建；2026-07-31 Wave H 补充 probe-rs、defmt、Knurling、Ferrous Systems 国际来源。

**文档版本**: 1.1
**最后更新**: 2026-07-31
**状态**: ✅ 概念文件创建完成

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((no_std 与裸机惯用法))
    crate 设置
      #![no_std]
      #![no_main]
      panic_handler
      global_allocator
    启动入口
      cortex-m-rt entry
      riscv-rt entry
      自定义 _start
    同步与顺序
      critical-section
      compiler_fence
      fence
      AcquireRelease
    静态安全
      static_mut_refs 禁用
      Mutex<RefCell<T>>
      AtomicXxx
    构建与目标
      build-std
      target JSON
      linker script
    运行时选择
      cortex-m-rt
      riscv-rt
      Embassy executor
    反模式
      static mut
      栈上 DMA 缓冲区
      临界区内阻塞
```

> **认知功能**: 本 mindmap 从 crate 设置、启动入口、同步与顺序、静态安全、构建目标、运行时选择与反模式七个维度组织内容，可作为裸机 Rust 项目选型的快速导航索引。
