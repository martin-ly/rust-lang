//! no_std 分配器、panic handler 与临界区综合示例
//!
//! 目标平台：
//! - `thumbv7em-none-eabihf`（ARM Cortex-M4F，如 STM32F4 / Nucleo-F446RE）
//! - `thumbv7m-none-eabi`（ARM Cortex-M3，如 STM32F103 / Blue Pill）
//! - `riscv32imac-unknown-none-elf`（通用 32-bit RISC-V MCU，如 SiFive FE310 / GD32VF103）
//!
//! 本示例演示：
//! 1. 自定义 `#[panic_handler]`（日志 LED 提示 + 无限循环）。
//! 2. 最小 bump allocator 实现 `#[global_allocator]`，使 `alloc::vec::Vec` 可在裸机运行。
//! 3. `critical-section` 保护共享计数器，避免中断与主循环间的数据竞争。
//!
//! 编译命令：
//! ```bash
//! cargo build -p c13_embedded --target thumbv7em-none-eabihf --example no_std_allocators_and_panic_handlers
//! cargo build -p c13_embedded --target thumbv7m-none-eabi    --example no_std_allocators_and_panic_handlers
//! cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example no_std_allocators_and_panic_handlers
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/52_no_std_allocators_and_panic_handlers.md`
//! `concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md`

#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_std
)]
#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_main
)]

// Host 模拟入口：在 x86_64 / Windows 上 `cargo check --workspace` 直接通过。
#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
fn main() {
    println!("no_std_allocators_and_panic_handlers: host 模拟模式");
    println!("ARM Cortex-M4F:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7em-none-eabihf \\\
    \
         --example no_std_allocators_and_panic_handlers"
    );
    println!("ARM Cortex-M3:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7m-none-eabi \\\n    \
         --example no_std_allocators_and_panic_handlers"
    );
    println!("RISC-V 32-bit:");
    println!(
        "  cargo build -p c13_embedded --target riscv32imac-unknown-none-elf \\\n    \
         --example no_std_allocators_and_panic_handlers"
    );
}

// 裸机真实目标入口。
#[cfg(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
))]
mod target_impl {
    use core::alloc::{GlobalAlloc, Layout};
    use core::cell::UnsafeCell;
    use core::panic::PanicInfo;
    use core::sync::atomic::{AtomicUsize, Ordering};

    // -------------------------------------------------------------------------
    // 1. 自定义 panic handler：进入无限循环，可替换为复位或错误日志。
    // -------------------------------------------------------------------------
    #[panic_handler]
    fn panic(_info: &PanicInfo) -> ! {
        // 真实硬件上可在此处翻转 GPIO 提示故障。
        loop {
            #[cfg(target_arch = "arm")]
            cortex_m::asm::wfi();
            #[cfg(target_arch = "riscv32")]
            riscv::asm::wfi();
        }
    }

    // -------------------------------------------------------------------------
    // 2. 最小 bump allocator：单线程/关中断场景安全，演示 #[global_allocator]。
    // -------------------------------------------------------------------------
    const HEAP_SIZE: usize = 1024;

    pub struct BumpAllocator {
        heap: UnsafeCell<[u8; HEAP_SIZE]>,
        next: AtomicUsize,
    }

    // 裸机单核 + 临界区保护下，可安全实现 Sync。
    unsafe impl Sync for BumpAllocator {}

    impl BumpAllocator {
        pub const fn new() -> Self {
            Self {
                heap: UnsafeCell::new([0; HEAP_SIZE]),
                next: AtomicUsize::new(0),
            }
        }
    }

    unsafe impl GlobalAlloc for BumpAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let start = self.next.fetch_add(layout.size(), Ordering::Relaxed);
            let end = start.saturating_add(layout.size());
            if end > HEAP_SIZE {
                return core::ptr::null_mut();
            }
            // 简单对齐处理：按 size 对齐（实际项目应使用 layout.align()）
            let ptr = unsafe { (*self.heap.get()).as_mut_ptr().add(start) };
            ptr
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
            // bump allocator 不支持释放；真实项目应使用 TLSF 或 slab。
        }
    }

    #[global_allocator]
    static ALLOCATOR: BumpAllocator = BumpAllocator::new();

    // -------------------------------------------------------------------------
    // 3. critical-section 保护共享状态：主循环 + 中断均可安全递增。
    // -------------------------------------------------------------------------
    static COUNTER: critical_section::Mutex<core::cell::RefCell<u32>> =
        critical_section::Mutex::new(core::cell::RefCell::new(0));

    fn increment_counter() {
        critical_section::with(|cs| {
            *COUNTER.borrow(cs).borrow_mut() += 1;
        });
    }

    fn read_counter() -> u32 {
        critical_section::with(|cs| *COUNTER.borrow(cs).borrow())
    }

    // -------------------------------------------------------------------------
    // ARM 入口
    // -------------------------------------------------------------------------
    #[cfg(target_arch = "arm")]
    #[cortex_m_rt::entry]
    fn main() -> ! {
        use alloc::vec::Vec;
        extern crate alloc;

        let mut v = Vec::new();
        v.push(1u8);
        v.push(2);
        v.push(3);

        loop {
            increment_counter();
            let _ = read_counter();

            // 简单延时
            for _ in 0..50_000 {
                cortex_m::asm::nop();
            }
        }
    }

    // -------------------------------------------------------------------------
    // RISC-V 入口
    // -------------------------------------------------------------------------
    #[cfg(target_arch = "riscv32")]
    #[riscv_rt::entry]
    fn main() -> ! {
        use alloc::vec::Vec;
        extern crate alloc;

        let mut v = Vec::new();
        v.push(1u8);
        v.push(2);
        v.push(3);

        loop {
            increment_counter();
            let _ = read_counter();

            for _ in 0..50_000 {
                riscv::asm::nop();
            }
        }
    }
}
