//! 自定义 bump allocator 示例（host 可编译）
//!
//! 演示如何实现 `GlobalAlloc` 并在 `#![no_std]` 环境中使用。
//! host 目标下不注册为全局分配器（避免与 std 冲突），而是直接调用实例方法；
//! ARM 目标下可通过 `#[global_allocator]` 注册。
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/16_embedded_memory_allocators.md`
//! `concept/06_ecosystem/05_systems_and_embedded/29_embedded_memory_layout_and_heap_safety.md`

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(not(target_arch = "arm"))]
extern crate std;

use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::ptr;

// ---------------------------------------------------------------------------
// Bump allocator：只分配、不释放，适合阶段化批处理
// ---------------------------------------------------------------------------

pub struct BumpPointerAlloc {
    head: UnsafeCell<usize>,
    end: UnsafeCell<usize>,
}

unsafe impl Sync for BumpPointerAlloc {}

impl BumpPointerAlloc {
    pub const fn empty() -> Self {
        Self {
            head: UnsafeCell::new(0),
            end: UnsafeCell::new(0),
        }
    }

    pub unsafe fn init(&self, start: *mut u8, size: usize) {
        unsafe {
            *self.head.get() = start as usize;
            *self.end.get() = start as usize + size;
        }
    }

    /// host 演示用：不依赖中断临界区
    #[cfg(not(target_arch = "arm"))]
    fn with_critical_section<R>(&self, f: impl FnOnce() -> R) -> R {
        f()
    }

    /// ARM 目标下通过关中断实现临界区
    #[cfg(target_arch = "arm")]
    fn with_critical_section<R>(&self, f: impl FnOnce() -> R) -> R {
        cortex_m::interrupt::free(|_| f())
    }
}

unsafe impl GlobalAlloc for BumpPointerAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe {
            self.with_critical_section(|| {
                let head = self.head.get();
                let align = layout.align();
                let size = layout.size();
                let start = ((*head + align - 1) / align) * align;
                if start + size > *self.end.get() {
                    ptr::null_mut()
                } else {
                    *head = start + size;
                    start as *mut u8
                }
            })
        }
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // bump allocator 不释放单块内存
    }
}

// ---------------------------------------------------------------------------
// 入口：host 演示分配过程；ARM 目标下注册为全局分配器
// ---------------------------------------------------------------------------

#[cfg(target_arch = "arm")]
#[global_allocator]
static HEAP: BumpPointerAlloc = BumpPointerAlloc::empty();

#[cfg(target_arch = "arm")]
#[cortex_m_rt::entry]
fn main() -> ! {
    static mut POOL: [u8; 1024] = [0; 1024];
    unsafe {
        HEAP.init(POOL.as_mut_ptr(), POOL.len());
    }
    // 应用代码...
    loop {}
}

#[cfg(target_arch = "arm")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[cfg(not(target_arch = "arm"))]
fn main() {
    let mut pool = [0u8; 1024];
    let alloc = BumpPointerAlloc::empty();
    unsafe {
        alloc.init(pool.as_mut_ptr(), pool.len());

        let layout = Layout::new::<u64>();
        let ptr = alloc.alloc(layout);
        assert!(!ptr.is_null(), "allocation should succeed");
        (ptr as *mut u64).write(0xDEAD_BEEF_CAFE_BABE);
        assert_eq!((ptr as *mut u64).read(), 0xDEAD_BEEF_CAFE_BABE);
    }
    std::println!("bump allocator demo passed");
}
