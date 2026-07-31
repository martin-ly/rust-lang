//! 自定义裸机异步执行器示例（host 可编译）
//!
//! 演示如何在 `#![no_std]` 环境中用 `Future`、`RawWaker`、`Waker` 构建最小 executor。
//! 在 host 目标下用模拟的“硬件计数器”触发唤醒；在 ARM 目标下可替换为真实定时器 ISR。
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/28_custom_bare_metal_async_executor.md`

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(not(target_arch = "arm"))]
extern crate std;

use core::cell::Cell;
use core::future::Future;
use core::pin::Pin;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

// ---------------------------------------------------------------------------
// Waker 实现：单核裸机中用一个全局原子标志表示“有待处理唤醒”
// ---------------------------------------------------------------------------

static WAKE_FLAG: AtomicBool = AtomicBool::new(false);

unsafe fn clone(_: *const ()) -> RawWaker {
    RawWaker::new(core::ptr::null(), &VTABLE)
}

unsafe fn wake(_: *const ()) {
    WAKE_FLAG.store(true, Ordering::Release);
}

unsafe fn wake_by_ref(_: *const ()) {
    WAKE_FLAG.store(true, Ordering::Release);
}

unsafe fn drop(_: *const ()) {}

static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);

fn make_waker() -> Waker {
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

// ---------------------------------------------------------------------------
// SyncCell：host 下让 `Cell` 静态变量满足 `Sync` 以通过编译；
// ARM no_std 裸机中单线程使用同样安全。
// ---------------------------------------------------------------------------

pub struct SyncCell<T: ?Sized>(T);

unsafe impl<T: ?Sized> Sync for SyncCell<T> {}

// ---------------------------------------------------------------------------
// 静态任务槽与执行器
// ---------------------------------------------------------------------------

pub struct Executor<'a> {
    tasks: &'a [&'a SyncCell<Cell<Option<Pin<&'static mut dyn Future<Output = ()>>>>>],
}

impl<'a> Executor<'a> {
    pub fn new(tasks: &'a [&'a SyncCell<Cell<Option<Pin<&'static mut dyn Future<Output = ()>>>>>]) -> Self {
        Self { tasks }
    }

    pub fn run_once(&self) -> bool {
        let waker = make_waker();
        let mut cx = Context::from_waker(&waker);
        let mut active = false;

        for slot in self.tasks {
            if let Some(mut future) = slot.0.take() {
                match future.as_mut().poll(&mut cx) {
                    Poll::Pending => {
                        slot.0.set(Some(future));
                        active = true;
                    }
                    Poll::Ready(()) => {}
                }
            }
        }

        active || WAKE_FLAG.swap(false, Ordering::Acquire)
    }

    #[cfg(not(target_arch = "arm"))]
    pub fn run(&self) {
        while self.run_once() {
            // host 模拟：推进模拟硬件时间
            advance_hardware_clock();
            core::hint::spin_loop();
        }
    }

    #[cfg(target_arch = "arm")]
    pub fn run(&self) -> ! {
        loop {
            self.run_once();
            cortex_m::asm::wfi();
        }
    }
}

// ---------------------------------------------------------------------------
// 模拟硬件：host 用一个静态原子计数器代替真实定时器
// ---------------------------------------------------------------------------

static HARDWARE_CLOCK: AtomicBool = AtomicBool::new(false);
static COUNTER: AtomicU32 = AtomicU32::new(0);

#[cfg(not(target_arch = "arm"))]
fn advance_hardware_clock() {
    HARDWARE_CLOCK.store(true, Ordering::Relaxed);
}

struct TimerFuture {
    expires_at: u32,
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let now = current_time();
        if now >= self.expires_at {
            Poll::Ready(())
        } else {
            // 注册 waker；真实硬件会把 cx.waker() 存入定时器槽
            let _ = cx.waker().clone();
            Poll::Pending
        }
    }
}

#[cfg(not(target_arch = "arm"))]
fn current_time() -> u32 {
    if HARDWARE_CLOCK.swap(false, Ordering::Relaxed) {
        COUNTER.fetch_add(1, Ordering::Relaxed);
    }
    COUNTER.load(Ordering::Relaxed)
}

#[cfg(target_arch = "arm")]
fn current_time() -> u32 {
    // 真实项目应读取 SysTick 或定时器寄存器
    0
}

// ---------------------------------------------------------------------------
// 入口
// ---------------------------------------------------------------------------

static mut FUT1: TimerFuture = TimerFuture { expires_at: 3 };
static TASK1: SyncCell<Cell<Option<Pin<&'static mut dyn Future<Output = ()>>>>> =
    SyncCell(Cell::new(None));

#[cfg(not(target_arch = "arm"))]
fn main() {
    let raw = &raw mut FUT1;
    let fut1: Pin<&'static mut TimerFuture> = unsafe { Pin::new_unchecked(&mut *raw) };
    TASK1.0.set(Some(fut1));

    let tasks: &[&SyncCell<Cell<Option<Pin<&'static mut dyn Future<Output = ()>>>>>] = &[&TASK1];
    let executor = Executor::new(tasks);
    executor.run();

    std::println!("custom async executor demo finished");
}

#[cfg(target_arch = "arm")]
#[cortex_m_rt::entry]
fn main() -> ! {
    let raw = &raw mut FUT1;
    let fut1: Pin<&'static mut TimerFuture> = unsafe { Pin::new_unchecked(&mut *raw) };
    TASK1.0.set(Some(fut1));

    let tasks: &[&SyncCell<Cell<Option<Pin<&'static mut dyn Future<Output = ()>>>>>] = &[&TASK1];
    let executor = Executor::new(tasks);
    executor.run()
}

#[cfg(target_arch = "arm")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
