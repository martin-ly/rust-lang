//! Bare-metal 基础概念
//! 演示 `#![no_std]`、`#![no_main]`、panic handler 和启动代码概念。
//! #![no_main]
//! ```
//!

/// 自定义 panic handler 概念说明
/// definition panic handler concept explain
/// 自definition panic handler conceptexplain
/// 在 `#![no_std]` 环境中，必须提供一个 `#[panic_handler]`：
/// in `#![no_std]` environment in ，must `#[panic_handler]`：
/// use core::panic::PanicInfo;
///
/// #[panic_handler]
/// fn panic(_info: &PanicInfo) -> ! {
///     // 真实硬件上：闪烁 LED、写入调试串口、触发看门狗复位
///     // real hardware on ： LED、、
/// ```
///
/// `-> !` 表示发散函数（永不返回）。
/// `->!` represent function （）。
/// 常用 panic handler crate：
/// - `panic-halt`: 进入无限循环
/// - `panic-halt`: circulation
/// - `panic-halt`: 进入无限circulation
/// - `panic-itm`: 通过 ITM 输出调试信息（仅 Cortex-M）
/// - `panic-itm`: ITM （ Cortex-M）
/// - `panic-semihosting`: 通过 semihosting 输出到调试器
pub struct PanicHandlerConcept;

impl PanicHandlerConcept {
    pub fn description() -> &'static str {
        "panic handler 是 no_std 环境的必需组件，负责在 panic 时执行系统级处理"
    }
}

/// 启动代码 (Startup Code) 概念
/// (Startup Code) concept
/// 裸机程序没有操作系统加载器，CPU 复位后直接从复位向量开始执行。
/// program operating system ，CPU after from 。
/// 启动代码负责：
/// ：
/// 1. **初始化栈指针 (SP)**：从向量表第一个字加载
/// 1. **stack pointer (SP)**：from first
/// 3. **清零 .bss 段**：将未初始化的全局变量置零
/// 3. **.bss **：will global variable
/// 4. **调用 `main()` 或 `#[entry]` 函数**
/// 4. ** `main()` or `#[entry]` function **
/// 在 Cortex-M 上，`cortex-m-rt` crate 自动处理这些步骤：
/// use cortex_m_rt::entry;
///
/// #[entry]
/// fn main() -> ! {
///     // 用户代码
///     //
/// ```
pub struct StartupCode;

impl StartupCode {
    /// 返回启动序列描述
    /// sequence describe
    pub fn startup_sequence() -> &'static str {
        "复位 -> 初始化 SP -> 复制 .data -> 清零 .bss -> 调用 main"
    }
}

/// 全局分配器概念（可选）
/// global concept （）
/// 如果需要使用 `alloc` crate（`Vec`、`Box` 等），必须提供全局分配器：
/// if `alloc` crate（`Vec`、`Box` etc. ），must global ：
/// use core::alloc::GlobalAlloc;
///
/// struct DummyAllocator;
///
/// unsafe impl GlobalAlloc for DummyAllocator {
///     unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
///         core::ptr::null_mut()
///     }
///     unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {}
/// }
///
/// #[global_allocator]
/// static ALLOCATOR: DummyAllocator = DummyAllocator;
/// ```
///
/// 实际项目中常用 `embedded-alloc` 或自定义 slab allocator。
pub struct GlobalAllocatorConcept;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_panic_handler_description() {
        assert!(!PanicHandlerConcept::description().is_empty());
    }

    #[test]
    fn test_startup_sequence() {
        assert!(StartupCode::startup_sequence().contains("复位"));
    }
}
