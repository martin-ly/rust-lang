//! Bare-metal 基础概念
//!
//! 演示 `#![no_std]`、`#![no_main]`、panic handler 和启动代码概念。
//!
//! 在真实的 bare-metal 程序中，crate 根文件需要添加：
//! ```rust,ignore
//! #![no_std]
//! #![no_main]
//! ```
//!
//! `no_std` 表示不使用 Rust 标准库，只使用 `core`（以及可选的 `alloc`）。
//! `no_main` 表示不使用标准库的 `main` 入口，由启动代码或 `cortex-m-rt` 接管。

/// 自定义 panic handler 概念说明
///
/// 在 `#![no_std]` 环境中，必须提供一个 `#[panic_handler]`：
///
/// ```rust,ignore
/// use core::panic::PanicInfo;
///
/// #[panic_handler]
/// fn panic(_info: &PanicInfo) -> ! {
///     // 真实硬件上：闪烁 LED、写入调试串口、触发看门狗复位
///     loop {}
/// }
/// ```
///
/// `-> !` 表示发散函数（永不返回）。
/// 因为 panic 后系统无法恢复，通常进入无限循环或触发硬件复位。
///
/// 常用的 panic handler crate：
/// - `panic-halt`: 进入无限循环
/// - `panic-itm`: 通过 ITM 输出调试信息（仅 Cortex-M）
/// - `panic-semihosting`: 通过 semihosting 输出到调试器
pub struct PanicHandlerConcept;

impl PanicHandlerConcept {
    /// 描述 panic handler 的作用
    pub fn description() -> &'static str {
        "panic handler 是 no_std 环境的必需组件，负责在 panic 时执行系统级处理"
    }
}

/// 启动代码 (Startup Code) 概念
///
/// 裸机程序没有操作系统加载器，CPU 复位后直接从复位向量开始执行。
/// 启动代码负责：
///
/// 1. **初始化栈指针 (SP)**：从向量表第一个字加载
/// 2. **复制 .data 段**：将已初始化的全局变量从 Flash 复制到 RAM
/// 3. **清零 .bss 段**：将未初始化的全局变量置零
/// 4. **调用 `main()` 或 `#[entry]` 函数**
///
/// 在 Cortex-M 上，`cortex-m-rt` crate 自动处理这些步骤：
///
/// ```rust,ignore
/// use cortex_m_rt::entry;
///
/// #[entry]
/// fn main() -> ! {
///     // 用户代码
///     loop {}
/// }
/// ```
pub struct StartupCode;

impl StartupCode {
    /// 返回启动序列描述
    pub fn startup_sequence() -> &'static str {
        "复位 -> 初始化 SP -> 复制 .data -> 清零 .bss -> 调用 main"
    }
}

/// 全局分配器概念（可选）
///
/// 如果需要使用 `alloc` crate（`Vec`、`Box` 等），必须提供全局分配器：
///
/// ```rust,ignore
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
