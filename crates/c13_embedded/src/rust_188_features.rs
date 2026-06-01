//! Rust 188.0 新特性实现模块 —— c13_embedded
//! Rust 188.0 feature module —— c13_embedded
//! - `naked_functions`: 裸函数 `#[naked]` 稳定
//! - `naked_functions`: 裸function `#[naked]` 稳定
//! # 版本信息
//! # this
//! - Rust 版本: 188.0
//! - Rust this : 188.0
//! - Rust 版this: 188.0
//! - 稳定日期: 2025-06-26
//! - date : 2025-06-26
//! - 稳定date: 2025-06-26
//! - date: 2025-06-26

// ============================================================================
// 1. 裸函数 `#[naked]` 稳定
// ============================================================================

/// # 裸函数（Naked Functions）
/// # 裸function（Naked Functions）
/// 直接暴露原始汇编入口。
/// expose 。
/// ## 使用场景
/// ## scenario
/// - 操作系统中断处理程序（ISR）
/// - operating system in program （ISR）
/// - 引导加载程序入口点
/// - program point
/// - 与汇编代码直接交互的回调
/// - and
/// ## 限制
/// ##
/// - 函数体必须是单条 `asm!` 宏调用
/// - function volume must `asm!`
/// - 编译器不为裸函数生成栈帧管理代码
/// - as function stack
/// - 调用者负责保存/恢复寄存器
/// - /
#[cfg(target_arch = "x86_64")]
#[unsafe(naked)]
pub extern "C" fn naked_syscall_handler() {
    core::arch::naked_asm!(
        "push rax",
        "push rcx",
        "push rdx",
        "call {handler}",
        "pop rdx",
        "pop rcx",
        "pop rax",
        "iretq",
        handler = sym syscall_dispatch,
    );
}

#[cfg(target_arch = "x86_64")]
extern "C" fn syscall_dispatch() {
    // 实际的系统调用分发逻辑
}

#[test]
#[cfg(target_arch = "x86_64")]
fn test_naked_function_exists() {
    // 裸函数本身难以在单元测试中直接调用，
    // 但可以通过函数指针确认其符号存在
    let _ptr: extern "C" fn() = naked_syscall_handler;
}
