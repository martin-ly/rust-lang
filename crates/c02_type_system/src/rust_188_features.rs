//! Rust 188.0 新特性实现模块 —— c02_type_system
//!
//! 本模块展示了 Rust 188.0 (2025-06-26) 的关键语言特性和工具链改进。
//!
//! - `let_chains`: Let Chains 在 2024 Edition 中稳定
//! - `naked_functions`: 裸函数 `#[naked]` 稳定
//!
//! # 版本信息
//! - Rust 版本: 188.0
//! - 稳定日期: 2025-06-26
//! - Edition: 2024

// ============================================================================
// 1. Let Chains 在 2024 Edition 中稳定
// ============================================================================

/// # Let Chains 稳定化
///
/// Rust 1.88.0 在 2024 Edition 中稳定了 let chains，
/// 允许在 `if` 和 `while` 条件中将 `let` 模式与布尔表达式混合使用。
///
/// ## 语法
/// `if let Some(x) = opt && x > 0 { ... }`
///
/// ## 之前
/// 需要使用嵌套 `if let` 或 `match`。
///
/// ## 现在
/// 可以直接链式组合多个 let 条件和布尔条件。
///
/// ## 限制
/// - 仅在 Edition 2024 中可用
/// - 不支持 `||`（或）与 `let` 混合（因语义复杂）
pub fn process_option_chain(opt: Option<i32>) -> Option<i32> {
    if let Some(x) = opt
        && x > 0
        && x < 100
    {
        Some(x * 2)
    } else {
        None
    }
}

pub fn while_let_chain_example() -> usize {
    let mut count = 0;
    let mut iter = [Some(1), Some(2), None, Some(3)].into_iter();
    while let Some(x) = iter.next()
        && let Some(y) = x
        && y > 0
    {
        count += y as usize;
    }
    count
}

#[test]
fn test_let_chains() {
    assert_eq!(process_option_chain(Some(42)), Some(84));
    assert_eq!(process_option_chain(Some(-1)), None);
    assert_eq!(process_option_chain(None), None);
    assert_eq!(while_let_chain_example(), 3);
}

// ============================================================================
// 2. 裸函数 `#[naked]` 稳定
// ============================================================================

/// # 裸函数（Naked Functions）
///
/// Rust 1.88.0 稳定了 `#[naked]` 属性，允许函数不使用标准 prologue/epilogue，
/// 直接暴露原始汇编入口。
///
/// ## 使用场景
/// - 操作系统中断处理程序（ISR）
/// - 引导加载程序入口点
/// - 与汇编代码直接交互的回调
///
/// ## 限制
/// - 函数体必须是单条 `asm!` 宏调用
/// - 编译器不为裸函数生成栈帧管理代码
/// - 调用者负责保存/恢复寄存器
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
