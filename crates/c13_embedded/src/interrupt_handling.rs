//! 中断处理
//!
//! 中断是嵌入式系统的核心机制，允许外设在事件发生时异步通知 CPU。
//!
//! ## Cortex-M 中断基础
//!
//! - **NVIC (Nested Vectored Interrupt Controller)**: 管理中断使能、优先级和挂起
//! - **中断向量表**: 存储每个中断服务例程 (ISR) 的入口地址
//! - **抢占优先级** vs **子优先级**: 决定中断嵌套行为

/// NVIC 配置概念（ARM 目标下使用 `cortex-m` crate）
///
/// ```rust,ignore
/// use cortex_m::peripheral::NVIC;
/// use cortex_m::peripheral::nvic::NvicIdx;
///
/// // 启用 UART0 中断
/// unsafe { NVIC::unmask(NvicIdx::UART0) };
///
/// // 设置优先级（数值越小优先级越高）
/// NVIC::set_priority(NvicIdx::UART0, 1);
/// ```
pub struct NvicConcept;

impl NvicConcept {
    /// 返回 NVIC 配置步骤
    pub fn setup_steps() -> &'static [&'static str] {
        &[
            "1. 在 NVIC 中设置中断优先级",
            "2. 清除中断挂起位",
            "3. 在 NVIC 中使能中断 (unmask)",
            "4. 在外设中使能对应中断源",
        ]
    }
}

/// 临界区概念
///
/// 临界区用于保护共享资源，防止中断在中间打断导致数据竞争。
///
/// 在 Cortex-M 上，`cortex_m::interrupt::free` 会关闭中断执行闭包：
///
/// ```rust,ignore
/// use cortex_m::interrupt;
///
/// static mut COUNTER: u32 = 0;
///
/// interrupt::free(|_cs| {
///     // 此处中断被全局禁用
///     unsafe { COUNTER += 1; }
/// });
/// ```
///
/// **注意**：临界区应尽可能短，以减少中断延迟。
pub struct CriticalSectionConcept;

impl CriticalSectionConcept {
    /// 描述临界区最佳实践
    pub fn best_practices() -> &'static str {
        "临界区应尽可能短，只包含必要的共享资源访问，避免在临界区内调用复杂逻辑"
    }
}

/// 中断服务例程 (ISR) 模板
///
/// 使用 `cortex-m-rt` 的 `#[interrupt]` 宏：
///
/// ```rust,ignore
/// use cortex_m_rt::interrupt;
///
/// #[interrupt]
/// fn TIM2() {
///     // 清除中断标志（必须！否则中断会重复触发）
///     unsafe {
///         let tim2 = &*stm32f1::pac::TIM2::ptr();
///         tim2.sr.modify(|_, w| w.uif().clear_bit());
///     }
/// }
/// ```
///
/// ISR 设计原则：
/// 1. **快速执行**：ISR 应尽快返回，复杂处理放到主循环
/// 2. **清除标志**：必须在 ISR 中清除中断标志
/// 3. **避免阻塞**：ISR 中不能使用阻塞操作
/// 4. **使用静态可变变量**：与主循环共享数据
pub struct IsrTemplate;

/// 中断安全的共享状态模式
///
/// 使用 `core::cell::Cell`（对于 `Copy` 类型）或自定义原子操作。
///
/// ```rust,ignore
/// use core::cell::Cell;
///
/// static FLAG: Cell<bool> = Cell::new(false);
///
/// #[interrupt]
/// fn EXTI0() {
///     FLAG.set(true);
/// }
///
/// fn main() {
///     loop {
///         if FLAG.get() {
///             FLAG.set(false);
///             // 处理事件
///         }
///     }
/// }
/// ```
pub struct SharedStatePattern;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nvic_steps() {
        assert_eq!(NvicConcept::setup_steps().len(), 4);
    }

    #[test]
    fn test_critical_section_practices() {
        assert!(CriticalSectionConcept::best_practices().contains("临界区"));
    }
}
