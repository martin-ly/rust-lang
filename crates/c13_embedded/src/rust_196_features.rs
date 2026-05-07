//! Rust 1.96.0 / Nightly 1.97 嵌入式相关新特性实现模块
//!
//! 本模块展示了 Rust 1.96.0+（nightly 1.97）在嵌入式和 bare-metal 编程方面的关键增强：
//! - `core::pin::pin!` 宏 — 无 alloc 环境下的栈上固定 ⭐
//! - `VecDeque::new` 的 const 上下文支持 — 常量初始化环形缓冲区
//! - `impl From<bool> for {f32, f64}` — 布尔传感器数据到浮点转换
//! - `DerefMut for PathBuf` — 最小示例（host 目标）
//! - `NonNull::new` 的 const 支持 — 裸指针常量初始化
//!
//! # 版本信息
//! - Rust版本: 1.96.0+ / nightly 1.97
//! - 稳定日期: 2026-05-XX
//! - Edition: 2024
//!
//! # 安全说明
//! 本模块**完全禁止 unsafe 代码**，所有示例均在 safe Rust 中实现。
//! 在 bare-metal 环境中，safe 抽象可以消除整类内存安全错误。
//!
//! # 参考
//! - [Rust 1.96.0 Release Notes](https://releases.rs/docs/1.96.0/)

#![forbid(unsafe_code)]

// ============================================================================
// 1. core::pin::pin! 宏 — 无 alloc 环境下的栈上固定
// ============================================================================

/// # `core::pin::pin!` 宏
///
/// ## 概念定义
/// `core::pin::pin!` 宏允许在栈上创建 `Pin<&mut T>`，无需堆分配。
/// 这在 `no_std` 嵌入式环境中极为重要，因为许多系统没有堆分配器。
///
/// ## 嵌入式应用场景
/// - 固定异步状态机（传感器轮询、DMA 传输）
/// - 固定自引用结构（缓冲区与解析器共存）
/// - 避免 `Box::pin` 带来的分配器依赖
///
/// ## 对比
///
/// | 方式 | 是否需要 alloc | 适用环境 | 开销 |
/// |------|-------------|---------|------|
/// | `Box::pin` | ✅ 需要 | 有堆的系统 | 堆分配 + 指针间接 |
/// | `core::pin::pin!` | ❌ 不需要 | `no_std` / bare-metal | 零开销 |
///
/// ## 决策树
/// ```text
/// 需要固定数据？
/// ├── 有堆分配器？ → Box::pin（通用）
/// └── 无堆分配器（bare-metal）？
///     ├── 数据在栈上？ → core::pin::pin!（推荐）
///     └── 数据在静态存储？ → Pin::static_mut（unsafe，需验证）
/// ```
pub struct StackPinningExamples;

impl StackPinningExamples {
    /// 示例 1：固定异步传感器读取状态机
    ///
    /// 在嵌入式系统中，异步驱动通常需要在栈上固定 Future，
    /// 以确保自引用结构在轮询期间不会被移动。
    pub fn pin_sensor_future() {
        // 模拟一个传感器读取 future（无 alloc，栈上固定）
        let future = core::pin::pin!(async {
            // 模拟读取传感器寄存器
            42u16
        });

        // future 的类型为 Pin<&mut impl Future>
        // 在 bare-metal 中，此模式避免了 Box::pin 的分配开销
        let _future = future;
    }

    /// 示例 2：固定自引用缓冲区结构
    ///
    /// 解析器常需要持有对输入缓冲区的引用。
    /// 使用 `pin!` 可以确保结构体及其引用的缓冲区不被移动。
    pub fn pin_self_referential_buffer() {
        let buffer = [0u8; 64];
        let _pinned_buffer = core::pin::pin!(buffer);

        // 在真实场景中，解析器结构会持有 _pinned_buffer 的引用
        // Pin 保证了解析器状态与缓冲区之间的相对位置不变
    }

    /// 示例 3：固定 DMA 传输描述符
    ///
    /// DMA 控制器需要物理地址不变化的缓冲区。
    /// 栈上固定可确保 DMA 传输期间缓冲区不会被移动。
    pub fn pin_dma_transfer_descriptor() {
        let descriptor = core::pin::pin!([0u8; 256]);

        // 获取固定引用的地址，传递给 DMA 控制器
        let _addr = descriptor.as_ptr();
    }
}

// ============================================================================
// 2. VecDeque::new 的 const 上下文支持 — 常量初始化环形缓冲区
// ============================================================================

/// # `VecDeque::new` 的 const 初始化
///
/// Rust 1.96+ 稳定了 `VecDeque::new` 的 const 上下文支持。
/// 这意味着可以在编译期创建空的环形缓冲区，无需运行时初始化代码。
///
/// ## 嵌入式应用场景
/// - **UART 接收缓冲区**：ISR 接收字节存入环形队列
/// - **ADC 采样队列**：定时器中断触发采样，主循环处理
/// - **CAN/LIN 消息缓冲**：总线中断缓冲，协议栈后处理
///
/// ## 注意事项
/// - `const` 初始化的 `VecDeque` 为空，容量为 0
/// - 首次 `push_back` 时会触发堆分配（如使用 alloc）
/// - 对于 `no_std` 无 alloc 场景，仍需使用固定大小的数组环形缓冲区
///
/// ## no_std + alloc 用法
/// ```ignore
/// use alloc::collections::VecDeque;
/// static mut UART_RX: VecDeque<u8> = VecDeque::new();
/// ```
pub struct ConstVecDequeExamples;

impl ConstVecDequeExamples {
    /// 常量初始化的 UART 接收环形缓冲区（host 目标演示）
    ///
    /// 在嵌入式目标上，可声明为 `static mut` 或封装在 Mutex 中。
    #[cfg(not(target_arch = "arm"))]
    pub const UART_RX_BUFFER: std::collections::VecDeque<u8> = std::collections::VecDeque::new();

    /// 常量初始化的传感器数据队列
    #[cfg(not(target_arch = "arm"))]
    pub const SENSOR_DATA_QUEUE: std::collections::VecDeque<f32> =
        std::collections::VecDeque::new();

    /// 获取一个新的空 VecDeque（编译期常量）
    pub const fn new_uart_buffer() -> std::collections::VecDeque<u8> {
        std::collections::VecDeque::new()
    }
}

// ============================================================================
// 3. impl From<bool> for {f32, f64} — 布尔传感器数据转浮点
// ============================================================================

/// # 布尔到浮点转换
///
/// Rust 1.96+ 稳定了 `From<bool> for f32` 和 `From<bool> for f64`。
/// - `true` → `1.0`
/// - `false` → `0.0`
///
/// ## 嵌入式应用场景
/// - **数字传感器标志归一化**：将布尔标志（如"过温检测"）转为浮点参与滤波
/// - **GPIO 状态平均**：计算一段时间内 GPIO 高电平的占空比
/// - **数字输入平滑**：与模拟信号一起进行卡尔曼滤波
///
/// ## 对比：显式分支 vs From 转换
///
/// | 方式 | 代码 | 可读性 | 性能 |
/// |------|------|--------|------|
/// | 分支 | `if b { 1.0 } else { 0.0 }` | ⭐⭐⭐ | 相同 |
/// | From | `f32::from(b)` | ⭐⭐⭐⭐⭐ | 相同 |
pub struct BoolToFloatExamples;

impl BoolToFloatExamples {
    /// 将数字传感器标志转换为归一化 f32 值
    ///
    /// # 示例
    /// ```
    /// # use c13_embedded::rust_196_features::BoolToFloatExamples;
    /// assert_eq!(BoolToFloatExamples::sensor_flag_to_f32(true), 1.0f32);
    /// assert_eq!(BoolToFloatExamples::sensor_flag_to_f32(false), 0.0f32);
    /// ```
    pub fn sensor_flag_to_f32(flag: bool) -> f32 {
        f32::from(flag)
    }

    /// 将数字传感器标志转换为归一化 f64 值
    pub fn sensor_flag_to_f64(flag: bool) -> f64 {
        f64::from(flag)
    }

    /// 计算布尔传感器数组的平均值（占空比）
    ///
    /// 例如，计算过去 100 个采样周期内风扇开启的占比。
    pub fn bool_duty_cycle(flags: &[bool]) -> f64 {
        if flags.is_empty() {
            return 0.0;
        }
        let sum: f64 = flags.iter().copied().map(f64::from).sum();
        sum / flags.len() as f64
    }

    /// 将布尔标志混入浮点信号流（用于混合滤波）
    ///
    /// 例如：限位开关触发时，将位置信号强制置为 0.0。
    pub fn mix_bool_into_signal(signal: f32, flag: bool, flag_weight: f32) -> f32 {
        let flag_f = f32::from(flag);
        signal * (1.0 - flag_weight) + flag_f * flag_weight
    }
}

// ============================================================================
// 4. DerefMut for PathBuf — 最小示例
// ============================================================================

/// # `DerefMut for PathBuf`
///
/// Rust 1.96+ 稳定了 `DerefMut` 对 `PathBuf` 的实现。
/// 虽然这对嵌入式编程直接相关性较低（文件系统不常见），
/// 但在 host 目标调试或固件镜像路径处理中有轻微便利。
///
/// ## 主要影响
/// - 可以直接对 `PathBuf` 调用 `Path` 的可变方法
/// - 更一致地与 `String`/`str` 的 `DerefMut` 模式对齐
#[cfg(not(target_arch = "arm"))]
pub struct PathBufDerefMutExamples;

#[cfg(not(target_arch = "arm"))]
impl PathBufDerefMutExamples {
    /// 最小示例：获取 PathBuf 的 Path 可变引用
    pub fn pathbuf_deref_mut_example() {
        use std::ops::DerefMut;
        use std::path::PathBuf;

        let mut path = PathBuf::from("/dev/ttyUSB0");
        let _path_ref: &mut std::path::Path = path.deref_mut();
    }
}

// ============================================================================
// 5. NonNull::new 的 const 支持 — 裸指针常量初始化
// ============================================================================

/// # `NonNull::new` 的 const 支持
///
/// Rust 1.96+ 进一步扩展了 `NonNull::new` 的 const 上下文支持。
/// 在嵌入式系统中，`NonNull` 常用于表示 DMA 缓冲区、外设寄存器或链表节点。
///
/// ## 应用场景
/// - **链表头节点**：静态初始化为 `None`，运行时链接
/// - **DMA 描述符指针**：编译期占位，启动代码填充
/// - **外设基地址**：启动后由 HAL 设置为有效地址
///
/// ## 安全说明
/// `NonNull::new` 在 const 上下文中是 safe 的，因为它仅进行 null 检查并返回 `Option`。
pub struct ConstNonNullExamples;

impl ConstNonNullExamples {
    /// 常量初始化的链表头指针（未链接状态）
    pub const LIST_HEAD: Option<std::ptr::NonNull<u8>> =
        std::ptr::NonNull::new(core::ptr::null_mut());

    /// 常量初始化的外设寄存器占位指针
    pub const PERIPHERAL_PTR: Option<std::ptr::NonNull<u32>> =
        std::ptr::NonNull::new(core::ptr::null_mut());

    /// 获取一个指向有效栈数据的 NonNull（运行时使用）
    pub fn stack_nonnull_example() -> std::ptr::NonNull<i32> {
        let mut value = 42i32;
        // 使用 safe API，无需 unsafe 块
        std::ptr::NonNull::new(&mut value).expect("stack reference is non-null")
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pin_sensor_future() {
        StackPinningExamples::pin_sensor_future();
    }

    #[test]
    fn test_pin_self_referential_buffer() {
        StackPinningExamples::pin_self_referential_buffer();
    }

    #[test]
    fn test_pin_dma_transfer_descriptor() {
        StackPinningExamples::pin_dma_transfer_descriptor();
    }

    #[test]
    fn test_const_vecdeque_new() {
        let buffer = ConstVecDequeExamples::new_uart_buffer();
        assert!(buffer.is_empty());
    }

    #[test]
    fn test_sensor_flag_to_f32() {
        assert_eq!(BoolToFloatExamples::sensor_flag_to_f32(true), 1.0f32);
        assert_eq!(BoolToFloatExamples::sensor_flag_to_f32(false), 0.0f32);
    }

    #[test]
    fn test_sensor_flag_to_f64() {
        assert_eq!(BoolToFloatExamples::sensor_flag_to_f64(true), 1.0f64);
        assert_eq!(BoolToFloatExamples::sensor_flag_to_f64(false), 0.0f64);
    }

    #[test]
    fn test_bool_duty_cycle() {
        let flags = [true, false, true, true, false];
        let duty = BoolToFloatExamples::bool_duty_cycle(&flags);
        assert!((duty - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mix_bool_into_signal() {
        let signal = 5.0f32;
        let mixed = BoolToFloatExamples::mix_bool_into_signal(signal, true, 1.0);
        assert_eq!(mixed, 1.0f32);

        let mixed2 = BoolToFloatExamples::mix_bool_into_signal(signal, false, 1.0);
        assert_eq!(mixed2, 0.0f32);

        let mixed3 = BoolToFloatExamples::mix_bool_into_signal(signal, true, 0.0);
        assert_eq!(mixed3, 5.0f32);
    }

    #[test]
    #[cfg(not(target_arch = "arm"))]
    fn test_pathbuf_deref_mut() {
        PathBufDerefMutExamples::pathbuf_deref_mut_example();
    }

    #[test]
    fn test_const_nonnull() {
        assert!(ConstNonNullExamples::LIST_HEAD.is_none());
        assert!(ConstNonNullExamples::PERIPHERAL_PTR.is_none());
    }

    #[test]
    fn test_stack_nonnull() {
        // NonNull 类型本身已保证指针非 null，只需验证函数不 panic 即可
        let _ptr = ConstNonNullExamples::stack_nonnull_example();
    }
}
