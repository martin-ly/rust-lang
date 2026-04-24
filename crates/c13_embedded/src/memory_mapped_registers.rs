//! 内存映射寄存器 (Memory-Mapped I/O, MMIO)
//!
//! 在嵌入式系统中，外设寄存器被映射到特定的内存地址。
//! 通过读写这些地址来控制硬件（如 GPIO、UART、定时器等）。
//!
//! ## 核心概念
//!
//! - **volatile 访问**：编译器不能优化或重排对外设的读写
//! - **对齐要求**：寄存器通常需要 32 位或 16 位对齐
//! - **原子性**：某些外设访问需要是原子的

/// 模拟的内存映射 GPIO 寄存器组
///
/// 以 STM32F1 风格的 GPIO 为例：
/// - MODER: 模式寄存器
/// - ODR:   输出数据寄存器
/// - IDR:   输入数据寄存器
///
/// 真实硬件中，这些结构体通过 `#[repr(C)]` 保证内存布局，
/// 并使用 `volatile-register` crate 或原始指针访问。
#[repr(C)]
pub struct GpioRegisters {
    /// 端口模式寄存器（每个引脚 2 位）
    pub moder: u32,
    /// 输出类型寄存器
    pub otyper: u32,
    /// 输出速度寄存器
    pub ospeedr: u32,
    /// 上拉/下拉寄存器
    pub pupdr: u32,
    /// 输入数据寄存器
    pub idr: u32,
    /// 输出数据寄存器
    pub odr: u32,
    /// 位设置/清除寄存器
    pub bsrr: u32,
    /// 配置锁定寄存器
    pub lckr: u32,
}

/// GPIO 寄存器基地址（模拟）
///
/// 在真实硬件上，这是固定的内存地址，例如：
/// `const GPIOA: *mut GpioRegisters = 0x4002_0000 as *mut GpioRegisters;`
pub const GPIOA_BASE: usize = 0x4002_0000;

/// 安全的 GPIO 包装器
///
/// 通过 Rust 的所有权和借用检查，确保寄存器访问的安全。
pub struct GpioPort {
    base: *mut GpioRegisters,
}

// 在 bare-metal 中，Send 和 Sync 需要手动实现，因为原始指针默认不实现
unsafe impl Send for GpioPort {}
unsafe impl Sync for GpioPort {}

impl GpioPort {
    /// 创建新的 GPIO 端口实例（unsafe，因为需要确保地址有效）
    ///
    /// # Safety
    ///
    /// 调用者必须确保 `base` 指向有效的 GPIO 寄存器组。
    pub const unsafe fn new(base: usize) -> Self {
        Self {
            base: base as *mut GpioRegisters,
        }
    }

    /// 读取 MODER 寄存器
    ///
    /// 使用 `core::ptr::read_volatile` 确保编译器不会优化掉读操作。
    pub fn read_moder(&self) -> u32 {
        // Safety: 构造时已保证 base 有效
        unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).moder)) }
    }

    /// 写入 MODER 寄存器
    pub fn write_moder(&mut self, value: u32) {
        // Safety: 构造时已保证 base 有效，&mut self 确保独占访问
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).moder), value) }
    }

    /// 设置特定引脚为输出模式
    pub fn set_pin_output(&mut self, pin: u8) {
        assert!(pin < 16, "引脚号必须在 0-15 范围内");
        let mut moder = self.read_moder();
        let shift = pin * 2;
        // 清除该引脚的模式位，设置为 01（输出模式）
        moder &= !(0b11 << shift);
        moder |= 0b01 << shift;
        self.write_moder(moder);
    }

    /// 设置特定引脚电平（高电平）
    pub fn set_pin_high(&mut self, pin: u8) {
        assert!(pin < 16, "引脚号必须在 0-15 范围内");
        // BSRR 寄存器：低 16 位设置，高 16 位清除
        let bsrr = 1 << pin;
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).bsrr), bsrr) }
    }

    /// 清除特定引脚电平（低电平）
    pub fn set_pin_low(&mut self, pin: u8) {
        assert!(pin < 16, "引脚号必须在 0-15 范围内");
        let bsrr = 1 << (pin + 16);
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).bsrr), bsrr) }
    }

    /// 读取引脚输入状态
    pub fn read_pin(&self, pin: u8) -> bool {
        assert!(pin < 16, "引脚号必须在 0-15 范围内");
        let idr = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).idr)) };
        (idr & (1 << pin)) != 0
    }
}

/// 位操作工具函数
///
/// 嵌入式编程中大量涉及位操作。
pub struct BitOps;

impl BitOps {
    /// 设置指定位
    pub const fn set_bit(value: u32, bit: u8) -> u32 {
        value | (1 << bit)
    }

    /// 清除指定位
    pub const fn clear_bit(value: u32, bit: u8) -> u32 {
        value & !(1 << bit)
    }

    /// 翻转指定位
    pub const fn toggle_bit(value: u32, bit: u8) -> u32 {
        value ^ (1 << bit)
    }

    /// 检查指定位是否为 1
    pub const fn is_bit_set(value: u32, bit: u8) -> bool {
        (value & (1 << bit)) != 0
    }

    /// 修改位域（value 写入 bits 范围的位）
    pub const fn modify_bits(original: u32, start: u8, width: u8, value: u32) -> u32 {
        let mask = ((1u32 << width) - 1) << start;
        (original & !mask) | ((value << start) & mask)
    }
}

/// 使用 `volatile-register` crate 的示例（ARM 目标下）
///
/// ```rust,ignore
/// use volatile_register::{RW, RO, WO};
///
/// #[repr(C)]
/// pub struct RegisterBlock {
///     pub moder: RW<u32>,
///     pub odr: RW<u32>,
///     pub idr: RO<u32>,
/// }
/// ```
#[cfg(target_arch = "arm")]
pub mod volatile_register_example {
    // 仅在 ARM 目标下编译真实代码
    // host 上不导入 volatile-register，确保 cargo check 通过
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_ops() {
        assert_eq!(BitOps::set_bit(0b0000, 2), 0b0100);
        assert_eq!(BitOps::clear_bit(0b1111, 1), 0b1101);
        assert_eq!(BitOps::toggle_bit(0b1010, 1), 0b1000);
        assert!(BitOps::is_bit_set(0b1000, 3));
        assert!(!BitOps::is_bit_set(0b1000, 2));
    }

    #[test]
    fn test_modify_bits() {
        // 将 0xABCD_1234 的 bit[7:4] 改为 0xF
        let result = BitOps::modify_bits(0xABCD_1234, 4, 4, 0xF);
        assert_eq!(result, 0xABCD_12F4);
    }

    #[test]
    fn test_gpio_port_mock() {
        // 在 host 上，使用堆分配的模拟内存验证结构体布局
        let mut gpio_memory = GpioRegisters {
            moder: 0,
            otyper: 0,
            ospeedr: 0,
            pupdr: 0,
            idr: 0,
            odr: 0,
            bsrr: 0,
            lckr: 0,
        };

        let mut gpio = unsafe { GpioPort::new(&mut gpio_memory as *mut _ as usize) };
        gpio.set_pin_output(5);
        assert_ne!(gpio_memory.moder, 0);
        gpio.set_pin_high(5);
        assert_eq!(gpio_memory.bsrr, 1 << 5);
        gpio.set_pin_low(5);
        assert_eq!(gpio_memory.bsrr, 1 << (5 + 16));
    }
}
