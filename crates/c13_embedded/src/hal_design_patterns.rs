//! HAL 设计模式
//!
//! 硬件抽象层 (Hardware Abstraction Layer) 是嵌入式 Rust 的核心。
//! 通过类型系统和所有权，HAL 可以在编译时防止许多常见错误。
//!
//! ## 类型状态编程 (Type State)
//!
//! 利用泛型和 PhantomData，将外设状态编码到类型中。
//! 只有处于正确状态的外设才能执行对应操作。

use core::marker::PhantomData;

/// 外设状态标记
pub mod states {
    /// 未初始化状态
    pub struct Uninitialized;
    /// 已初始化状态
    pub struct Initialized;
    /// 正在传输状态
    pub struct Transmitting;
    /// 接收状态
    pub struct Receiving;
}

/// 类型状态 SPI 外设示例
///
/// STATE 泛型参数编码外设当前状态。
pub struct Spi<STATE> {
    _state: PhantomData<STATE>,
    base: usize,
}

impl Spi<states::Uninitialized> {
    /// 创建未初始化的 SPI 实例
    pub const fn new(base: usize) -> Self {
        Self {
            _state: PhantomData,
            base,
        }
    }

    /// 初始化 SPI，状态转换为 Initialized
    pub fn init(self, _baudrate: u32, _mode: u8) -> Spi<states::Initialized> {
        Spi {
            _state: PhantomData,
            base: self.base,
        }
    }
}

impl Spi<states::Initialized> {
    /// 发送数据，状态变为 Transmitting
    pub fn send(self, _data: &[u8]) -> Spi<states::Transmitting> {
        Spi {
            _state: PhantomData,
            base: self.base,
        }
    }

    /// 接收数据，状态变为 Receiving
    pub fn receive(self, _buf: &mut [u8]) -> Spi<states::Receiving> {
        Spi {
            _state: PhantomData,
            base: self.base,
        }
    }

    /// 反初始化
    pub fn deinit(self) -> Spi<states::Uninitialized> {
        Spi {
            _state: PhantomData,
            base: self.base,
        }
    }
}

impl Spi<states::Transmitting> {
    /// 检查传输是否完成
    pub fn is_complete(&self) -> bool {
        true
    }

    /// 等待传输完成
    pub fn wait(self) -> Spi<states::Initialized> {
        Spi {
            _state: PhantomData,
            base: self.base,
        }
    }
}

/// 所有权转移配置模式
///
/// 通过消耗 self 来确保每个配置步骤只执行一次。
pub struct UartBuilder {
    base: usize,
    baudrate: Option<u32>,
    data_bits: Option<u8>,
    parity: Option<bool>,
}

impl UartBuilder {
    /// 创建新的 UART 构建器
    pub const fn new(base: usize) -> Self {
        Self {
            base,
            baudrate: None,
            data_bits: None,
            parity: None,
        }
    }

    /// 设置波特率
    pub fn baudrate(mut self, rate: u32) -> Self {
        self.baudrate = Some(rate);
        self
    }

    /// 设置数据位
    pub fn data_bits(mut self, bits: u8) -> Self {
        self.data_bits = Some(bits);
        self
    }

    /// 设置校验位
    pub fn parity(mut self, enable: bool) -> Self {
        self.parity = Some(enable);
        self
    }

    /// 构建 UART 实例
    pub fn build(self) -> Result<UartInstance, &'static str> {
        let _ = self.baudrate.ok_or("波特率未设置")?;
        let _ = self.data_bits.ok_or("数据位未设置")?;
        Ok(UartInstance { base: self.base })
    }
}

/// 构建完成的 UART 实例
pub struct UartInstance {
    /// UART 寄存器基地址
    pub base: usize,
}

/// 零成本抽象演示
///
/// Rust 的泛型和内联优化确保 HAL 抽象在 release 模式下完全消除运行时开销。
pub struct ZeroCostAbstraction;

impl ZeroCostAbstraction {
    /// 内联优化的 GPIO 设置函数
    #[inline(always)]
    pub unsafe fn set_pin_optimized(gpio_base: *mut u32, pin: u8, high: bool) {
        let offset = if high { 0 } else { 16 };
        let value = 1 << (pin + offset);
        unsafe {
            core::ptr::write_volatile(gpio_base, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_state_spi() {
        let spi = Spi::<states::Uninitialized>::new(0x4001_3000);
        let spi = spi.init(1_000_000, 0);
        let spi = spi.send(b"hello");
        assert!(spi.is_complete());
        let spi = spi.wait();
        let _spi = spi.deinit();
    }

    #[test]
    fn test_uart_builder() {
        let uart = UartBuilder::new(0x4000_4400)
            .baudrate(115200)
            .data_bits(8)
            .parity(false)
            .build();
        assert!(uart.is_ok());
    }

    #[test]
    fn test_uart_builder_missing_baudrate() {
        let uart = UartBuilder::new(0x4000_4400).data_bits(8).build();
        assert!(uart.is_err());
    }
}
