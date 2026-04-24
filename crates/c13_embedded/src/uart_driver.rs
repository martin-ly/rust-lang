//! UART 驱动示例
//!
//! UART（通用异步收发传输器）是最基本的串行通信外设。
//! 本模块展示如何设计一个简单的轮询式 UART 驱动。

use core::fmt;

/// 模拟的 UART 寄存器组
///
/// 以典型的 16550 风格 UART 为例：
/// - RBR/THR: 接收缓冲/发送保持（共享地址）
/// - IER: 中断使能
/// - IIR/FCR: 中断标识/FIFO 控制
/// - LCR: 线控制
/// - LSR: 线状态
#[repr(C)]
pub struct UartRegisters {
    /// 发送保持 / 接收缓冲（偏移 0）
    pub thr_rbr: u32,
    /// 中断使能（偏移 4）
    pub ier: u32,
    /// FIFO 控制（偏移 8）
    pub fcr: u32,
    /// 线控制（偏移 12）
    pub lcr: u32,
    /// 线状态（偏移 20）
    pub lsr: u32,
}

/// 线状态寄存器位
pub mod lsr_flags {
    /// 数据就绪
    pub const DR: u32 = 1 << 0;
    /// 发送保持寄存器空
    pub const THRE: u32 = 1 << 5;
    /// 发送器空
    pub const TEMT: u32 = 1 << 6;
}

/// UART 驱动结构体
///
/// 通过所有权确保同一时间只有一个驱动实例访问硬件。
pub struct UartDriver {
    base: *mut UartRegisters,
}

unsafe impl Send for UartDriver {}
unsafe impl Sync for UartDriver {}

impl UartDriver {
    /// 创建 UART 驱动实例
    ///
    /// # Safety
    ///
    /// 调用者必须确保 `base` 指向有效的 UART 寄存器组。
    pub const unsafe fn new(base: usize) -> Self {
        Self {
            base: base as *mut UartRegisters,
        }
    }

    /// 检查是否可以发送
    fn is_transmit_empty(&self) -> bool {
        let lsr = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).lsr)) };
        (lsr & lsr_flags::THRE) != 0
    }

    /// 检查是否有数据可读
    fn is_data_ready(&self) -> bool {
        let lsr = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).lsr)) };
        (lsr & lsr_flags::DR) != 0
    }

    /// 发送单个字节（轮询方式）
    ///
    /// 阻塞直到发送保持寄存器为空。
    pub fn send_byte(&mut self, byte: u8) {
        while !self.is_transmit_empty() {
            // 在真实硬件上，这里会忙等待
            // 可使用 WFI 指令降低功耗：cortex_m::asm::wfi()
        }
        unsafe {
            core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).thr_rbr), byte as u32);
        }
    }

    /// 接收单个字节（轮询方式）
    ///
    /// 如果没有数据，返回 `None`。
    pub fn receive_byte(&self) -> Option<u8> {
        if self.is_data_ready() {
            let val = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).thr_rbr)) };
            Some(val as u8)
        } else {
            None
        }
    }

    /// 发送字符串
    pub fn send_str(&mut self, s: &str) {
        for byte in s.as_bytes() {
            self.send_byte(*byte);
        }
    }

    /// 初始化 UART（概念演示）
    ///
    /// 真实实现需要配置波特率分频、数据位、停止位、校验等。
    pub fn init(&mut self) {
        // 禁用中断（轮询模式）
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).ier), 0) };
        // 启用 FIFO
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).fcr), 0x01) };
        // 8 位数据，1 位停止，无校验
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).lcr), 0x03) };
    }
}

/// 为 UART 实现 `fmt::Write` trait，支持 `write!` 宏
impl fmt::Write for UartDriver {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.send_str(s);
        Ok(())
    }
}

/// 中断驱动 UART 概念
///
/// 中断驱动模式更高效，CPU 只在有数据时才处理 UART：
///
/// 1. 配置 UART 中断使能（接收数据就绪中断）
/// 2. 在 NVIC 中启用 UART 中断
/// 3. 实现 ISR，在中断中读取/写入数据
/// 4. 使用环形缓冲区解耦 ISR 和应用代码
///
/// ```rust,ignore
/// #[interrupt]
/// fn UART0() {
///     let uart = unsafe { UART_DRIVER.as_mut().unwrap() };
///     if uart.is_data_ready() {
///         let byte = uart.receive_byte().unwrap();
///         RX_BUFFER.push(byte);
///     }
/// }
/// ```
pub struct InterruptDrivenUart;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uart_driver_mock() {
        let mut uart_mem = UartRegisters {
            thr_rbr: 0,
            ier: 0,
            fcr: 0,
            lcr: 0,
            lsr: lsr_flags::THRE, // 初始状态：发送寄存器为空
        };

        let mut uart = unsafe { UartDriver::new(&mut uart_mem as *mut _ as usize) };
        uart.init();
        assert_eq!(uart_mem.ier, 0);
        assert_eq!(uart_mem.fcr, 0x01);
        assert_eq!(uart_mem.lcr, 0x03);
    }

    #[test]
    fn test_uart_send_receive() {
        let mut uart_mem = UartRegisters {
            thr_rbr: 0,
            ier: 0,
            fcr: 0,
            lcr: 0,
            lsr: lsr_flags::THRE | lsr_flags::DR, // 可发送且数据就绪
        };

        let mut uart = unsafe { UartDriver::new(&mut uart_mem as *mut _ as usize) };
        uart.send_byte(b'X');
        assert_eq!(uart_mem.thr_rbr, b'X' as u32);

        // 再次发送另一个字节，验证 receive_byte 能读到最新值
        uart.send_byte(b'Z');
        assert_eq!(uart.receive_byte(), Some(b'Z'));
    }
}
