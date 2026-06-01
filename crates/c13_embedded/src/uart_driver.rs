//! UART 驱动示例
//! UART driver example

use core::fmt;

/// - RBR/THR: 接收缓冲/发送保持（共享地址）
/// - RBR/THR: buffering /（）
/// - IER: 中断使能
/// - IER: in
/// - IER: in断使能
/// - IER: in
/// - IIR/FCR: 中断标识/FIFO 控制
/// - IIR/FCR: in /FIFO
/// - IIR/FCR: in断标识/FIFO 控制
/// - LCR: 线控制
/// - LCR: line
/// - LSR: 线状态
/// - LSR: line state
#[repr(C)]
pub struct UartRegisters {
    /// 发送保持 / 接收缓冲（偏移 0）
    /// / buffering （ 0）
    pub thr_rbr: u32,
    /// 中断使能（偏移 4）
    /// in （ 4）
    pub ier: u32,
    /// FIFO 控制（偏移 8）
    /// FIFO （ 8）
    pub fcr: u32,
    /// 线控制（偏移 12）
    /// line （ 12）
    pub lcr: u32,
    /// 线状态（偏移 20）
    /// line state （ 20）
    /// linestate（偏移 20）
    pub lsr: u32,
}

/// 线状态寄存器位
/// line state
pub mod lsr_flags {
    /// 数据就绪
    /// data
    pub const DR: u32 = 1 << 0;
    /// 发送保持寄存器空
    pub const THRE: u32 = 1 << 5;
    /// 发送器空
    pub const TEMT: u32 = 1 << 6;
}

/// UART 驱动结构体
/// UART driver struct
/// 通过所有权确保同一时间只有一个驱动实例访问硬件。
/// ownership time driver hardware 。
pub struct UartDriver {
    base: *mut UartRegisters,
}

unsafe impl Send for UartDriver {}
unsafe impl Sync for UartDriver {}

impl UartDriver {
    /// 创建 UART 驱动实例
    /// UART driver
    ///
    pub const unsafe fn new(base: usize) -> Self {
        Self {
            base: base as *mut UartRegisters,
        }
    }

    /// 检查是否可以发送
    /// can
    fn is_transmit_empty(&self) -> bool {
        let lsr = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).lsr)) };
        (lsr & lsr_flags::THRE) != 0
    }

    /// 检查是否有数据可读
    /// data
    fn is_data_ready(&self) -> bool {
        let lsr = unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).lsr)) };
        (lsr & lsr_flags::DR) != 0
    }

    /// 发送单个字节（轮询方式）
    /// （poll way ）
    /// （way ）
    /// 阻塞直到发送保持寄存器为空。
    /// to as 。
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
    /// （poll way ）
    /// （way ）
    /// 如果没有数据，返回 `None`。
    /// if data ， `None`。
    /// if ， `None`。
    /// if没有数据，Return `None`。
    pub fn receive_byte(&self) -> Option<u8> {
        if self.is_data_ready() {
            let val =
                unsafe { core::ptr::read_volatile(core::ptr::addr_of!((*self.base).thr_rbr)) };
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
    /// UART（concept demonstration ）
    /// 真实实现需要配置波特率分频、数据位、停止位、校验等。
    /// real configuration 、data 、、etc. 。
    /// real 、、、etc. 。
    pub fn init(&mut self) {
        // 禁用中断（轮询模式）
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).ier), 0) };
        // 启用 FIFO
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).fcr), 0x01) };
        // 8 位数据，1 位停止，无校验
        unsafe { core::ptr::write_volatile(core::ptr::addr_of_mut!((*self.base).lcr), 0x03) };
    }
}

/// as UART Implementation of `fmt::Write` trait，Supports `write!` 宏
impl fmt::Write for UartDriver {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.send_str(s);
        Ok(())
    }
}

/// 中断驱动 UART 概念
/// in driver UART concept
/// in断driver UART concept
/// 中断驱动模式更高效，CPU 只在有数据时才处理 UART：
/// in driver efficient ，CPU in data UART：
/// in driver efficient ，CPU in UART：
/// 1. 配置 UART 中断使能（接收数据就绪中断）
/// 1. configuration UART in （data in ）
/// 1. UART in （in ）
/// 2. 在 NVIC 中启用 UART 中断
/// 2. in NVIC in UART in
/// 2. in NVIC in启用 UART in断
/// 3. 实现 ISR，在中断中读取/写入数据
/// 3. ISR，in in in /data
/// 3. ISR，in in in /
/// 4. 使用环形缓冲区解耦 ISR 和应用代码
/// 4. buffering ISR and application
/// #[interrupt]
/// fn UART0() {
///     let uart = unsafe { UART_DRIVER.as_mut().unwrap() };
///     if uart.is_data_ready() {
///         let byte = uart.receive_byte().unwrap();
///         RX_BUFFER.push(byte);
///     }
/// ```
pub struct InterruptDrivenUart;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(miri, ignore)]
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
    #[cfg_attr(miri, ignore)]
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
