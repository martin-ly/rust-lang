//! Rust 1.93.0 嵌入式 特性模块
#![allow(clippy::incompatible_msrv)]

use std::mem::MaybeUninit;

/// 使用 `MaybeUninit` 在嵌入式风格中延迟初始化寄存器值
pub fn lazy_register_init() -> u32 {
    let mut reg = MaybeUninit::uninit();
    reg.write(0xDEAD_BEEF);
    // SAFETY: 刚刚写入
    unsafe { *reg.assume_init_ref() }
}

/// 使用 `MaybeUninit::assume_init_drop` 安全释放嵌入式资源
pub fn safe_resource_drop() {
    let mut resource = MaybeUninit::new([0xAAu8; 16]);
    // SAFETY: resource 包含已初始化的数组
    unsafe { resource.assume_init_drop() };
}

/// 使用 `char::MAX_LEN_UTF8` 配置 UART 发送缓冲区（单字符最大字节数）
pub fn uart_char_buffer_size() -> usize {
    char::MAX_LEN_UTF8
}

/// 使用 `char::MAX_LEN_UTF16` 配置 DMA 缓冲区
pub fn dma_utf16_buffer_size() -> usize {
    char::MAX_LEN_UTF16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_register_init() {
        assert_eq!(lazy_register_init(), 0xDEAD_BEEF);
    }

    #[test]
    fn test_safe_resource_drop() {
        safe_resource_drop();
    }

    #[test]
    fn test_uart_char_buffer_size() {
        assert_eq!(uart_char_buffer_size(), 4);
    }

    #[test]
    fn test_dma_utf16_buffer_size() {
        assert_eq!(dma_utf16_buffer_size(), 2);
    }
}
