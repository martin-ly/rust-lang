//! Rust 1.92.0 WASM 特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在 WASM 场景中的应用，包括：
//! - `MaybeUninit` 在 WASM 内存管理中的应用
//! - `NonZero::div_ceil` 在 WASM 缓冲区分配中的应用
//! - WASM 特定的性能优化
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::mem::MaybeUninit;
use std::num::NonZeroUsize;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

// ==================== 1. MaybeUninit 在 WASM 内存管理中的应用 ====================

/// WASM 内存缓冲区，使用 MaybeUninit 优化
///
/// Rust 1.92.0: 改进的 MaybeUninit 文档和有效性检查
pub struct WasmBuffer {
    buffer: Vec<MaybeUninit<u8>>,
    initialized_len: usize,
}

impl WasmBuffer {
    /// 创建指定大小的 WASM 缓冲区
    pub fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        unsafe {
            buffer.set_len(capacity);
        }
        WasmBuffer {
            buffer,
            initialized_len: 0,
        }
    }

    /// 写入数据到缓冲区
    ///
    /// Rust 1.92.0: 使用 MaybeUninit 确保安全性
    pub unsafe fn write(&mut self, data: &[u8]) -> usize {
        let write_len = data.len().min(self.buffer.len() - self.initialized_len);
        for i in 0..write_len {
            self.buffer[self.initialized_len + i].write(data[i]);
        }
        self.initialized_len += write_len;
        write_len
    }

    /// 读取已初始化的数据
    pub unsafe fn read(&self, len: usize) -> Vec<u8> {
        let read_len = len.min(self.initialized_len);
        let mut result = Vec::with_capacity(read_len);
        for i in 0..read_len {
            result.push(self.buffer[i].assume_init_read());
        }
        result
    }

    /// 获取已初始化的长度
    pub fn initialized_len(&self) -> usize {
        self.initialized_len
    }

    /// 获取容量
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }
}

/// WASM 对象池，用于重用内存
pub struct WasmObjectPool<T> {
    pool: Vec<MaybeUninit<T>>,
    available: usize,
}

impl<T> WasmObjectPool<T> {
    /// 创建指定大小的对象池
    pub fn new(size: usize) -> Self {
        let mut pool = Vec::with_capacity(size);
        unsafe {
            pool.set_len(size);
        }
        WasmObjectPool { pool, available: 0 }
    }

    /// 从池中获取对象（如果可用）
    pub unsafe fn acquire(&mut self) -> Option<T> {
        if self.available == 0 {
            return None;
        }
        self.available -= 1;
        Some(self.pool[self.available].assume_init_read())
    }

    /// 归还对象到池中
    pub unsafe fn release(&mut self, obj: T) {
        if self.available < self.pool.len() {
            self.pool[self.available].write(obj);
            self.available += 1;
        }
    }
}

// ==================== 2. NonZero::div_ceil 在 WASM 缓冲区分配中的应用 ====================

/// 使用 NonZero::div_ceil 计算 WASM 缓冲区块数
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算向上取整除法
pub fn calculate_buffer_chunks(
    total_size: usize,
    chunk_size: NonZeroUsize,
) -> usize {
    if total_size == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_size).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算需要的块数
    total.div_ceil(chunk_size).get()
}

/// WASM 内存分配器配置
pub struct WasmAllocatorConfig {
    page_size: NonZeroUsize,
    max_pages: usize,
}

impl WasmAllocatorConfig {
    pub fn new(page_size: NonZeroUsize, max_pages: usize) -> Self {
        WasmAllocatorConfig {
            page_size,
            max_pages,
        }
    }

    /// 计算需要的 WASM 页面数
    pub fn calculate_pages(&self, total_bytes: usize) -> usize {
        if total_bytes == 0 {
            return 0;
        }
        let total = NonZeroUsize::new(total_bytes).unwrap();
        total.div_ceil(self.page_size).get().min(self.max_pages)
    }
}

/// WASM 数据传输配置
pub struct WasmTransferConfig {
    packet_size: NonZeroUsize,
}

impl WasmTransferConfig {
    pub fn new(packet_size: NonZeroUsize) -> Self {
        WasmTransferConfig { packet_size }
    }

    /// 计算需要的数据包数量
    pub fn calculate_packets(&self, data_size: usize) -> usize {
        if data_size == 0 {
            return 0;
        }
        let total = NonZeroUsize::new(data_size).unwrap();
        total.div_ceil(self.packet_size).get()
    }
}

// ==================== 3. WASM 特定的性能优化 ====================

/// WASM 优化的数组处理
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub struct WasmOptimizedProcessor {
    buffer: WasmBuffer,
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
impl WasmOptimizedProcessor {
    #[wasm_bindgen(constructor)]
    pub fn new(capacity: usize) -> WasmOptimizedProcessor {
        WasmOptimizedProcessor {
            buffer: WasmBuffer::new(capacity),
        }
    }

    /// 处理数据（WASM 绑定）
    #[wasm_bindgen]
    pub fn process(&mut self, data: &[u8]) -> usize {
        unsafe { self.buffer.write(data) }
    }

    /// 获取已处理的数据长度
    #[wasm_bindgen]
    pub fn processed_len(&self) -> usize {
        self.buffer.initialized_len()
    }
}

/// 非 WASM 平台的兼容实现
#[cfg(not(target_arch = "wasm32"))]
pub struct WasmOptimizedProcessor {
    buffer: WasmBuffer,
}

#[cfg(not(target_arch = "wasm32"))]
impl WasmOptimizedProcessor {
    pub fn new(capacity: usize) -> WasmOptimizedProcessor {
        WasmOptimizedProcessor {
            buffer: WasmBuffer::new(capacity),
        }
    }

    pub fn process(&mut self, data: &[u8]) -> usize {
        unsafe { self.buffer.write(data) }
    }

    pub fn processed_len(&self) -> usize {
        self.buffer.initialized_len()
    }
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 WASM 特性
pub fn demonstrate_rust_192_wasm_features() {
    println!("\n=== Rust 1.92.0 WASM 特性演示 ===\n");

    // 1. MaybeUninit 在 WASM 内存管理中的应用
    println!("1. MaybeUninit 在 WASM 内存管理中的应用:");
    let mut buffer = WasmBuffer::new(100);
    let data = b"Hello, WASM!";
    unsafe {
        let written = buffer.write(data);
        println!("   写入 {} 字节", written);
        println!("   已初始化长度: {}", buffer.initialized_len());
    }

    // 2. NonZero::div_ceil 在缓冲区分配中的应用
    println!("\n2. NonZero::div_ceil 在缓冲区分配中的应用:");
    let chunk_size = NonZeroUsize::new(1024).unwrap();
    let total_size = 5000;
    let chunks = calculate_buffer_chunks(total_size, chunk_size);
    println!("   总大小: {} 字节", total_size);
    println!("   块大小: {} 字节", chunk_size);
    println!("   需要的块数: {}", chunks);

    let allocator = WasmAllocatorConfig::new(NonZeroUsize::new(65536).unwrap(), 100);
    let pages = allocator.calculate_pages(1000000);
    println!("   WASM 页面大小: 65536 字节");
    println!("   1MB 数据需要页面数: {}", pages);

    let transfer = WasmTransferConfig::new(NonZeroUsize::new(1024).unwrap());
    let packets = transfer.calculate_packets(5000);
    println!("   数据包大小: 1024 字节");
    println!("   5000 字节需要数据包数: {}", packets);

    // 3. WASM 优化的处理器
    println!("\n3. WASM 优化的处理器:");
    let mut processor = WasmOptimizedProcessor::new(1000);
    let written = processor.process(b"WASM Data");
    println!("   处理的数据长度: {}", written);
    println!("   已处理长度: {}", processor.processed_len());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_buffer() {
        let mut buffer = WasmBuffer::new(100);
        assert_eq!(buffer.initialized_len(), 0);
        assert_eq!(buffer.capacity(), 100);

        unsafe {
            let data = b"test";
            buffer.write(data);
            assert_eq!(buffer.initialized_len(), 4);
        }
    }

    #[test]
    fn test_calculate_buffer_chunks() {
        let chunk_size = NonZeroUsize::new(1024).unwrap();
        assert_eq!(calculate_buffer_chunks(0, chunk_size), 0);
        assert_eq!(calculate_buffer_chunks(1024, chunk_size), 1);
        assert_eq!(calculate_buffer_chunks(1025, chunk_size), 2);
        assert_eq!(calculate_buffer_chunks(5000, chunk_size), 5);
    }

    #[test]
    fn test_wasm_allocator_config() {
        let config = WasmAllocatorConfig::new(NonZeroUsize::new(65536).unwrap(), 100);
        assert_eq!(config.calculate_pages(0), 0);
        assert_eq!(config.calculate_pages(65536), 1);
        assert_eq!(config.calculate_pages(65537), 2);
    }

    #[test]
    fn test_wasm_transfer_config() {
        let config = WasmTransferConfig::new(NonZeroUsize::new(1024).unwrap());
        assert_eq!(config.calculate_packets(0), 0);
        assert_eq!(config.calculate_packets(1024), 1);
        assert_eq!(config.calculate_packets(1025), 2);
    }

    #[test]
    fn test_wasm_optimized_processor() {
        let mut processor = WasmOptimizedProcessor::new(100);
        assert_eq!(processor.processed_len(), 0);
        processor.process(b"test");
        assert_eq!(processor.processed_len(), 4);
    }
}
