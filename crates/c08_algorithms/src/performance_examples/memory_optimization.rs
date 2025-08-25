//! 内存优化实践示例
//! 
//! 本模块演示Rust中的内存优化技术：
//! - 内存池 (Memory Pools)
//! - 对象池 (Object Pools)
//! - 零拷贝优化 (Zero-Copy Optimization)
//! - 内存对齐优化 (Memory Alignment)

use std::alloc::{alloc, dealloc, Layout};
use std::ptr;
use std::sync::Arc;
use std::collections::VecDeque;
use std::sync::Mutex;

/// 简单内存池实现
/// 
/// 预分配固定大小的内存块，减少动态分配开销
pub struct MemoryPool {
    block_size: usize,
    blocks: VecDeque<*mut u8>,
    layout: Layout,
}

impl MemoryPool {
    /// 创建新的内存池
    pub fn new(block_size: usize, initial_capacity: usize) -> Self {
        let layout = Layout::from_size_align(block_size, 8).unwrap();
        let mut pool = Self {
            block_size,
            blocks: VecDeque::new(),
            layout,
        };
        
        // 预分配内存块
        for _ in 0..initial_capacity {
            unsafe {
                let ptr = alloc(layout);
                if !ptr.is_null() {
                    pool.blocks.push_back(ptr);
                }
            }
        }
        
        pool
    }

    /// 获取内存块
    pub fn allocate(&mut self) -> Option<*mut u8> {
        self.blocks.pop_front().or_else(|| {
            // 如果池中没有可用块，动态分配新的
            unsafe {
                let ptr = alloc(self.layout);
                if ptr.is_null() {
                    None
                } else {
                    Some(ptr)
                }
            }
        })
    }

    /// 归还内存块到池中
    pub fn deallocate(&mut self, ptr: *mut u8) {
        self.blocks.push_back(ptr);
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        // 释放所有预分配的内存块
        while let Some(ptr) = self.blocks.pop_front() {
            unsafe {
                dealloc(ptr, self.layout);
            }
        }
    }
}

/// 对象池实现
/// 
/// 重用对象实例，避免频繁的创建和销毁
pub struct ObjectPool<T> {
    objects: VecDeque<T>,
    factory: Box<dyn Fn() -> T>,
}

impl<T> ObjectPool<T> {
    /// 创建新的对象池
    pub fn new<F>(factory: F) -> Self 
    where
        F: Fn() -> T + 'static,
    {
        Self {
            objects: VecDeque::new(),
            factory: Box::new(factory),
        }
    }

    /// 获取对象
    pub fn acquire(&mut self) -> T {
        self.objects.pop_front().unwrap_or_else(|| (self.factory)())
    }

    /// 归还对象
    pub fn release(&mut self, obj: T) {
        self.objects.push_back(obj);
    }

    /// 获取池中对象数量
    pub fn len(&self) -> usize {
        self.objects.len()
    }
}

/// 线程安全的对象池
pub struct ThreadSafeObjectPool<T> {
    pool: Arc<Mutex<ObjectPool<T>>>,
}

impl<T> ThreadSafeObjectPool<T> {
    /// 创建新的线程安全对象池
    pub fn new<F>(factory: F) -> Self 
    where
        F: Fn() -> T + 'static,
    {
        Self {
            pool: Arc::new(Mutex::new(ObjectPool::new(factory))),
        }
    }

    /// 获取对象
    pub fn acquire(&self) -> T {
        self.pool.lock().unwrap().acquire()
    }

    /// 归还对象
    pub fn release(&self, obj: T) {
        self.pool.lock().unwrap().release(obj);
    }
}

/// 零拷贝缓冲区
/// 
/// 避免不必要的数据复制，提高性能
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    read_pos: usize,
    write_pos: usize,
}

impl ZeroCopyBuffer {
    /// 创建新的零拷贝缓冲区
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity],
            read_pos: 0,
            write_pos: 0,
        }
    }

    /// 写入数据（零拷贝）
    pub fn write(&mut self, data: &[u8]) -> usize {
        let available = self.data.len() - self.write_pos;
        let to_write = data.len().min(available);
        
        if to_write > 0 {
            self.data[self.write_pos..self.write_pos + to_write].copy_from_slice(&data[..to_write]);
            self.write_pos += to_write;
        }
        
        to_write
    }

    /// 读取数据（零拷贝）
    pub fn read(&mut self, buffer: &mut [u8]) -> usize {
        let available = self.write_pos - self.read_pos;
        let to_read = buffer.len().min(available);
        
        if to_read > 0 {
            buffer[..to_read].copy_from_slice(&self.data[self.read_pos..self.read_pos + to_read]);
            self.read_pos += to_read;
        }
        
        to_read
    }

    /// 获取可读数据长度
    pub fn readable_len(&self) -> usize {
        self.write_pos - self.read_pos
    }

    /// 获取可写空间长度
    pub fn writable_len(&self) -> usize {
        self.data.len() - self.write_pos
    }

    /// 重置缓冲区
    pub fn reset(&mut self) {
        self.read_pos = 0;
        self.write_pos = 0;
    }
}

/// 内存对齐优化示例
/// 
/// 确保数据结构按CPU缓存行对齐，提高访问效率
#[repr(align(64))]
pub struct CacheAlignedData {
    pub value: u64,
    pub padding: [u8; 56], // 填充到64字节（典型缓存行大小）
}

impl CacheAlignedData {
    pub fn new(value: u64) -> Self {
        Self {
            value,
            padding: [0; 56],
        }
    }
}

/// 内存优化基准测试
pub fn run_memory_optimization_benchmarks() {
    println!("=== 内存优化基准测试 ===");
    
    // 测试内存池
    let mut pool = MemoryPool::new(1024, 10);
    let start = std::time::Instant::now();
    
    for _ in 0..1000 {
        if let Some(ptr) = pool.allocate() {
            pool.deallocate(ptr);
        }
    }
    
    println!("内存池操作耗时: {:?}", start.elapsed());
    
    // 测试对象池
    let mut obj_pool = ObjectPool::new(|| String::new());
    let start = std::time::Instant::now();
    
    for _ in 0..1000 {
        let obj = obj_pool.acquire();
        obj_pool.release(obj);
    }
    
    println!("对象池操作耗时: {:?}", start.elapsed());
    
    // 测试零拷贝缓冲区
    let mut buffer = ZeroCopyBuffer::new(1024);
    let test_data = b"Hello, World!";
    let start = std::time::Instant::now();
    
    for _ in 0..1000 {
        buffer.write(test_data);
        let mut read_buffer = [0u8; 13];
        buffer.read(&mut read_buffer);
        buffer.reset();
    }
    
    println!("零拷贝缓冲区操作耗时: {:?}", start.elapsed());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pool() {
        let mut pool = MemoryPool::new(64, 5);
        
        let ptr1 = pool.allocate().unwrap();
        let ptr2 = pool.allocate().unwrap();
        
        assert_ne!(ptr1, ptr2);
        
        pool.deallocate(ptr1);
        pool.deallocate(ptr2);
    }

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::new(|| String::from("test"));
        
        let obj1 = pool.acquire();
        let obj2 = pool.acquire();
        
        assert_eq!(obj1, "test");
        assert_eq!(obj2, "test");
        
        pool.release(obj1);
        pool.release(obj2);
        
        assert_eq!(pool.len(), 2);
    }

    #[test]
    fn test_zero_copy_buffer() {
        let mut buffer = ZeroCopyBuffer::new(100);
        let test_data = b"Hello";
        
        let written = buffer.write(test_data);
        assert_eq!(written, 5);
        assert_eq!(buffer.readable_len(), 5);
        
        let mut read_buffer = [0u8; 5];
        let read = buffer.read(&mut read_buffer);
        assert_eq!(read, 5);
        assert_eq!(&read_buffer, test_data);
    }

    #[test]
    fn test_cache_aligned_data() {
        let data = CacheAlignedData::new(42);
        assert_eq!(data.value, 42);
        
        // 验证对齐
        let ptr = &data as *const _ as usize;
        assert_eq!(ptr % 64, 0);
    }
}
