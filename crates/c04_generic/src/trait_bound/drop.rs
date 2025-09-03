/*
Drop trait 是 Rust 中用于资源清理的重要特征。
它定义了 `drop` 方法，允许类型在离开作用域时进行清理操作。

## 定义

Drop trait 定义了一个 `drop` 方法：

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

## 重要特性

1. **自动调用**: 当值离开作用域时自动调用
2. **手动实现**: 不能通过 derive 自动实现
3. **资源管理**: 用于释放内存、关闭文件、释放锁等
4. **确定性**: 保证资源在正确的时间被释放

## 实现示例

### 1. 基本结构体实现 Drop

```rust
struct Resource {
    name: String,
    data: Vec<u8>,
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Dropping resource: {}", self.name);
        // 清理资源
        self.data.clear();
    }
}
```

### 2. 泛型类型实现 Drop

```rust
struct Container<T> {
    value: T,
    metadata: String,
}

impl<T> Drop for Container<T> {
    fn drop(&mut self) {
        println!("Dropping container with metadata: {}", self.metadata);
        // 清理资源
    }
}
```

### 3. 智能指针实现 Drop

```rust
struct SmartPointer<T> {
    data: *mut T,
}

impl<T> SmartPointer<T> {
    fn new(value: T) -> Self {
        let data = Box::into_raw(Box::new(value));
        SmartPointer { data }
    }
}

impl<T> Drop for SmartPointer<T> {
    fn drop(&mut self) {
        unsafe {
            // 释放内存
            let _ = Box::from_raw(self.data);
        }
    }
}
```

## 使用场景

### 1. 资源管理

```rust
struct FileHandle {
    path: String,
    file: Option<std::fs::File>,
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if let Some(file) = self.file.take() {
            println!("Closing file: {}", self.path);
            // 文件会在 drop 时自动关闭
        }
    }
}

fn main() {
    let handle = FileHandle {
        path: "example.txt".to_string(),
        file: std::fs::File::open("example.txt").ok(),
    };
    
    // 当 handle 离开作用域时，文件会自动关闭
}
```

### 2. 锁管理

```rust
use std::sync::Mutex;

struct GuardedResource<T> {
    data: T,
    mutex: Mutex<()>,
    _guard: Option<MutexGuard<()>>,
}

impl<T> GuardedResource<T> {
    fn new(data: T) -> Self {
        let mutex = Mutex::new(());
        let _guard = mutex.lock().ok();
        
        GuardedResource {
            data,
            mutex,
            _guard,
        }
    }
    
    fn access(&self) -> &T {
        &self.data
    }
}

impl<T> Drop for GuardedResource<T> {
    fn drop(&mut self) {
        // 锁会在 drop 时自动释放
        println!("Releasing lock on resource");
    }
}
```

### 3. 内存管理

```rust
struct MemoryPool {
    data: Vec<u8>,
    capacity: usize,
}

impl MemoryPool {
    fn new(capacity: usize) -> Self {
        MemoryPool {
            data: Vec::with_capacity(capacity),
            capacity,
        }
    }
    
    fn allocate(&mut self, size: usize) -> Option<&mut [u8]> {
        if self.data.len() + size <= self.capacity {
            let start = self.data.len();
            self.data.extend(std::iter::repeat(0).take(size));
            Some(&mut self.data[start..start + size])
        } else {
            None
        }
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        println!("Releasing memory pool with capacity: {}", self.capacity);
        // 内存会在 drop 时自动释放
        self.data.clear();
        self.data.shrink_to_fit();
    }
}
```

## 性能考虑

1. **零成本**: Drop 实现通常是零成本的
2. **编译时优化**: 编译器可以优化 drop 调用
3. **内存效率**: 避免内存泄漏
4. **延迟释放**: 资源在正确的时间被释放

## 最佳实践

1. **资源清理**: 确保所有资源都被正确清理
2. **性能**: 避免在 drop 中进行昂贵的操作
3. **安全性**: 确保 drop 实现是安全的
4. **测试**: 为资源清理编写测试

## 高级用法

### 1. 条件清理

```rust
impl Drop for ConditionalResource {
    fn drop(&mut self) {
        if self.needs_cleanup {
            println!("Performing cleanup");
            self.cleanup();
        }
    }
}
```

### 2. 链式清理

```rust
impl Drop for ChainedResource {
    fn drop(&mut self) {
        // 按顺序清理资源
        self.cleanup_primary();
        self.cleanup_secondary();
        self.cleanup_tertiary();
    }
}
```

### 3. 错误处理

```rust
impl Drop for ErrorHandlingResource {
    fn drop(&mut self) {
        if let Err(e) = self.cleanup() {
            eprintln!("Error during cleanup: {}", e);
        }
    }
}
```

## 总结

Drop trait 为 Rust 提供了资源管理的核心机制。
通过正确实现 Drop，可以确保资源在正确的时间被释放，
同时保持零成本抽象的优势。
*/

use std::sync::Mutex;
use std::sync::MutexGuard;

// 示例资源结构体
pub struct DropExample {
    pub name: String,
    pub data: Vec<u8>,
    pub active: bool,
}

impl Drop for DropExample {
    fn drop(&mut self) {
        println!("Dropping resource: {}", self.name);
        
        // 清理资源
        if self.active {
            println!("  - Resource was active, performing cleanup");
            self.data.clear();
            self.active = false;
        }
        
        println!("  - Resource cleanup completed");
    }
}

// 泛型容器
pub struct DropContainer<T> {
    pub value: T,
    pub metadata: String,
    pub cleanup_required: bool,
}

impl<T> Drop for DropContainer<T> {
    fn drop(&mut self) {
        println!("Dropping container with metadata: {}", self.metadata);
        
        if self.cleanup_required {
            println!("  - Container requires cleanup");
            // 执行清理操作
        }
        
        println!("  - Container cleanup completed");
    }
}

// 文件句柄模拟
pub struct FileHandle {
    pub path: String,
    pub is_open: bool,
    pub file_size: usize,
}

impl FileHandle {
    pub fn new(path: String) -> Self {
        FileHandle {
            path,
            is_open: true,
            file_size: 0,
        }
    }
    
    pub fn read(&mut self, data: &mut [u8]) -> usize {
        if self.is_open {
            // 模拟读取操作
            let bytes_read = data.len().min(1024);
            self.file_size += bytes_read;
            bytes_read
        } else {
            0
        }
    }
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        if self.is_open {
            println!("Closing file: {}", self.path);
            println!("  - File size: {} bytes", self.file_size);
            
            // 关闭文件
            self.is_open = false;
            self.file_size = 0;
            
            println!("  - File closed successfully");
        }
    }
}

// 内存池
pub struct MemoryPool {
    pub data: Vec<u8>,
    pub capacity: usize,
    pub allocated: usize,
}

impl MemoryPool {
    pub fn new(capacity: usize) -> Self {
        MemoryPool {
            data: Vec::with_capacity(capacity),
            capacity,
            allocated: 0,
        }
    }
    
    pub fn allocate(&mut self, size: usize) -> Option<&mut [u8]> {
        if self.allocated + size <= self.capacity {
            let start = self.data.len();
            self.data.extend(std::iter::repeat(0).take(size));
            self.allocated += size;
            Some(&mut self.data[start..start + size])
        } else {
            None
        }
    }
    
    pub fn get_usage(&self) -> f64 {
        self.allocated as f64 / self.capacity as f64
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        println!("Releasing memory pool");
        println!("  - Capacity: {} bytes", self.capacity);
        println!("  - Allocated: {} bytes", self.allocated);
        println!("  - Usage: {:.1}%", self.get_usage() * 100.0);
        
        // 清理内存
        self.data.clear();
        self.data.shrink_to_fit();
        self.allocated = 0;
        
        println!("  - Memory pool released successfully");
    }
}

// 锁保护资源
pub struct GuardedResource<T> {
    pub data: T,
    pub _guard: Option<MutexGuard<'static, ()>>,
}

impl<T> GuardedResource<T> {
    pub fn new(data: T) -> Self {
        // 使用静态 Mutex 来避免生命周期问题
        static STATIC_MUTEX: Mutex<()> = Mutex::new(());
        let _guard = STATIC_MUTEX.lock().ok();
        
        GuardedResource {
            data,
            _guard,
        }
    }
    
    pub fn access(&self) -> &T {
        &self.data
    }
}

impl<T> Drop for GuardedResource<T> {
    fn drop(&mut self) {
        println!("Releasing lock on guarded resource");
        
        // 锁会在 drop 时自动释放
        self._guard = None;
        
        println!("  - Lock released successfully");
    }
}

// 演示函数
pub fn demonstrate_drop() {
    println!("=== Drop Trait Demonstration ===\n");
    
    // 基本资源清理
    {
        let resource = DropExample {
            name: "Test Resource".to_string(),
            data: vec![1, 2, 3, 4, 5],
            active: true,
        };
        
        println!("Created resource: {}", resource.name);
        println!("Resource data length: {}", resource.data.len());
        
        // 资源会在作用域结束时自动 drop
    }
    println!();
    
    // 文件句柄清理
    {
        let mut file = FileHandle::new("example.txt".to_string());
        
        let mut buffer = [0u8; 512];
        let bytes_read = file.read(&mut buffer);
        
        println!("Read {} bytes from file", bytes_read);
        println!("File is open: {}", file.is_open);
        
        // 文件会在作用域结束时自动关闭
    }
    println!();
    
    // 内存池清理
    {
        let mut pool = MemoryPool::new(1024);
        
        if let Some(_memory) = pool.allocate(256) {
            println!("Allocated 256 bytes from pool");
            println!("Pool usage: {:.1}%", pool.get_usage() * 100.0);
        }
        
        if let Some(_memory) = pool.allocate(128) {
            println!("Allocated 128 bytes from pool");
            println!("Pool usage: {:.1}%", pool.get_usage() * 100.0);
        }
        
        // 内存池会在作用域结束时自动释放
    }
    println!();
    
    // 锁保护资源清理
    {
        let resource = GuardedResource::new("Protected Data".to_string());
        
        println!("Accessing protected resource: {}", resource.access());
        
        // 锁会在作用域结束时自动释放
    }
    println!();
    
    // 泛型容器清理
    {
        let container = DropContainer {
            value: 42,
            metadata: "Test Container".to_string(),
            cleanup_required: true,
        };
        
        println!("Created container with value: {}", container.value);
        
        // 容器会在作用域结束时自动清理
    }
    println!();
    
    println!("=== All resources have been cleaned up ===");
}

// 条件清理示例
pub struct ConditionalResource {
    pub name: String,
    pub needs_cleanup: bool,
    pub cleanup_count: u32,
}

impl ConditionalResource {
    pub fn new(name: String, needs_cleanup: bool) -> Self {
        ConditionalResource {
            name,
            needs_cleanup,
            cleanup_count: 0,
        }
    }
    
    pub fn mark_dirty(&mut self) {
        self.needs_cleanup = true;
        self.cleanup_count += 1;
    }
    
    pub fn cleanup(&mut self) {
        if self.needs_cleanup {
            println!("  - Performing cleanup (attempt #{})", self.cleanup_count);
            self.needs_cleanup = false;
        }
    }
}

impl Drop for ConditionalResource {
    fn drop(&mut self) {
        println!("Dropping conditional resource: {}", self.name);
        
        if self.needs_cleanup {
            println!("  - Resource needs cleanup");
            self.cleanup();
        } else {
            println!("  - Resource is clean, no cleanup needed");
        }
        
        println!("  - Conditional resource cleanup completed");
    }
}

// 链式清理示例
pub struct ChainedResource {
    pub name: String,
    pub primary_cleanup_done: bool,
    pub secondary_cleanup_done: bool,
    pub tertiary_cleanup_done: bool,
}

impl ChainedResource {
    pub fn new(name: String) -> Self {
        ChainedResource {
            name,
            primary_cleanup_done: false,
            secondary_cleanup_done: false,
            tertiary_cleanup_done: false,
        }
    }
    
    pub fn cleanup_primary(&mut self) {
        if !self.primary_cleanup_done {
            println!("  - Performing primary cleanup");
            self.primary_cleanup_done = true;
        }
    }
    
    pub fn cleanup_secondary(&mut self) {
        if !self.secondary_cleanup_done {
            println!("  - Performing secondary cleanup");
            self.secondary_cleanup_done = true;
        }
    }
    
    pub fn cleanup_tertiary(&mut self) {
        if !self.tertiary_cleanup_done {
            println!("  - Performing tertiary cleanup");
            self.tertiary_cleanup_done = true;
        }
    }
}

impl Drop for ChainedResource {
    fn drop(&mut self) {
        println!("Dropping chained resource: {}", self.name);
        
        // 按顺序清理资源
        self.cleanup_primary();
        self.cleanup_secondary();
        self.cleanup_tertiary();
        
        println!("  - Chained resource cleanup completed");
    }
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_drop_example() {
        let resource = DropExample {
            name: "Test".to_string(),
            data: vec![1, 2, 3],
            active: true,
        };
        
        assert_eq!(resource.name, "Test");
        assert_eq!(resource.data.len(), 3);
        assert!(resource.active);
        
        // 资源会在测试结束时自动 drop
    }
    
    #[test]
    fn test_file_handle() {
        let file = FileHandle::new("test.txt".to_string());
        
        assert_eq!(file.path, "test.txt");
        assert!(file.is_open);
        assert_eq!(file.file_size, 0);
        
        // 文件会在测试结束时自动关闭
    }
    
    #[test]
    fn test_memory_pool() {
        let mut pool = MemoryPool::new(1024);
        
        assert_eq!(pool.capacity, 1024);
        assert_eq!(pool.allocated, 0);
        
        if let Some(memory) = pool.allocate(256) {
            assert_eq!(memory.len(), 256);
            assert_eq!(pool.allocated, 256);
        }
        
        // 内存池会在测试结束时自动释放
    }
    
    #[test]
    fn test_conditional_resource() {
        let mut resource = ConditionalResource::new("Test".to_string(), false);
        
        assert_eq!(resource.name, "Test");
        assert!(!resource.needs_cleanup);
        
        resource.mark_dirty();
        assert!(resource.needs_cleanup);
        assert_eq!(resource.cleanup_count, 1);
        
        // 资源会在测试结束时自动清理
    }
    
    #[test]
    fn test_chained_resource() {
        let resource = ChainedResource::new("Test".to_string());
        
        assert_eq!(resource.name, "Test");
        assert!(!resource.primary_cleanup_done);
        assert!(!resource.secondary_cleanup_done);
        assert!(!resource.tertiary_cleanup_done);
        
        // 资源会在测试结束时自动清理
    }
}
