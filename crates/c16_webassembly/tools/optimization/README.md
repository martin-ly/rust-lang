# WebAssembly 优化工具集

## 核心优化工具

### 1. wasm-opt (Binaryen)

- **功能**: WebAssembly二进制优化
- **优化类型**:
  - 代码大小优化 (-Os)
  - 性能优化 (-O3)
  - 调试信息优化 (-g)
  - 死代码消除
- **使用方法**:

```bash
# 安装
npm install -g binaryen

# 基本优化
wasm-opt -Os input.wasm -o output.wasm

# 性能优化
wasm-opt -O3 input.wasm -o output.wasm

# 调试优化
wasm-opt -g input.wasm -o output.wasm
```

### 2. wasm-pack 优化

- **功能**: Rust WebAssembly包优化
- **优化选项**:
  - 大小优化
  - 性能优化
  - 调试支持
- **配置示例**:

```toml
# Cargo.toml
[package.metadata.wasm-pack.profile.release]
opt-level = "s"  # 大小优化
lto = true       # 链接时优化
codegen-units = 1 # 单代码生成单元
panic = "abort"  # 快速失败
```

### 3. Rust编译器优化

- **功能**: 编译时优化
- **优化级别**:
  - `-C opt-level=0`: 无优化
  - `-C opt-level=1`: 基本优化
  - `-C opt-level=2`: 默认优化
  - `-C opt-level=3`: 最大优化
  - `-C opt-level=s`: 大小优化
  - `-C opt-level=z`: 最大大小优化

## 内存优化

### 1. 内存池管理

```rust
use std::collections::VecDeque;

pub struct MemoryPool {
    pools: Vec<VecDeque<Vec<u8>>>,
    sizes: Vec<usize>,
}

impl MemoryPool {
    pub fn new() -> Self {
        Self {
            pools: vec![VecDeque::new(); 8], // 8个不同大小的池
            sizes: vec![64, 128, 256, 512, 1024, 2048, 4096, 8192],
        }
    }
    
    pub fn allocate(&mut self, size: usize) -> Vec<u8> {
        let pool_index = self.find_pool_index(size);
        if let Some(mut buffer) = self.pools[pool_index].pop_front() {
            buffer.clear();
            buffer.reserve(size);
            buffer
        } else {
            vec![0u8; size]
        }
    }
    
    pub fn deallocate(&mut self, mut buffer: Vec<u8>) {
        let size = buffer.capacity();
        if let Some(pool_index) = self.find_pool_index_by_capacity(size) {
            if self.pools[pool_index].len() < 10 { // 限制池大小
                self.pools[pool_index].push_back(buffer);
            }
        }
    }
    
    fn find_pool_index(&self, size: usize) -> usize {
        self.sizes.iter().position(|&s| s >= size).unwrap_or(7)
    }
    
    fn find_pool_index_by_capacity(&self, capacity: usize) -> Option<usize> {
        self.sizes.iter().position(|&s| s == capacity)
    }
}
```

### 2. 零拷贝优化

```rust
use std::slice;

pub struct ZeroCopyBuffer<'a> {
    data: &'a [u8],
    offset: usize,
}

impl<'a> ZeroCopyBuffer<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, offset: 0 }
    }
    
    pub fn read_u32(&mut self) -> Option<u32> {
        if self.offset + 4 <= self.data.len() {
            let bytes = &self.data[self.offset..self.offset + 4];
            self.offset += 4;
            Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
        } else {
            None
        }
    }
    
    pub fn read_slice(&mut self, len: usize) -> Option<&'a [u8]> {
        if self.offset + len <= self.data.len() {
            let slice = &self.data[self.offset..self.offset + len];
            self.offset += len;
            Some(slice)
        } else {
            None
        }
    }
}
```

## 性能优化

### 1. SIMD优化

```rust
use std::arch::wasm32::*;

pub fn simd_add_vectors(a: &[f32], b: &[f32], result: &mut [f32]) {
    let chunks = a.chunks_exact(4);
    let b_chunks = b.chunks_exact(4);
    let result_chunks = result.chunks_exact_mut(4);
    
    for ((a_chunk, b_chunk), result_chunk) in chunks.zip(b_chunks).zip(result_chunks) {
        unsafe {
            let a_simd = v128_load(a_chunk.as_ptr() as *const v128);
            let b_simd = v128_load(b_chunk.as_ptr() as *const v128);
            let sum = f32x4_add(a_simd, b_simd);
            v128_store(result_chunk.as_mut_ptr() as *mut v128, sum);
        }
    }
}
```

### 2. 批量操作优化

```rust
pub struct BatchProcessor<T> {
    batch_size: usize,
    buffer: Vec<T>,
}

impl<T> BatchProcessor<T> {
    pub fn new(batch_size: usize) -> Self {
        Self {
            batch_size,
            buffer: Vec::with_capacity(batch_size),
        }
    }
    
    pub fn add(&mut self, item: T) -> Option<Vec<T>> {
        self.buffer.push(item);
        
        if self.buffer.len() >= self.batch_size {
            Some(std::mem::replace(&mut self.buffer, Vec::with_capacity(self.batch_size)))
        } else {
            None
        }
    }
    
    pub fn flush(&mut self) -> Vec<T> {
        std::mem::replace(&mut self.buffer, Vec::with_capacity(self.batch_size))
    }
}
```

## 代码生成优化

### 1. 模板特化

```rust
use std::marker::PhantomData;

pub trait OptimizedProcessor<T> {
    fn process(&self, data: &[T]) -> Vec<T>;
}

pub struct GenericProcessor<T> {
    _phantom: PhantomData<T>,
}

impl<T> GenericProcessor<T> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

// 为特定类型特化
impl OptimizedProcessor<u32> for GenericProcessor<u32> {
    fn process(&self, data: &[u32]) -> Vec<u32> {
        // 针对u32的优化实现
        data.iter().map(|&x| x * 2).collect()
    }
}

impl OptimizedProcessor<f32> for GenericProcessor<f32> {
    fn process(&self, data: &[f32]) -> Vec<f32> {
        // 针对f32的优化实现
        data.iter().map(|&x| x * 2.0).collect()
    }
}
```

### 2. 内联优化

```rust
#[inline(always)]
pub fn fast_add(a: i32, b: i32) -> i32 {
    a + b
}

#[inline(never)]
pub fn slow_complex_operation(data: &[i32]) -> i32 {
    // 复杂操作，不内联以避免代码膨胀
    data.iter().fold(0, |acc, &x| acc + x * x)
}

// 条件内联
#[inline]
pub fn conditional_add(a: i32, b: i32) -> i32 {
    if a > 0 && b > 0 {
        fast_add(a, b)
    } else {
        slow_complex_operation(&[a, b])
    }
}
```

## 运行时优化

### 1. 缓存优化

```rust
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

pub struct Cache<K, V> {
    cache: HashMap<u64, V>,
    max_size: usize,
}

impl<K, V> Cache<K, V>
where
    K: Hash,
    V: Clone,
{
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: HashMap::with_capacity(max_size),
            max_size,
        }
    }
    
    pub fn get(&self, key: &K) -> Option<&V> {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        self.cache.get(&hash)
    }
    
    pub fn insert(&mut self, key: K, value: V) {
        if self.cache.len() >= self.max_size {
            // 简单的LRU策略：清除一半缓存
            let keys_to_remove: Vec<u64> = self.cache.keys().take(self.max_size / 2).cloned().collect();
            for key in keys_to_remove {
                self.cache.remove(&key);
            }
        }
        
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        self.cache.insert(hash, value);
    }
}
```

### 2. 预分配优化

```rust
pub struct PreallocatedBuffer {
    buffer: Vec<u8>,
    position: usize,
}

impl PreallocatedBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: vec![0u8; capacity],
            position: 0,
        }
    }
    
    pub fn write_u32(&mut self, value: u32) -> Result<(), &'static str> {
        if self.position + 4 > self.buffer.len() {
            return Err("Buffer overflow");
        }
        
        let bytes = value.to_le_bytes();
        self.buffer[self.position..self.position + 4].copy_from_slice(&bytes);
        self.position += 4;
        Ok(())
    }
    
    pub fn write_slice(&mut self, data: &[u8]) -> Result<(), &'static str> {
        if self.position + data.len() > self.buffer.len() {
            return Err("Buffer overflow");
        }
        
        self.buffer[self.position..self.position + data.len()].copy_from_slice(data);
        self.position += data.len();
        Ok(())
    }
    
    pub fn reset(&mut self) {
        self.position = 0;
    }
    
    pub fn as_slice(&self) -> &[u8] {
        &self.buffer[..self.position]
    }
}
```

## 优化配置

### 1. Cargo.toml优化配置

```toml
[profile.release]
# 大小优化
opt-level = "s"
lto = true
codegen-units = 1
panic = "abort"

# 调试信息
debug = false
strip = true

# 性能优化
opt-level = 3
lto = "fat"
codegen-units = 16

[profile.dev]
# 开发环境优化
opt-level = 0
debug = true
```

### 2. wasm-pack配置

```toml
[package.metadata.wasm-pack.profile.release]
opt-level = "s"
lto = true
codegen-units = 1
panic = "abort"

[package.metadata.wasm-pack.profile.dev]
opt-level = 0
debug = true
```

## 性能基准测试

### 1. 基准测试框架

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_optimized_function(c: &mut Criterion) {
    c.bench_function("optimized_add", |b| {
        b.iter(|| {
            let result = fast_add(black_box(42), black_box(24));
            black_box(result)
        })
    });
}

fn benchmark_memory_pool(c: &mut Criterion) {
    c.bench_function("memory_pool_alloc", |b| {
        let mut pool = MemoryPool::new();
        b.iter(|| {
            let buffer = pool.allocate(black_box(1024));
            black_box(&buffer);
            pool.deallocate(buffer);
        })
    });
}

criterion_group!(benches, benchmark_optimized_function, benchmark_memory_pool);
criterion_main!(benches);
```

### 2. 性能分析

```rust
use std::time::Instant;

pub struct PerformanceProfiler {
    start_time: Instant,
    measurements: Vec<(String, u128)>,
}

impl PerformanceProfiler {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            measurements: Vec::new(),
        }
    }
    
    pub fn measure<F, R>(&mut self, name: &str, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed().as_micros();
        self.measurements.push((name.to_string(), duration));
        result
    }
    
    pub fn print_report(&self) {
        println!("Performance Report:");
        for (name, duration) &self.measurements {
            println!("  {}: {}μs", name, duration);
        }
    }
}
```

## 优化最佳实践

### 1. 选择正确的优化级别

- **开发阶段**: 使用 `-C opt-level=0` 快速编译
- **测试阶段**: 使用 `-C opt-level=1` 平衡编译速度和性能
- **发布阶段**: 使用 `-C opt-level=s` 或 `-C opt-level=3`

### 2. 内存管理优化

- 使用内存池减少分配开销
- 预分配缓冲区避免动态分配
- 使用零拷贝技术减少内存复制

### 3. 算法优化

- 使用SIMD指令加速向量操作
- 批量处理减少函数调用开销
- 缓存热点数据减少重复计算

### 4. 代码结构优化

- 合理使用内联函数
- 避免不必要的动态分发
- 使用模板特化优化特定类型

## 总结

WebAssembly优化工具集提供了从编译时到运行时的全方位优化方案。通过合理使用这些工具和技术，可以显著提升WebAssembly应用的性能和效率。
