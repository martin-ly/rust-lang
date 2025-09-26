//! 性能优化技巧演示模块
//! 
//! 本模块演示了 Rust 1.90 中的各种性能优化技巧，包括：
//! - 内存布局优化
//! - 零成本抽象
//! - 内联优化
//! - 分支预测优化
//! - 缓存友好的数据结构
//! - SIMD 优化
//! - 编译时优化

use std::arch::x86_64::*;
use std::mem;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

/// 内存布局优化演示
pub mod memory_layout {
    use super::*;

    /// 缓存行大小（通常为 64 字节）
    const CACHE_LINE_SIZE: usize = 64;

    /// 缓存友好的数据结构
    #[repr(align(64))]
    #[derive(Debug)]
    pub struct CacheAlignedData {
        pub value: u64,
        pub counter: AtomicUsize,
        _padding: [u8; CACHE_LINE_SIZE - 16], // 填充到缓存行大小
    }

    impl CacheAlignedData {
        pub fn new(value: u64) -> Self {
            Self {
                value,
                counter: AtomicUsize::new(0),
                _padding: [0; CACHE_LINE_SIZE - 16],
            }
        }

        /// 原子操作，避免伪共享
        pub fn increment(&self) -> usize {
            self.counter.fetch_add(1, Ordering::Relaxed)
        }
    }

    /// 结构体字段重排序优化
    #[derive(Debug, Clone)]
    pub struct OptimizedStruct {
        // 将经常一起访问的字段放在一起
        pub id: u32,
        pub status: u8,
        pub flags: u8,
        pub reserved: u16, // 填充到 8 字节边界
        pub data: [u8; 32],
    }

    impl OptimizedStruct {
        pub fn new(id: u32, status: u8, flags: u8, data: [u8; 32]) -> Self {
            Self {
                id,
                status,
                flags,
                reserved: 0,
                data,
            }
        }
    }

    /// 演示内存布局优化的性能差异
    pub fn demonstrate_memory_layout_optimization() {
        println!("=== 内存布局优化演示 ===");
        
        // 创建缓存对齐的数据
        let aligned_data = CacheAlignedData::new(42);
        println!("缓存对齐数据大小: {} 字节", mem::size_of::<CacheAlignedData>());
        
        // 演示原子操作
        for i in 0..5 {
            let count = aligned_data.increment();
            println!("原子操作 {}: 计数器 = {}", i + 1, count);
        }
        
        // 演示结构体优化
        let optimized = OptimizedStruct::new(1, 2, 3, [0; 32]);
        println!("优化结构体大小: {} 字节", mem::size_of::<OptimizedStruct>());
        println!("优化结构体: {:?}", optimized);
    }
}

/// 零成本抽象演示
pub mod zero_cost_abstractions {
    use super::*;

    /// 零成本抽象：编译时计算
    pub const fn compile_time_fibonacci(n: u32) -> u32 {
        match n {
            0 => 0,
            1 => 1,
            _ => compile_time_fibonacci(n - 1) + compile_time_fibonacci(n - 2),
        }
    }

    /// 零成本抽象：泛型特化
    pub trait Processor<T> {
        fn process(&self, data: T) -> T;
    }

    pub struct FastProcessor;
    pub struct SlowProcessor;

    impl Processor<u32> for FastProcessor {
        #[inline(always)]
        fn process(&self, data: u32) -> u32 {
            data * 2
        }
    }

    impl Processor<u64> for FastProcessor {
        #[inline(always)]
        fn process(&self, data: u64) -> u64 {
            data << 1 // 位运算比乘法更快
        }
    }

    impl Processor<u32> for SlowProcessor {
        fn process(&self, data: u32) -> u32 {
            // 模拟复杂计算
            let mut result = data;
            for _ in 0..1000 {
                result = result.wrapping_mul(3).wrapping_add(1);
            }
            result
        }
    }

    /// 零成本抽象：编译时类型检查
    pub struct TypeId<T> {
        _phantom: std::marker::PhantomData<T>,
    }

    impl<T> TypeId<T> {
        pub const fn new() -> Self {
            Self {
                _phantom: std::marker::PhantomData,
            }
        }
    }

    /// 演示零成本抽象
    pub fn demonstrate_zero_cost_abstractions() {
        println!("=== 零成本抽象演示 ===");
        
        // 编译时计算
        const FIB_10: u32 = compile_time_fibonacci(10);
        println!("编译时计算斐波那契数列第10项: {}", FIB_10);
        
        // 泛型特化
        let fast_processor = FastProcessor;
        let slow_processor = SlowProcessor;
        
        let start = Instant::now();
        let result1 = fast_processor.process(42u32);
        let fast_time = start.elapsed();
        
        let start = Instant::now();
        let result2 = slow_processor.process(42u32);
        let slow_time = start.elapsed();
        
        println!("快速处理器结果: {}, 耗时: {:?}", result1, fast_time);
        println!("慢速处理器结果: {}, 耗时: {:?}", result2, slow_time);
        
        // 类型ID（零成本）
        let _type_id = TypeId::<u32>::new();
        println!("类型ID创建完成（零成本）");
    }
}

/// 内联优化演示
pub mod inlining_optimization {
    use super::*;

    /// 内联函数
    #[inline(always)]
    pub fn fast_add(a: u32, b: u32) -> u32 {
        a.wrapping_add(b)
    }

    /// 条件内联
    #[inline]
    pub fn conditional_multiply(x: u32, factor: u32) -> u32 {
        if factor == 0 {
            0
        } else if factor == 1 {
            x
        } else {
            x * factor
        }
    }

    /// 热路径优化
    pub struct HotPathOptimizer {
        cache: Vec<u32>,
    }

    impl HotPathOptimizer {
        pub fn new(size: usize) -> Self {
            Self {
                cache: vec![0; size],
            }
        }

        /// 热路径：频繁调用的函数
        #[inline(always)]
        pub fn hot_path_lookup(&self, index: usize) -> Option<u32> {
            self.cache.get(index).copied()
        }

        /// 冷路径：不经常调用的函数
        pub fn cold_path_operation(&mut self, index: usize, value: u32) {
            if index < self.cache.len() {
                self.cache[index] = value;
            }
        }
    }

    /// 演示内联优化
    pub fn demonstrate_inlining_optimization() {
        println!("=== 内联优化演示 ===");
        
        let start = Instant::now();
        let mut sum = 0u32;
        for i in 0..1_000_000 {
            sum = fast_add(sum, i as u32);
        }
        let inline_time = start.elapsed();
        println!("内联函数求和: {}, 耗时: {:?}", sum, inline_time);
        
        let optimizer = HotPathOptimizer::new(1000);
        let start = Instant::now();
        for i in 0..1000 {
            let _ = optimizer.hot_path_lookup(i);
        }
        let hot_path_time = start.elapsed();
        println!("热路径查找耗时: {:?}", hot_path_time);
    }
}

/// 分支预测优化演示
pub mod branch_prediction {
    use super::*;

    /// 分支预测友好的代码
    pub fn branch_friendly_sum(data: &[u32]) -> u32 {
        let mut sum = 0;
        for &value in data {
            // 使用位运算而不是分支
            sum += value;
        }
        sum
    }

    /// 分支预测不友好的代码
    pub fn branch_unfriendly_sum(data: &[u32]) -> u32 {
        let mut sum = 0;
        for &value in data {
            // 频繁的分支判断
            if value > 100 {
                sum += value * 2;
            } else if value > 50 {
                sum += value;
            } else {
                sum += value / 2;
            }
        }
        sum
    }

    /// 使用查找表优化分支
    pub struct LookupTable {
        table: [u32; 256],
    }

    impl LookupTable {
        pub fn new() -> Self {
            let mut table = [0u32; 256];
            for i in 0..256 {
                table[i] = (i as u32).wrapping_mul(3).wrapping_add(1);
            }
            Self { table }
        }

        #[inline(always)]
        pub fn lookup(&self, index: u8) -> u32 {
            self.table[index as usize]
        }
    }

    /// 演示分支预测优化
    pub fn demonstrate_branch_prediction() {
        println!("=== 分支预测优化演示 ===");
        
        let data: Vec<u32> = (0..10000).collect();
        
        let start = Instant::now();
        let result1 = branch_friendly_sum(&data);
        let friendly_time = start.elapsed();
        
        let start = Instant::now();
        let result2 = branch_unfriendly_sum(&data);
        let unfriendly_time = start.elapsed();
        
        println!("分支友好求和: {}, 耗时: {:?}", result1, friendly_time);
        println!("分支不友好求和: {}, 耗时: {:?}", result2, unfriendly_time);
        
        // 查找表优化
        let lookup_table = LookupTable::new();
        let start = Instant::now();
        let mut sum = 0u32;
        for i in 0..10000 {
            sum += lookup_table.lookup((i % 256) as u8);
        }
        let lookup_time = start.elapsed();
        println!("查找表求和: {}, 耗时: {:?}", sum, lookup_time);
    }
}

/// SIMD 优化演示
pub mod simd_optimization {
    use super::*;

    /// SIMD 向量加法（需要 x86_64 支持）
    #[cfg(target_arch = "x86_64")]
    pub unsafe fn simd_add_vectors(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len().min(b.len()).min(result.len());
        let mut i = 0;
        
        // 处理 4 个元素为一组
        while i + 4 <= len {
            unsafe {
                let va = _mm_loadu_ps(a.as_ptr().add(i));
                let vb = _mm_loadu_ps(b.as_ptr().add(i));
                let vc = _mm_add_ps(va, vb);
                _mm_storeu_ps(result.as_mut_ptr().add(i), vc);
            }
            i += 4;
        }
        
        // 处理剩余元素
        while i < len {
            result[i] = a[i] + b[i];
            i += 1;
        }
    }

    /// 标量向量加法（对比用）
    pub fn scalar_add_vectors(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len().min(b.len()).min(result.len());
        for i in 0..len {
            result[i] = a[i] + b[i];
        }
    }

    /// 演示 SIMD 优化
    pub fn demonstrate_simd_optimization() {
        println!("=== SIMD 优化演示 ===");
        
        let size = 10000;
        let a: Vec<f32> = (0..size).map(|i| i as f32).collect();
        let b: Vec<f32> = (0..size).map(|i| (i * 2) as f32).collect();
        let mut result_scalar = vec![0.0f32; size];
        let mut result_simd = vec![0.0f32; size];
        
        // 标量版本
        let start = Instant::now();
        scalar_add_vectors(&a, &b, &mut result_scalar);
        let scalar_time = start.elapsed();
        
        // SIMD 版本
        #[cfg(target_arch = "x86_64")]
        {
            let start = Instant::now();
            unsafe {
                simd_add_vectors(&a, &b, &mut result_simd);
            }
            let simd_time = start.elapsed();
            
            println!("标量向量加法耗时: {:?}", scalar_time);
            println!("SIMD 向量加法耗时: {:?}", simd_time);
            
            // 验证结果一致性
            let is_equal = result_scalar.iter()
                .zip(result_simd.iter())
                .all(|(a, b)| (a - b).abs() < 1e-6);
            println!("结果一致性检查: {}", is_equal);
        }
        
        #[cfg(not(target_arch = "x86_64"))]
        {
            println!("SIMD 优化需要 x86_64 架构支持");
        }
    }
}

/// 编译时优化演示
pub mod compile_time_optimization {

    /// 编译时常量
    pub const MAX_BUFFER_SIZE: usize = 1024;
    pub const ALIGNMENT: usize = 64;

    /// 编译时计算
    pub const fn calculate_offset(index: usize) -> usize {
        index * ALIGNMENT
    }

    /// 条件编译优化
    #[cfg(target_arch = "x86_64")]
    pub fn optimized_function() -> &'static str {
        "x86_64 优化版本"
    }

    #[cfg(not(target_arch = "x86_64"))]
    pub fn optimized_function() -> &'static str {
        "通用版本"
    }

    /// 编译时类型检查
    pub struct CompileTimeChecker<T> {
        _phantom: std::marker::PhantomData<T>,
    }

    impl<T> CompileTimeChecker<T> {
        pub const fn new() -> Self {
            Self {
                _phantom: std::marker::PhantomData,
            }
        }
    }

    /// 演示编译时优化
    pub fn demonstrate_compile_time_optimization() {
        println!("=== 编译时优化演示 ===");
        
        println!("最大缓冲区大小: {}", MAX_BUFFER_SIZE);
        println!("对齐大小: {}", ALIGNMENT);
        
        const OFFSET_5: usize = calculate_offset(5);
        println!("索引 5 的偏移量: {}", OFFSET_5);
        
        println!("优化函数: {}", optimized_function());
        
        let _checker = CompileTimeChecker::<u32>::new();
        println!("编译时类型检查器创建完成");
    }
}

/// 性能分析工具
pub mod profiling_tools {
    use std::time::Instant;

    /// 性能计时器
    pub struct PerformanceTimer {
        start_time: Instant,
        name: String,
    }

    impl PerformanceTimer {
        pub fn new(name: &str) -> Self {
            Self {
                start_time: Instant::now(),
                name: name.to_string(),
            }
        }

        pub fn elapsed(&self) -> std::time::Duration {
            self.start_time.elapsed()
        }
    }

    impl Drop for PerformanceTimer {
        fn drop(&mut self) {
            let elapsed = self.start_time.elapsed();
            println!("{} 耗时: {:?}", self.name, elapsed);
        }
    }

    /// 内存使用统计
    pub struct MemoryStats {
        pub allocated: usize,
        pub peak: usize,
    }

    impl MemoryStats {
        pub fn new() -> Self {
            Self {
                allocated: 0,
                peak: 0,
            }
        }

        pub fn allocate(&mut self, size: usize) {
            self.allocated += size;
            self.peak = self.peak.max(self.allocated);
        }

        pub fn deallocate(&mut self, size: usize) {
            self.allocated = self.allocated.saturating_sub(size);
        }
    }

    /// 演示性能分析工具
    pub fn demonstrate_profiling_tools() {
        println!("=== 性能分析工具演示 ===");
        
        let _timer = PerformanceTimer::new("性能测试");
        
        let mut stats = MemoryStats::new();
        stats.allocate(1024);
        stats.allocate(512);
        stats.deallocate(256);
        
        println!("当前分配内存: {} 字节", stats.allocated);
        println!("峰值内存使用: {} 字节", stats.peak);
        
        // 模拟一些工作
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

/// 主演示函数
pub fn demonstrate_performance_optimization() {
    println!("🚀 Rust 1.90 性能优化技巧演示");
    println!("=====================================");
    
    memory_layout::demonstrate_memory_layout_optimization();
    println!();
    
    zero_cost_abstractions::demonstrate_zero_cost_abstractions();
    println!();
    
    inlining_optimization::demonstrate_inlining_optimization();
    println!();
    
    branch_prediction::demonstrate_branch_prediction();
    println!();
    
    simd_optimization::demonstrate_simd_optimization();
    println!();
    
    compile_time_optimization::demonstrate_compile_time_optimization();
    println!();
    
    profiling_tools::demonstrate_profiling_tools();
    println!();
    
    println!("✅ 性能优化技巧演示完成！");
}
