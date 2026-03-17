//! 内存安全高级演示模块
//!
//! 本模块演示了 Rust 1.90 中的各种内存安全高级特性，包括：
//! - 高级生命周期管理
//! - 内存布局优化
//! - 零成本抽象
//! - 智能指针高级用法
//! - 内存池和分配器
//! - 内存泄漏检测
//! - 缓冲区溢出防护
//! - 内存对齐和缓存优化
use std::alloc::{GlobalAlloc, Layout, System};
use std::marker::PhantomData;
use std::mem::{align_of, size_of};
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// 高级生命周期管理
pub mod advanced_lifetimes {
    use super::*;

    /// 生命周期追踪器
    pub struct LifetimeTracker<'a, T> {
        data: &'a T,
        created_at: Instant,
        tracker_id: u64,
    }

    impl<'a, T> LifetimeTracker<'a, T> {
        pub fn new(data: &'a T, tracker_id: u64) -> Self {
            Self {
                data,
                created_at: Instant::now(),
                tracker_id,
            }
        }

        pub fn age(&self) -> Duration {
            self.created_at.elapsed()
        }

        pub fn get_data(&self) -> &'a T {
            self.data
        }

        pub const fn tracker_id(&self) -> u64 {
            self.tracker_id
        }
    }

    /// 生命周期组合器
    pub struct LifetimeCombinator<'a, 'b, T, U>
    where
        T: 'a,
        U: 'b,
    {
        short_lived: &'a T,
        long_lived: &'b U,
        _phantom: PhantomData<(&'a T, &'b U)>,
    }

    impl<'a, 'b, T, U> LifetimeCombinator<'a, 'b, T, U>
    where
        T: 'a,
        U: 'b,
    {
        pub fn new(short_lived: &'a T, long_lived: &'b U) -> Self {
            Self {
                short_lived,
                long_lived,
                _phantom: PhantomData,
            }
        }

        pub fn get_short(&self) -> &'a T {
            self.short_lived
        }

        pub fn get_long(&self) -> &'b U {
            self.long_lived
        }

        pub fn combine<F, R>(&self, f: F) -> R
        where
            F: FnOnce(&'a T, &'b U) -> R,
        {
            f(self.short_lived, self.long_lived)
        }
    }

    /// 生命周期验证器
    pub struct LifetimeValidator<'a> {
        lifetime_id: &'a str,
        created_at: Instant,
        is_valid: bool,
    }

    impl<'a> LifetimeValidator<'a> {
        pub fn new(lifetime_id: &'a str) -> Self {
            Self {
                lifetime_id,
                created_at: Instant::now(),
                is_valid: true,
            }
        }

        pub fn validate(&self) -> bool {
            self.is_valid && self.created_at.elapsed() < Duration::from_secs(60)
        }

        pub fn invalidate(&mut self) {
            self.is_valid = false;
        }

        pub fn lifetime_id(&self) -> &'a str {
            self.lifetime_id
        }
    }
}

/// 内存布局优化
pub mod memory_layout {
    use super::*;

    /// 缓存行对齐的数据结构
    #[repr(align(64))]
    pub struct CacheAligned<T> {
        pub data: T,
        _padding: [u8; 64],
    }

    impl<T> CacheAligned<T> {
        pub fn new(data: T) -> Self {
            Self {
                data,
                _padding: [0; 64],
            }
        }

        pub fn get(&self) -> &T {
            &self.data
        }

        pub fn get_mut(&mut self) -> &mut T {
            &mut self.data
        }
    }

    /// 内存池分配器
    pub struct MemoryPool {
        blocks: Vec<*mut u8>,
        pub block_size: usize,
        pub total_blocks: usize,
        free_blocks: AtomicUsize,
    }

    impl MemoryPool {
        pub fn new(block_size: usize, total_blocks: usize) -> Self {
            let mut blocks = Vec::with_capacity(total_blocks);

            unsafe {
                for _ in 0..total_blocks {
                    let layout = Layout::from_size_align(block_size, align_of::<u8>()).unwrap();
                    let ptr = System.alloc(layout);
                    if !ptr.is_null() {
                        blocks.push(ptr);
                    }
                }
            }

            Self {
                blocks,
                block_size,
                total_blocks,
                free_blocks: AtomicUsize::new(total_blocks),
            }
        }

        pub fn allocate(&self) -> Option<*mut u8> {
            let current_free = self.free_blocks.load(Ordering::Acquire);
            if current_free == 0 {
                return None;
            }

            let new_free = current_free - 1;
            if self
                .free_blocks
                .compare_exchange_weak(current_free, new_free, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                Some(self.blocks[current_free - 1])
            } else {
                None
            }
        }

        pub fn deallocate(&self, _ptr: *mut u8) {
            // 在实际实现中，这里需要将指针返回到空闲列表
            self.free_blocks.fetch_add(1, Ordering::Release);
        }

        pub fn available_blocks(&self) -> usize {
            self.free_blocks.load(Ordering::Relaxed)
        }
    }

    impl Drop for MemoryPool {
        fn drop(&mut self) {
            unsafe {
                for &ptr in &self.blocks {
                    if !ptr.is_null() {
                        let layout =
                            Layout::from_size_align(self.block_size, align_of::<u8>()).unwrap();
                        System.dealloc(ptr, layout);
                    }
                }
            }
        }
    }

    /// 内存对齐工具
    pub struct AlignmentUtils;

    impl AlignmentUtils {
        pub fn align_up(addr: usize, alignment: usize) -> usize {
            (addr + alignment - 1) & !(alignment - 1)
        }

        pub fn align_down(addr: usize, alignment: usize) -> usize {
            addr & !(alignment - 1)
        }

        pub fn is_aligned(addr: usize, alignment: usize) -> bool {
            addr & (alignment - 1) == 0
        }

        pub fn get_alignment<T>() -> usize {
            align_of::<T>()
        }

        pub fn get_size<T>() -> usize {
            size_of::<T>()
        }
    }
}

/// 零成本抽象
pub mod zero_cost_abstractions {
    use super::*;

    /// 零成本包装器
    #[derive(Debug, Clone, Copy)]
    pub struct ZeroCostWrapper<T> {
        value: T,
    }

    impl<T> ZeroCostWrapper<T> {
        pub fn new(value: T) -> Self {
            Self { value }
        }

        pub fn get(&self) -> &T {
            &self.value
        }

        pub fn get_mut(&mut self) -> &mut T {
            &mut self.value
        }

        pub fn into_inner(self) -> T {
            self.value
        }
    }

    impl<T> Deref for ZeroCostWrapper<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            &self.value
        }
    }

    impl<T> DerefMut for ZeroCostWrapper<T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.value
        }
    }

    /// 编译时计算
    pub const fn compile_time_factorial(n: u32) -> u32 {
        match n {
            0 | 1 => 1,
            _ => n * compile_time_factorial(n - 1),
        }
    }

    /// 零成本迭代器
    pub struct ZeroCostIterator<'a, T> {
        data: &'a [T],
        index: usize,
    }

    impl<'a, T> ZeroCostIterator<'a, T> {
        pub fn new(slice: &'a [T]) -> Self {
            Self {
                data: slice,
                index: 0,
            }
        }
    }

    impl<'a, T> Iterator for ZeroCostIterator<'a, T> {
        type Item = &'a T;

        fn next(&mut self) -> Option<Self::Item> {
            if self.index < self.data.len() {
                let item = &self.data[self.index];
                self.index += 1;
                Some(item)
            } else {
                None
            }
        }
    }
}

/// 智能指针高级用法
pub mod smart_pointers {
    use super::*;

    /// 引用计数智能指针
    pub struct RefCounted<T> {
        data: *mut T,
        count: *mut AtomicUsize,
    }

    impl<T> RefCounted<T> {
        pub fn new(value: T) -> Self {
            unsafe {
                let data = System.alloc(Layout::new::<T>()) as *mut T;
                ptr::write(data, value);

                let count = System.alloc(Layout::new::<AtomicUsize>()) as *mut AtomicUsize;
                ptr::write(count, AtomicUsize::new(1));

                Self { data, count }
            }
        }

        #[allow(clippy::should_implement_trait)]
        pub fn clone(&self) -> Self {
            unsafe {
                (*self.count).fetch_add(1, Ordering::Relaxed);
                Self {
                    data: self.data,
                    count: self.count,
                }
            }
        }

        pub fn get(&self) -> &T {
            unsafe { &*self.data }
        }

        pub fn get_mut(&mut self) -> &mut T {
            unsafe { &mut *self.data }
        }
    }

    impl<T> Drop for RefCounted<T> {
        fn drop(&mut self) {
            unsafe {
                if (*self.count).fetch_sub(1, Ordering::Release) == 1 {
                    ptr::drop_in_place(self.data);
                    System.dealloc(self.data as *mut u8, Layout::new::<T>());
                    System.dealloc(self.count as *mut u8, Layout::new::<AtomicUsize>());
                }
            }
        }
    }

    /// 弱引用智能指针
    pub struct WeakRef<T> {
        data: *mut T,
        count: *mut AtomicUsize,
    }

    impl<T> WeakRef<T> {
        pub fn new(rc: &RefCounted<T>) -> Self {
            unsafe {
                (*rc.count).fetch_add(1, Ordering::Relaxed);
                Self {
                    data: rc.data,
                    count: rc.count,
                }
            }
        }

        pub fn upgrade(&self) -> Option<RefCounted<T>> {
            unsafe {
                if (*self.count).load(Ordering::Acquire) > 0 {
                    Some(RefCounted {
                        data: self.data,
                        count: self.count,
                    })
                } else {
                    None
                }
            }
        }
    }

    impl<T> Drop for WeakRef<T> {
        fn drop(&mut self) {
            unsafe {
                (*self.count).fetch_sub(1, Ordering::Release);
            }
        }
    }

    /// 自定义分配器
    pub struct CustomAllocator {
        pool: super::memory_layout::MemoryPool,
    }

    impl CustomAllocator {
        pub fn new(pool: super::memory_layout::MemoryPool) -> Self {
            Self { pool }
        }
    }

    unsafe impl GlobalAlloc for CustomAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            if layout.size() <= self.pool.block_size {
                self.pool.allocate().unwrap_or(ptr::null_mut())
            } else {
                unsafe { System.alloc(layout) }
            }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            if layout.size() <= self.pool.block_size {
                self.pool.deallocate(ptr);
            } else {
                unsafe { System.dealloc(ptr, layout) };
            }
        }
    }
}

/// 内存泄漏检测
pub mod memory_leak_detection {
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use std::time::Instant;

    /// 内存泄漏检测器
    #[allow(clippy::arc_with_non_send_sync)]
    pub struct MemoryLeakDetector {
        allocations: Arc<Mutex<HashMap<*mut u8, AllocationInfo>>>,
        total_allocated: AtomicUsize,
        total_deallocated: AtomicUsize,
    }

    #[derive(Debug, Clone)]
    pub struct AllocationInfo {
        pub size: usize,
        pub timestamp: Instant,
        pub stack_trace: Vec<String>,
    }

    #[allow(clippy::arc_with_non_send_sync)]
    impl Default for MemoryLeakDetector {
        fn default() -> Self {
            Self {
                allocations: Arc::new(Mutex::new(HashMap::new())),
                total_allocated: AtomicUsize::new(0),
                total_deallocated: AtomicUsize::new(0),
            }
        }
    }

    impl MemoryLeakDetector {
        pub fn new() -> Self {
            Self::default()
        }

        pub fn track_allocation(&self, ptr: *mut u8, size: usize) {
            let info = AllocationInfo {
                size,
                timestamp: Instant::now(),
                stack_trace: self.get_stack_trace(),
            };

            self.total_allocated.fetch_add(size, Ordering::Relaxed);

            let mut allocations = self.allocations.lock().expect("分配记录锁定失败");
            allocations.insert(ptr, info);
        }

        pub fn track_deallocation(&self, ptr: *mut u8) {
            let mut allocations = self.allocations.lock().expect("分配记录锁定失败");
            if let Some(info) = allocations.remove(&ptr) {
                self.total_deallocated
                    .fetch_add(info.size, Ordering::Relaxed);
            }
        }

        pub fn get_leaks(&self) -> Vec<AllocationInfo> {
            let allocations = self.allocations.lock().expect("分配记录锁定失败");
            allocations.values().cloned().collect()
        }

        pub fn get_memory_stats(&self) -> MemoryStats {
            MemoryStats {
                total_allocated: self.total_allocated.load(Ordering::Relaxed),
                total_deallocated: self.total_deallocated.load(Ordering::Relaxed),
                current_allocations: self.allocations.lock().expect("分配记录锁定失败").len(),
            }
        }

        fn get_stack_trace(&self) -> Vec<String> {
            // 在实际实现中，这里会收集真实的堆栈跟踪
            vec!["stack_trace_placeholder".to_string()]
        }
    }

    #[derive(Debug)]
    pub struct MemoryStats {
        pub total_allocated: usize,
        pub total_deallocated: usize,
        pub current_allocations: usize,
    }
}

/// 缓冲区溢出防护
pub mod buffer_overflow_protection {

    /// 安全缓冲区
    pub struct SafeBuffer {
        data: Vec<u8>,
        size: usize,
        canary: u64,
    }

    impl SafeBuffer {
        const CANARY_VALUE: u64 = 0xDEADBEEFCAFEBABE;

        pub fn new(size: usize) -> Self {
            let mut data = vec![0u8; size];
            let canary = Self::CANARY_VALUE;

            // 在缓冲区末尾放置金丝雀值
            let canary_bytes = canary.to_le_bytes();
            let data_len = data.len();
            for (i, &byte) in canary_bytes.iter().enumerate() {
                if i < data_len {
                    data[data_len - 1 - i] = byte;
                }
            }

            Self { data, size, canary }
        }

        pub fn write(&mut self, offset: usize, data: &[u8]) -> Result<(), BufferError> {
            if offset + data.len() > self.size {
                return Err(BufferError::Overflow);
            }

            if !self.check_canary() {
                return Err(BufferError::Corruption);
            }

            self.data[offset..offset + data.len()].copy_from_slice(data);
            Ok(())
        }

        pub fn read(&self, offset: usize, len: usize) -> Result<&[u8], BufferError> {
            if offset + len > self.size {
                return Err(BufferError::Overflow);
            }

            if !self.check_canary() {
                return Err(BufferError::Corruption);
            }

            Ok(&self.data[offset..offset + len])
        }

        fn check_canary(&self) -> bool {
            if self.data.len() < 8 {
                return true;
            }

            let canary_bytes = &self.data[self.data.len() - 8..];
            let stored_canary = u64::from_le_bytes([
                canary_bytes[0],
                canary_bytes[1],
                canary_bytes[2],
                canary_bytes[3],
                canary_bytes[4],
                canary_bytes[5],
                canary_bytes[6],
                canary_bytes[7],
            ]);

            stored_canary == self.canary
        }
    }

    #[derive(Debug, Clone)]
    pub enum BufferError {
        Overflow,
        Corruption,
    }

    impl std::fmt::Display for BufferError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BufferError::Overflow => write!(f, "Buffer overflow detected"),
                BufferError::Corruption => write!(f, "Buffer corruption detected"),
            }
        }
    }

    impl std::error::Error for BufferError {}

    /// 边界检查工具
    pub struct BoundsChecker;

    impl BoundsChecker {
        pub fn check_bounds<T>(slice: &[T], index: usize) -> Result<(), BoundsError> {
            if index >= slice.len() {
                Err(BoundsError::OutOfBounds {
                    index,
                    len: slice.len(),
                })
            } else {
                Ok(())
            }
        }

        pub fn safe_get<T>(slice: &[T], index: usize) -> Result<&T, BoundsError> {
            Self::check_bounds(slice, index)?;
            Ok(&slice[index])
        }

        pub fn safe_get_mut<T>(slice: &mut [T], index: usize) -> Result<&mut T, BoundsError> {
            if index >= slice.len() {
                return Err(BoundsError::OutOfBounds {
                    index,
                    len: slice.len(),
                });
            }
            Ok(&mut slice[index])
        }
    }

    #[derive(Debug, Clone)]
    pub enum BoundsError {
        OutOfBounds { index: usize, len: usize },
    }

    impl std::fmt::Display for BoundsError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BoundsError::OutOfBounds { index, len } => {
                    write!(
                        f,
                        "Index {} out of bounds for slice of length {}",
                        index, len
                    )
                }
            }
        }
    }

    impl std::error::Error for BoundsError {}
}

/// 内存对齐和缓存优化
pub mod memory_alignment_cache {

    /// 缓存友好的数据结构
    #[repr(align(64))]
    #[derive(Default)]
    pub struct CacheFriendlyStruct {
        pub hot_data: [u64; 8],  // 热数据，经常访问
        pub cold_data: [u8; 32], // 冷数据，很少访问
    }

    impl CacheFriendlyStruct {
        pub fn new() -> Self {
            Self::default()
        }

        pub fn update_hot_data(&mut self, index: usize, value: u64) {
            if index < self.hot_data.len() {
                self.hot_data[index] = value;
            }
        }

        pub fn get_hot_data(&self, index: usize) -> Option<u64> {
            self.hot_data.get(index).copied()
        }
    }

    /// 内存预取工具
    pub struct MemoryPrefetcher;

    impl MemoryPrefetcher {
        pub fn prefetch_read<T>(ptr: *const T) {
            unsafe {
                #[cfg(target_arch = "x86_64")]
                {
                    use std::arch::x86_64::_mm_prefetch;
                    _mm_prefetch(ptr as *const i8, 0); // _MM_HINT_T0
                }
            }
        }

        pub fn prefetch_write<T>(ptr: *const T) {
            unsafe {
                #[cfg(target_arch = "x86_64")]
                {
                    use std::arch::x86_64::_mm_prefetch;
                    _mm_prefetch(ptr as *const i8, 1); // _MM_HINT_T1
                }
            }
        }
    }

    /// 内存访问模式优化
    pub struct MemoryAccessOptimizer;

    impl MemoryAccessOptimizer {
        /// 顺序访问模式
        pub fn sequential_access<T>(data: &[T], mut f: impl FnMut(&T)) {
            for item in data {
                f(item);
            }
        }

        /// 随机访问模式
        pub fn random_access<T>(data: &[T], indices: &[usize], mut f: impl FnMut(&T)) {
            for &index in indices {
                if let Some(item) = data.get(index) {
                    f(item);
                }
            }
        }

        /// 分块访问模式
        pub fn blocked_access<T>(data: &[T], block_size: usize, mut f: impl FnMut(&[T])) {
            for chunk in data.chunks(block_size) {
                f(chunk);
            }
        }
    }
}

/// 主演示函数
pub fn demonstrate_memory_safety_advanced() {
    println!("🛡️  Rust 1.90 内存安全高级演示");
    println!("=================================");

    // 1. 高级生命周期管理演示
    println!("\n=== 高级生命周期管理演示 ===");
    let data = 42i32;
    let tracker = advanced_lifetimes::LifetimeTracker::new(&data, 1);
    println!(
        "生命周期追踪器 ID: {}, 年龄: {:?}",
        tracker.tracker_id(),
        tracker.age()
    );

    let long_lived = "长期数据".to_string();
    let combinator = advanced_lifetimes::LifetimeCombinator::new(&data, &long_lived);
    let result = combinator.combine(|short, long| format!("{} + {}", short, long));
    println!("生命周期组合结果: {}", result);

    // 2. 内存布局优化演示
    println!("\n=== 内存布局优化演示 ===");
    let aligned_data = memory_layout::CacheAligned::new(42u64);
    println!("缓存对齐数据: {}", aligned_data.get());

    let memory_pool = memory_layout::MemoryPool::new(1024, 10);
    println!("内存池可用块数: {}", memory_pool.available_blocks());

    // 3. 零成本抽象演示
    println!("\n=== 零成本抽象演示 ===");
    let wrapper = zero_cost_abstractions::ZeroCostWrapper::new(100);
    println!("零成本包装器值: {}", wrapper.get());

    const FACTORIAL_5: u32 = zero_cost_abstractions::compile_time_factorial(5);
    println!("编译时计算 5!: {}", FACTORIAL_5);

    // 4. 智能指针演示
    println!("\n=== 智能指针演示 ===");
    let rc = smart_pointers::RefCounted::new(200);
    let rc2 = rc.clone();
    println!("引用计数智能指针值: {}", rc.get());
    println!("克隆后值: {}", rc2.get());

    // 5. 内存泄漏检测演示
    println!("\n=== 内存泄漏检测演示 ===");
    let detector = memory_leak_detection::MemoryLeakDetector::new();
    let stats = detector.get_memory_stats();
    println!(
        "内存统计: 总分配={}, 总释放={}, 当前分配={}",
        stats.total_allocated, stats.total_deallocated, stats.current_allocations
    );

    // 6. 缓冲区溢出防护演示
    println!("\n=== 缓冲区溢出防护演示 ===");
    let mut safe_buffer = buffer_overflow_protection::SafeBuffer::new(100);
    match safe_buffer.write(0, b"Hello, World!") {
        Ok(_) => println!("安全写入成功"),
        Err(e) => println!("写入失败: {}", e),
    }

    match safe_buffer.read(0, 13) {
        Ok(data) => println!("安全读取: {}", String::from_utf8_lossy(data)),
        Err(e) => println!("读取失败: {}", e),
    }

    // 7. 内存对齐和缓存优化演示
    println!("\n=== 内存对齐和缓存优化演示 ===");
    let mut cache_friendly = memory_alignment_cache::CacheFriendlyStruct::new();
    cache_friendly.update_hot_data(0, 123);
    println!("缓存友好结构热数据: {:?}", cache_friendly.hot_data);

    let data_array = vec![1, 2, 3, 4, 5];
    memory_alignment_cache::MemoryAccessOptimizer::sequential_access(&data_array, |x| {
        println!("顺序访问: {}", x);
    });

    println!("\n✅ 内存安全高级演示完成！");
}
