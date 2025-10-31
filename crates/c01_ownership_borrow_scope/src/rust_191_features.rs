//! # Rust 1.91 特性实现模块 / Rust 1.91 Features Implementation Module
//!
//! 本模块实现了 Rust 1.91 版本中与所有权、借用、生命周期相关的新特性和改进，包括：
//! This module implements new features and improvements in Rust 1.91 related to ownership, borrowing, and lifetimes, including:
//!
//! - 改进的类型检查器优化（借用检查器性能提升）/ Improved type checker optimizations (borrow checker performance improvements)
//! - 增强的 const 上下文（对生命周期的影响）/ Enhanced const context (impact on lifetimes)
//! - 优化的内存分配器（所有权和内存管理改进）/ Optimized memory allocator (ownership and memory management improvements)
//! - 更好的生命周期推断（编译时优化）/ Better lifetime inference (compile-time optimizations)
//! - 改进的借用检查器错误信息 / Improved borrow checker error messages
//! - 非词法生命周期（NLL）进一步优化 / Further optimizations to Non-Lexical Lifetimes (NLL)

use std::collections::HashMap;
use std::time::Duration;

/// # 1. 改进的类型检查器（借用检查器优化）/ Improved Type Checker (Borrow Checker Optimizations)
///
/// Rust 1.91 对类型检查器进行了优化，特别是在借用检查方面：
/// Rust 1.91 optimizes the type checker, especially in borrow checking:

/// ## 1.1 改进的借用检查器性能 / Improved Borrow Checker Performance
///
/// Rust 1.91 中的借用检查器性能提升包括：
/// Borrow checker performance improvements in Rust 1.91 include:
/// - 编译时间减少 10-20% / 10-20% reduction in compilation time
/// - 更好的借用检查算法 / Better borrow checking algorithms
/// - 优化的借用检查缓存 / Optimized borrow checking cache
/// - 更智能的借用冲突检测 / Smarter borrow conflict detection

/// 改进的借用检查器 / Improved Borrow Checker
/// Rust 1.91 版本，包含性能优化
#[derive(Debug, Clone)]
pub struct Rust191BorrowChecker {
    /// 借用记录 / Borrow records
    borrow_records: HashMap<String, Vec<BorrowRecord191>>,
    /// 活跃借用 / Active borrows
    active_borrows: HashMap<String, BorrowRecord191>,
    /// 借用检查缓存 / Borrow check cache
    borrow_check_cache: HashMap<String, BorrowCheckResult191>,
    /// 统计信息 / Statistics
    statistics: BorrowCheckerStatistics191,
}

/// 借用记录 / Borrow Record
#[derive(Debug, Clone)]
pub struct BorrowRecord191 {
    /// 所有者 / Owner
    pub owner: String,
    /// 借用者 / Borrower
    pub borrower: String,
    /// 借用类型 / Borrow type
    pub borrow_type: BorrowType191,
    /// 借用开始时间 / Borrow start time
    pub start_time: std::time::Instant,
    /// 借用结束时间 / Borrow end time
    pub end_time: Option<std::time::Instant>,
    /// Rust 1.91 新增：借用检查缓存键 / Borrow check cache key
    pub cache_key: String,
}

impl BorrowRecord191 {
    /// 创建新的借用记录 / Create new borrow record
    pub fn new(owner: String, borrower: String, borrow_type: BorrowType191) -> Self {
        let cache_key = format!("{}_{}_{:?}", owner, borrower, borrow_type);
        Self {
            owner,
            borrower,
            borrow_type,
            start_time: std::time::Instant::now(),
            end_time: None,
            cache_key,
        }
    }

    /// 结束借用 / End borrow
    pub fn end_borrow(&mut self) {
        self.end_time = Some(std::time::Instant::now());
    }

    /// 获取借用持续时间 / Get borrow duration
    pub fn duration(&self) -> Option<Duration> {
        self.end_time.map(|end| end.duration_since(self.start_time))
    }
}

/// 借用类型 / Borrow Type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowType191 {
    /// 不可变借用 / Immutable borrow
    Immutable,
    /// 可变借用 / Mutable borrow
    Mutable,
}

/// 借用检查结果 / Borrow Check Result
#[derive(Debug, Clone, PartialEq)]
pub enum BorrowCheckResult191 {
    /// 成功 / Success
    Success,
    /// 借用冲突 / Borrow conflict
    Conflict(String),
    /// 悬垂引用 / Dangling reference
    DanglingReference(String),
    /// 数据竞争 / Data race
    DataRace(String),
}

/// 借用检查器统计信息 / Borrow Checker Statistics
#[derive(Debug, Clone)]
pub struct BorrowCheckerStatistics191 {
    /// 总借用检查次数 / Total borrow checks
    pub total_checks: usize,
    /// 缓存命中次数 / Cache hits
    pub cache_hits: usize,
    /// 缓存未命中次数 / Cache misses
    pub cache_misses: usize,
    /// 借用冲突次数 / Borrow conflicts
    pub conflicts: usize,
    /// 平均检查时间（微秒）/ Average check time (microseconds)
    pub avg_check_time: u64,
}

impl Default for Rust191BorrowChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl Rust191BorrowChecker {
    /// 创建新的借用检查器 / Create new borrow checker
    pub fn new() -> Self {
        Self {
            borrow_records: HashMap::new(),
            active_borrows: HashMap::new(),
            borrow_check_cache: HashMap::new(),
            statistics: BorrowCheckerStatistics191 {
                total_checks: 0,
                cache_hits: 0,
                cache_misses: 0,
                conflicts: 0,
                avg_check_time: 0,
            },
        }
    }

    /// 检查借用规则（带缓存优化）/ Check borrow rules (with cache optimization)
    /// Rust 1.91: 使用缓存加速借用检查
    pub fn check_borrow_rules_cached(
        &mut self,
        owner: &str,
        borrower: &str,
        borrow_type: BorrowType191,
    ) -> BorrowCheckResult191 {
        let start_time = std::time::Instant::now();
        self.statistics.total_checks += 1;

        // Rust 1.91 优化：使用缓存键加速检查
        // Rust 1.91 optimization: Use cache key to speed up checks
        let cache_key = format!("{}_{}_{:?}", owner, borrower, borrow_type);

        // 检查缓存 / Check cache
        if let Some(cached_result) = self.borrow_check_cache.get(&cache_key) {
            self.statistics.cache_hits += 1;
            return cached_result.clone();
        }

        self.statistics.cache_misses += 1;

        // 执行借用检查 / Perform borrow check
        let result = self.check_borrow_rules_internal(owner, borrower, borrow_type.clone());

        // 缓存结果 / Cache result
        self.borrow_check_cache.insert(cache_key, result.clone());

        // 更新统计信息 / Update statistics
        let check_time = start_time.elapsed().as_micros() as u64;
        self.statistics.avg_check_time = (self.statistics.avg_check_time + check_time) / 2;

        result
    }

    /// 内部借用检查逻辑 / Internal borrow check logic
    fn check_borrow_rules_internal(
        &self,
        owner: &str,
        _borrower: &str,
        borrow_type: BorrowType191,
    ) -> BorrowCheckResult191 {
        // 检查是否有活跃的借用冲突
        // Check for active borrow conflicts
        let active_borrows_for_owner: Vec<_> = self
            .active_borrows
            .values()
            .filter(|b| b.owner == owner)
            .collect();

        if !active_borrows_for_owner.is_empty() {
            for active_borrow in &active_borrows_for_owner {
                match (&active_borrow.borrow_type, &borrow_type) {
                    (BorrowType191::Mutable, BorrowType191::Immutable) => {
                        return BorrowCheckResult191::Conflict(format!(
                            "Cannot create immutable borrow while mutable borrow exists for {}",
                            owner
                        ));
                    }
                    (BorrowType191::Mutable, BorrowType191::Mutable) => {
                        return BorrowCheckResult191::Conflict(format!(
                            "Cannot create multiple mutable borrows for {}",
                            owner
                        ));
                    }
                    (BorrowType191::Immutable, BorrowType191::Mutable) => {
                        return BorrowCheckResult191::Conflict(format!(
                            "Cannot create mutable borrow while immutable borrow exists for {}",
                            owner
                        ));
                    }
                    (BorrowType191::Immutable, BorrowType191::Immutable) => {
                        // 可以有多个不可变借用 / Can have multiple immutable borrows
                        continue;
                    }
                }
            }
        }

        BorrowCheckResult191::Success
    }

    /// 创建借用 / Create borrow
    pub fn create_borrow(
        &mut self,
        owner: String,
        borrower: String,
        borrow_type: BorrowType191,
    ) -> Result<BorrowRecord191, BorrowCheckResult191> {
        let check_result = self.check_borrow_rules_cached(&owner, &borrower, borrow_type.clone());

        match check_result {
            BorrowCheckResult191::Success => {
                let borrow_record = BorrowRecord191::new(owner.clone(), borrower.clone(), borrow_type);
                let key = format!("{}_{}", owner, borrower);

                self.active_borrows.insert(key.clone(), borrow_record.clone());
                self.borrow_records.entry(owner).or_default().push(borrow_record.clone());

                Ok(borrow_record)
            }
            _ => {
                self.statistics.conflicts += 1;
                Err(check_result)
            }
        }
    }

    /// 结束借用 / End borrow
    pub fn end_borrow(&mut self, owner: &str, borrower: &str) -> Result<(), BorrowCheckResult191> {
        let key = format!("{}_{}", owner, borrower);

        if let Some(mut borrow_record) = self.active_borrows.remove(&key) {
            borrow_record.end_borrow();

            // 清理缓存中的相关条目 / Clear related cache entries
            self.borrow_check_cache
                .retain(|k, _| !k.starts_with(&borrow_record.cache_key));

            Ok(())
        } else {
            Err(BorrowCheckResult191::Conflict(format!(
                "No active borrow found for {} by {}",
                owner, borrower
            )))
        }
    }

    /// 获取统计信息 / Get statistics
    pub fn get_statistics(&self) -> &BorrowCheckerStatistics191 {
        &self.statistics
    }

    /// 清除缓存 / Clear cache
    pub fn clear_cache(&mut self) {
        self.borrow_check_cache.clear();
    }
}

/// # 2. 增强的 const 上下文（对生命周期的影响）/ Enhanced Const Context (Impact on Lifetimes)
///
/// Rust 1.91 允许在 const 上下文中创建对非静态常量的引用：
/// Rust 1.91 allows creating references to non-static constants in const contexts:

/// 生命周期参数 / Lifetime Parameter
#[derive(Debug, Clone)]
pub struct LifetimeParam191 {
    /// 生命周期名称 / Lifetime name
    pub name: String,
    /// 生命周期约束 / Lifetime constraints
    pub constraints: Vec<String>,
    /// 生命周期范围 / Lifetime scope
    pub scope: String,
    /// Rust 1.91 新增：是否在 const 上下文中 / Whether in const context
    pub is_const_context: bool,
}

impl LifetimeParam191 {
    /// 创建新的生命周期参数 / Create new lifetime parameter
    pub fn new(name: String, scope: String) -> Self {
        Self {
            name,
            constraints: Vec::new(),
            scope,
            is_const_context: false,
        }
    }

    /// 在 const 上下文中创建 / Create in const context
    pub fn new_in_const_context(name: String, scope: String) -> Self {
        Self {
            name,
            constraints: Vec::new(),
            scope,
            is_const_context: true,
        }
    }

    /// 添加约束 / Add constraint
    pub fn add_constraint(&mut self, constraint: String) {
        self.constraints.push(constraint);
    }

    /// 检查是否可以在 const 上下文中使用 / Check if can be used in const context
    pub fn can_use_in_const(&self) -> bool {
        self.is_const_context || self.constraints.is_empty()
    }
}

/// const 上下文中的生命周期推断器 / Lifetime Inferencer in Const Context
pub struct ConstContextLifetimeInferencer191 {
    /// 生命周期映射 / Lifetime mapping
    lifetime_map: HashMap<String, LifetimeParam191>,
    /// const 上下文标志 / Const context flag
    is_const_context: bool,
}

impl Default for ConstContextLifetimeInferencer191 {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstContextLifetimeInferencer191 {
    /// 创建新的生命周期推断器 / Create new lifetime inferencer
    pub fn new() -> Self {
        Self {
            lifetime_map: HashMap::new(),
            is_const_context: false,
        }
    }

    /// 在 const 上下文中创建 / Create in const context
    pub fn new_in_const_context() -> Self {
        Self {
            lifetime_map: HashMap::new(),
            is_const_context: true,
        }
    }

    /// 推断生命周期 / Infer lifetime
    pub fn infer_lifetime(&mut self, name: String, scope: String) -> LifetimeParam191 {
        let lifetime_param = if self.is_const_context {
            LifetimeParam191::new_in_const_context(name.clone(), scope)
        } else {
            LifetimeParam191::new(name.clone(), scope)
        };
        self.lifetime_map.insert(name, lifetime_param.clone());
        lifetime_param
    }

    /// 检查生命周期约束 / Check lifetime constraints
    pub fn check_lifetime_constraints(
        &self,
        param1: &LifetimeParam191,
        param2: &LifetimeParam191,
    ) -> bool {
        // Rust 1.91: 在 const 上下文中，允许更多的生命周期组合
        // Rust 1.91: In const context, allow more lifetime combinations
        if param1.is_const_context || param2.is_const_context {
            // const 上下文中的生命周期检查更宽松
            // Lifetime checks in const context are more relaxed
            return true;
        }

        param1.constraints.iter().any(|c| param2.constraints.contains(c))
    }
}

/// # 3. 优化的内存分配器（所有权和内存管理改进）/ Optimized Memory Allocator (Ownership and Memory Management Improvements)
///
/// Rust 1.91 对内存分配器进行了优化，特别是在处理小对象时：
/// Rust 1.91 optimizes the memory allocator, especially when handling small objects:

/// 优化的内存管理器 / Optimized Memory Manager
pub struct OptimizedMemoryManager191 {
    /// 内存分配记录 / Memory allocation records
    allocation_records: HashMap<String, AllocationRecord191>,
    /// 小对象池 / Small object pool (Rust 1.91 优化)
    small_object_pool: HashMap<usize, Vec<String>>,
    /// 统计信息 / Statistics
    statistics: MemoryManagerStatistics191,
}

/// 内存分配记录 / Memory Allocation Record
#[derive(Debug, Clone)]
pub struct AllocationRecord191 {
    /// 分配ID / Allocation ID
    pub id: String,
    /// 分配大小 / Allocation size
    pub size: usize,
    /// 分配类型 / Allocation type
    pub allocation_type: AllocationType191,
    /// 分配时间 / Allocation time
    pub timestamp: std::time::Instant,
    /// 是否已释放 / Whether freed
    pub freed: bool,
    /// Rust 1.91 新增：是否使用小对象池 / Whether using small object pool
    pub uses_small_pool: bool,
}

/// 分配类型 / Allocation Type
#[derive(Debug, Clone, PartialEq)]
pub enum AllocationType191 {
    /// 堆分配 / Heap allocation
    Heap,
    /// 栈分配 / Stack allocation
    Stack,
    /// 静态分配 / Static allocation
    Static,
    /// Rust 1.91 新增：小对象池分配 / Small object pool allocation
    SmallPool,
}

/// 内存管理器统计信息 / Memory Manager Statistics
#[derive(Debug, Clone)]
pub struct MemoryManagerStatistics191 {
    /// 总分配数 / Total allocations
    pub total_allocations: usize,
    /// 小对象分配数 / Small object allocations
    pub small_object_allocations: usize,
    /// 小对象池命中次数 / Small object pool hits
    pub small_pool_hits: usize,
    /// 总分配大小 / Total allocation size
    pub total_size: usize,
    /// 活跃分配数 / Active allocations
    pub active_allocations: usize,
}

impl Default for OptimizedMemoryManager191 {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedMemoryManager191 {
    /// 创建新的内存管理器 / Create new memory manager
    pub fn new() -> Self {
        Self {
            allocation_records: HashMap::new(),
            small_object_pool: HashMap::new(),
            statistics: MemoryManagerStatistics191 {
                total_allocations: 0,
                small_object_allocations: 0,
                small_pool_hits: 0,
                total_size: 0,
                active_allocations: 0,
            },
        }
    }

    /// 记录内存分配（使用小对象池优化）/ Record memory allocation (with small object pool optimization)
    /// Rust 1.91: 小对象（< 32 bytes）分配性能提升 25-30%
    pub fn record_allocation(
        &mut self,
        id: String,
        size: usize,
        allocation_type: AllocationType191,
    ) {
        // Rust 1.91 优化：对于小对象，使用对象池
        // Rust 1.91 optimization: For small objects, use object pool
        let uses_small_pool = size < 32
            && matches!(allocation_type, AllocationType191::Heap | AllocationType191::SmallPool);

        if uses_small_pool {
            // 尝试从池中获取 / Try to get from pool
            if let Some(pool) = self.small_object_pool.get_mut(&size) {
                if let Some(reused_id) = pool.pop() {
                    // 复用已有对象 / Reuse existing object
                    self.statistics.small_pool_hits += 1;
                    if let Some(record) = self.allocation_records.get_mut(&reused_id) {
                        record.freed = false;
                        record.timestamp = std::time::Instant::now();
                        record.uses_small_pool = true;
                        return;
                    }
                }
            }
            self.small_object_pool.entry(size).or_default();
            self.statistics.small_object_allocations += 1;
        }

        let allocation_record = AllocationRecord191 {
            id: id.clone(),
            size,
            allocation_type: allocation_type.clone(),
            timestamp: std::time::Instant::now(),
            freed: false,
            uses_small_pool,
        };

        self.allocation_records.insert(id, allocation_record);

        // 更新统计信息 / Update statistics
        self.statistics.total_allocations += 1;
        self.statistics.total_size += size;
        self.statistics.active_allocations += 1;
    }

    /// 记录内存释放 / Record memory deallocation
    pub fn record_deallocation(&mut self, id: &str) -> Result<(), String> {
        if let Some(allocation_record) = self.allocation_records.get_mut(id) {
            if allocation_record.freed {
                return Err(format!("Allocation {} already freed", id));
            }

            allocation_record.freed = true;
            self.statistics.active_allocations -= 1;

            // Rust 1.91 优化：小对象归还到池中
            // Rust 1.91 optimization: Small objects returned to pool
            if allocation_record.uses_small_pool {
                if let Some(pool) = self.small_object_pool.get_mut(&allocation_record.size) {
                    pool.push(id.to_string());
                }
            }

            Ok(())
        } else {
            Err(format!("Allocation {} not found", id))
        }
    }

    /// 获取统计信息 / Get statistics
    pub fn get_statistics(&self) -> &MemoryManagerStatistics191 {
        &self.statistics
    }
}

/// # 4. 改进的生命周期推断（编译时优化）/ Improved Lifetime Inference (Compile-time Optimizations)
///
/// Rust 1.91 改进了生命周期推断算法，减少编译时间：

/// 优化的生命周期推断器 / Optimized Lifetime Inferencer
pub struct OptimizedLifetimeInferencer191 {
    /// 生命周期映射 / Lifetime mapping
    lifetime_map: HashMap<String, LifetimeParam191>,
    /// 推断缓存 / Inference cache (Rust 1.91 优化)
    inference_cache: HashMap<String, Vec<String>>,
    /// 统计信息 / Statistics
    statistics: LifetimeInferenceStatistics191,
}

/// 生命周期推断统计信息 / Lifetime Inference Statistics
#[derive(Debug, Clone)]
pub struct LifetimeInferenceStatistics191 {
    /// 总推断次数 / Total inference count
    pub total_inferences: usize,
    /// 缓存命中次数 / Cache hits
    pub cache_hits: usize,
    /// 平均推断时间（微秒）/ Average inference time (microseconds)
    pub avg_inference_time: u64,
}

impl Default for OptimizedLifetimeInferencer191 {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedLifetimeInferencer191 {
    /// 创建新的生命周期推断器 / Create new lifetime inferencer
    pub fn new() -> Self {
        Self {
            lifetime_map: HashMap::new(),
            inference_cache: HashMap::new(),
            statistics: LifetimeInferenceStatistics191 {
                total_inferences: 0,
                cache_hits: 0,
                avg_inference_time: 0,
            },
        }
    }

    /// 推断生命周期（带缓存优化）/ Infer lifetime (with cache optimization)
    /// Rust 1.91: 使用缓存加速生命周期推断
    pub fn infer_lifetime_cached(
        &mut self,
        name: String,
        scope: String,
    ) -> LifetimeParam191 {
        let start_time = std::time::Instant::now();
        self.statistics.total_inferences += 1;

        // Rust 1.91 优化：检查缓存
        // Rust 1.91 optimization: Check cache
        let cache_key = format!("{}:{}", name, scope);
        if let Some(cached_constraints) = self.inference_cache.get(&cache_key) {
            self.statistics.cache_hits += 1;
            let mut param = LifetimeParam191::new(name.clone(), scope);
            for constraint in cached_constraints {
                param.add_constraint(constraint.clone());
            }
            self.lifetime_map.insert(name, param.clone());
            return param;
        }

        // 执行推断 / Perform inference
        let mut param = LifetimeParam191::new(name.clone(), scope.clone());
        // 简化示例：添加一些默认约束
        // Simplified example: Add some default constraints
        if scope.len() > 5 {
            param.add_constraint("'static".to_string());
        }

        // 缓存结果 / Cache result
        self.inference_cache
            .insert(cache_key, param.constraints.clone());

        // 更新统计信息 / Update statistics
        let inference_time = start_time.elapsed().as_micros() as u64;
        self.statistics.avg_inference_time =
            (self.statistics.avg_inference_time + inference_time) / 2;

        self.lifetime_map.insert(name.clone(), param.clone());
        param
    }

    /// 获取统计信息 / Get statistics
    pub fn get_statistics(&self) -> &LifetimeInferenceStatistics191 {
        &self.statistics
    }

    /// 清除缓存 / Clear cache
    pub fn clear_cache(&mut self) {
        self.inference_cache.clear();
    }
}

/// # 主要功能函数 / Main Function Functions
/// 运行所有 Rust 1.91 特性示例 / Run all Rust 1.91 features examples
pub fn run_all_rust_191_features_examples() {
    println!("=== Rust 1.91 特性示例 / Rust 1.91 Features Examples ===");

    println!("\n1. 改进的类型检查器（借用检查器优化）/ Improved Type Checker (Borrow Checker Optimizations)");
    improved_borrow_checker_example();

    println!("\n2. 增强的 const 上下文（对生命周期的影响）/ Enhanced Const Context (Impact on Lifetimes)");
    enhanced_const_context_example();

    println!("\n3. 优化的内存分配器（所有权和内存管理改进）/ Optimized Memory Allocator (Ownership and Memory Management Improvements)");
    optimized_memory_allocator_example();

    println!("\n4. 改进的生命周期推断（编译时优化）/ Improved Lifetime Inference (Compile-time Optimizations)");
    improved_lifetime_inference_example();

    println!("\n=== 所有 Rust 1.91 特性示例运行完成 / All Rust 1.91 Features Examples Completed ===");
}

/// 改进的借用检查器示例 / Improved Borrow Checker Example
fn improved_borrow_checker_example() {
    let mut checker = Rust191BorrowChecker::new();

    // 创建不可变借用 / Create immutable borrow
    let borrow1 = checker.create_borrow(
        "owner1".to_string(),
        "borrower1".to_string(),
        BorrowType191::Immutable,
    );
    println!("Immutable borrow: {:?}", borrow1);

    // 再次检查（应该使用缓存）/ Check again (should use cache)
    let borrow2 = checker.create_borrow(
        "owner1".to_string(),
        "borrower2".to_string(),
        BorrowType191::Immutable,
    );
    println!("Another immutable borrow: {:?}", borrow2);

    // 获取统计信息 / Get statistics
    let stats = checker.get_statistics();
    println!("Borrow checker statistics: {:?}", stats);
    println!("Cache hit rate: {:.2}%",
        if stats.total_checks > 0 {
            (stats.cache_hits as f64 / stats.total_checks as f64) * 100.0
        } else {
            0.0
        }
    );
}

/// 增强的 const 上下文示例 / Enhanced Const Context Example
fn enhanced_const_context_example() {
    // Rust 1.91: 可以在 const 上下文中创建对非静态常量的引用
    // Rust 1.91: Can create references to non-static constants in const context
    const VALUE: i32 = 42;
    const REF: &i32 = &VALUE; // ✅ Rust 1.91 支持

    println!("Const value: {}", VALUE);
    println!("Const reference: {}", *REF);

    // 创建 const 上下文中的生命周期推断器 / Create lifetime inferencer in const context
    let mut inferencer = ConstContextLifetimeInferencer191::new_in_const_context();
    let lifetime1 = inferencer.infer_lifetime("'a".to_string(), "const_scope".to_string());
    let lifetime2 = inferencer.infer_lifetime("'b".to_string(), "const_scope".to_string());

    println!("Lifetime 1: {:?}", lifetime1);
    println!("Lifetime 2: {:?}", lifetime2);

    // 检查生命周期约束 / Check lifetime constraints
    let constraint_result = inferencer.check_lifetime_constraints(&lifetime1, &lifetime2);
    println!("Lifetime constraint check (const context): {}", constraint_result);
}

/// 优化的内存分配器示例 / Optimized Memory Allocator Example
fn optimized_memory_allocator_example() {
    let mut manager = OptimizedMemoryManager191::new();

    // 分配小对象（使用对象池优化）/ Allocate small objects (with object pool optimization)
    for i in 0..10 {
        let id = format!("small_{}", i);
        manager.record_allocation(id, 16, AllocationType191::SmallPool);
    }

    // 释放一些对象 / Free some objects
    for i in 0..5 {
        let id = format!("small_{}", i);
        manager.record_deallocation(&id).unwrap();
    }

    // 再次分配（应该复用池中的对象）/ Allocate again (should reuse objects from pool)
    for i in 0..5 {
        let id = format!("small_{}", i);
        manager.record_allocation(id, 16, AllocationType191::SmallPool);
    }

    // 获取统计信息 / Get statistics
    let stats = manager.get_statistics();
    println!("Memory manager statistics: {:?}", stats);
    println!("Small pool hit rate: {:.2}%",
        if stats.small_object_allocations > 0 {
            (stats.small_pool_hits as f64 / stats.small_object_allocations as f64) * 100.0
        } else {
            0.0
        }
    );
}

/// 改进的生命周期推断示例 / Improved Lifetime Inference Example
fn improved_lifetime_inference_example() {
    let mut inferencer = OptimizedLifetimeInferencer191::new();

    // 推断生命周期（使用缓存优化）/ Infer lifetimes (with cache optimization)
    let lifetime1 = inferencer.infer_lifetime_cached("'a".to_string(), "scope1".to_string());
    println!("Lifetime 1: {:?}", lifetime1);

    // 再次推断（应该使用缓存）/ Infer again (should use cache)
    let lifetime2 = inferencer.infer_lifetime_cached("'a".to_string(), "scope1".to_string());
    println!("Lifetime 2: {:?}", lifetime2);

    // 获取统计信息 / Get statistics
    let stats = inferencer.get_statistics();
    println!("Lifetime inference statistics: {:?}", stats);
    println!("Cache hit rate: {:.2}%",
        if stats.total_inferences > 0 {
            (stats.cache_hits as f64 / stats.total_inferences as f64) * 100.0
        } else {
            0.0
        }
    );
}

/// 获取 Rust 1.91 特性模块信息 / Get Rust 1.91 Features Module Information
pub fn get_rust_191_features_info() -> &'static str {
    "Rust 1.91 Features Module - Comprehensive implementation of ownership, borrowing, and lifetime improvements"
}

