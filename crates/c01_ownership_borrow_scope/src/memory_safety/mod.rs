//! # Rust 1.89 内存安全系统模块 / Rust 1.89 Memory Safety System Module
//!
//! 本模块实现了 Rust 1.89 版本的最新内存安全系统特性，包括：
//! This module implements the latest memory safety system features of Rust 1.89, including:
//!
//! - 编译时内存安全检查 / Compile-time Memory Safety Checks
//! - 运行时内存安全验证 / Runtime Memory Safety Verification
//! - 数据竞争检测 / Data Race Detection
//! - 悬垂引用防护 / Dangling Reference Protection
//! - 内存泄漏检测 / Memory Leak Detection
//! - 缓冲区溢出防护 / Buffer Overflow Protection

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 内存安全管理器 / Memory Safety Manager
/// 
/// 统一管理所有内存安全相关的检查和验证
/// Unified management of all memory safety related checks and verifications
pub struct MemorySafetyManager {
    /// 内存分配跟踪器 / Memory Allocation Tracker
    allocation_tracker: Arc<Mutex<MemoryAllocationTracker>>,
    /// 引用有效性检查器 / Reference Validity Checker
    reference_checker: Arc<Mutex<ReferenceValidityChecker>>,
    /// 数据竞争检测器 / Data Race Detector
    data_race_detector: Arc<Mutex<DataRaceDetector>>,
    /// 内存泄漏检测器 / Memory Leak Detector
    memory_leak_detector: Arc<Mutex<MemoryLeakDetector>>,
    /// 缓冲区安全检查器 / Buffer Safety Checker
    buffer_safety_checker: Arc<Mutex<BufferSafetyChecker>>,
    /// 安全统计信息 / Safety Statistics
    statistics: Arc<Mutex<MemorySafetyStatistics>>,
}

impl MemorySafetyManager {
    /// 创建新的内存安全管理器 / Create New Memory Safety Manager
    pub fn new() -> Self {
        Self {
            allocation_tracker: Arc::new(Mutex::new(MemoryAllocationTracker::new())),
            reference_checker: Arc::new(Mutex::new(ReferenceValidityChecker::new())),
            data_race_detector: Arc::new(Mutex::new(DataRaceDetector::new())),
            memory_leak_detector: Arc::new(Mutex::new(MemoryLeakDetector::new())),
            buffer_safety_checker: Arc::new(Mutex::new(BufferSafetyChecker::new())),
            statistics: Arc::new(Mutex::new(MemorySafetyStatistics::new())),
        }
    }
    
    /// 检查内存安全 / Check Memory Safety
    pub fn check_memory_safety(&self, program: &Program) -> Result<MemorySafetyReport, MemorySafetyError> {
        let start_time = Instant::now();
        let mut report = MemorySafetyReport::new();
        
        // 更新统计信息
        {
            let mut stats = self.statistics.lock().unwrap();
            stats.total_checks += 1;
            stats.check_start_time = start_time;
        }
        
        // 检查内存分配
        if let Ok(allocation_report) = self.check_memory_allocations(program) {
            report.add_allocation_report(allocation_report);
        }
        
        // 检查引用有效性
        if let Ok(reference_report) = self.check_reference_validity(program) {
            report.add_reference_report(reference_report);
        }
        
        // 检查数据竞争
        if let Ok(data_race_report) = self.check_data_races(program) {
            report.add_data_race_report(data_race_report);
        }
        
        // 检查内存泄漏
        if let Ok(leak_report) = self.check_memory_leaks(program) {
            report.add_leak_report(leak_report);
        }
        
        // 检查缓冲区安全
        if let Ok(buffer_report) = self.check_buffer_safety(program) {
            report.add_buffer_report(buffer_report);
        }
        
        // 更新统计信息
        {
            let mut stats = self.statistics.lock().unwrap();
            stats.last_check_duration = start_time.elapsed();
            stats.total_check_time += stats.last_check_duration;
        }
        
        Ok(report)
    }
    
    /// 检查内存分配 / Check Memory Allocations
    fn check_memory_allocations(&self, program: &Program) -> Result<AllocationReport, MemorySafetyError> {
        let tracker = self.allocation_tracker.lock().unwrap();
        tracker.check_allocations(program)
    }
    
    /// 检查引用有效性 / Check Reference Validity
    fn check_reference_validity(&self, program: &Program) -> Result<ReferenceReport, MemorySafetyError> {
        let checker = self.reference_checker.lock().unwrap();
        checker.check_references(program)
    }
    
    /// 检查数据竞争 / Check Data Races
    fn check_data_races(&self, program: &Program) -> Result<DataRaceReport, MemorySafetyError> {
        let detector = self.data_race_detector.lock().unwrap();
        detector.detect_races(program)
    }
    
    /// 检查内存泄漏 / Check Memory Leaks
    fn check_memory_leaks(&self, program: &Program) -> Result<LeakReport, MemorySafetyError> {
        let detector = self.memory_leak_detector.lock().unwrap();
        detector.detect_leaks(program)
    }
    
    /// 检查缓冲区安全 / Check Buffer Safety
    fn check_buffer_safety(&self, program: &Program) -> Result<BufferReport, MemorySafetyError> {
        let checker = self.buffer_safety_checker.lock().unwrap();
        checker.check_buffers(program)
    }
    
    /// 获取统计信息 / Get Statistics
    pub fn get_statistics(&self) -> MemorySafetyStatistics {
        self.statistics.lock().unwrap().clone()
    }
    
    /// 重置统计信息 / Reset Statistics
    pub fn reset_statistics(&self) {
        let mut stats = self.statistics.lock().unwrap();
        *stats = MemorySafetyStatistics::new();
    }
}

/// 程序结构体 / Program Struct
#[derive(Debug, Clone)]
pub struct Program {
    /// 程序名称 / Program Name
    pub name: String,
    /// 函数列表 / Function List
    pub functions: Vec<Function>,
    /// 全局变量 / Global Variables
    pub global_variables: Vec<GlobalVariable>,
    /// 内存分配 / Memory Allocations
    pub allocations: Vec<MemoryAllocation>,
    /// 引用 / References
    pub references: Vec<Reference>,
    /// 线程 / Threads
    pub threads: Vec<Thread>,
}

/// 函数结构体 / Function Struct
#[derive(Debug, Clone)]
pub struct Function {
    /// 函数名称 / Function Name
    pub name: String,
    /// 参数列表 / Parameter List
    pub parameters: Vec<Parameter>,
    /// 返回值类型 / Return Type
    pub return_type: String,
    /// 局部变量 / Local Variables
    pub local_variables: Vec<LocalVariable>,
    /// 内存分配 / Memory Allocations
    pub allocations: Vec<MemoryAllocation>,
    /// 引用 / References
    pub references: Vec<Reference>,
}

/// 参数结构体 / Parameter Struct
#[derive(Debug, Clone)]
pub struct Parameter {
    /// 参数名称 / Parameter Name
    pub name: String,
    /// 参数类型 / Parameter Type
    pub param_type: String,
    /// 是否可变 / Is Mutable
    pub is_mutable: bool,
    /// 生命周期 / Lifetime
    pub lifetime: Option<String>,
}

/// 全局变量结构体 / Global Variable Struct
#[derive(Debug, Clone)]
pub struct GlobalVariable {
    /// 变量名称 / Variable Name
    pub name: String,
    /// 变量类型 / Variable Type
    pub var_type: String,
    /// 是否可变 / Is Mutable
    pub is_mutable: bool,
    /// 初始化值 / Initial Value
    pub initial_value: Option<String>,
}

/// 局部变量结构体 / Local Variable Struct
#[derive(Debug, Clone)]
pub struct LocalVariable {
    /// 变量名称 / Variable Name
    pub name: String,
    /// 变量类型 / Variable Type
    pub var_type: String,
    /// 是否可变 / Is Mutable
    pub is_mutable: bool,
    /// 作用域 / Scope
    pub scope: String,
    /// 生命周期 / Lifetime
    pub lifetime: Option<String>,
}

/// 内存分配结构体 / Memory Allocation Struct
#[derive(Debug, Clone)]
pub struct MemoryAllocation {
    /// 分配ID / Allocation ID
    pub allocation_id: String,
    /// 分配大小 / Allocation Size
    pub size: usize,
    /// 分配类型 / Allocation Type
    pub allocation_type: AllocationType,
    /// 分配位置 / Allocation Location
    pub location: AllocationLocation,
    /// 分配时间 / Allocation Time
    pub allocated_at: Instant,
    /// 是否已释放 / Is Freed
    pub is_freed: bool,
    /// 释放时间 / Free Time
    pub freed_at: Option<Instant>,
}

/// 分配类型枚举 / Allocation Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum AllocationType {
    /// 堆分配 / Heap Allocation
    Heap,
    /// 栈分配 / Stack Allocation
    Stack,
    /// 静态分配 / Static Allocation
    Static,
    /// 全局分配 / Global Allocation
    Global,
}

/// 分配位置 / Allocation Location
#[derive(Debug, Clone)]
pub struct AllocationLocation {
    /// 文件路径 / File Path
    pub file_path: String,
    /// 行号 / Line Number
    pub line_number: usize,
    /// 列号 / Column Number
    pub column_number: usize,
    /// 函数名称 / Function Name
    pub function_name: String,
}

/// 引用结构体 / Reference Struct
#[derive(Debug, Clone)]
pub struct Reference {
    /// 引用ID / Reference ID
    pub reference_id: String,
    /// 引用类型 / Reference Type
    pub reference_type: ReferenceType,
    /// 目标分配 / Target Allocation
    pub target_allocation: String,
    /// 引用位置 / Reference Location
    pub location: AllocationLocation,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
    /// 是否有效 / Is Valid
    pub is_valid: bool,
    /// 生命周期 / Lifetime
    pub lifetime: Option<String>,
}

/// 引用类型枚举 / Reference Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum ReferenceType {
    /// 不可变引用 / Immutable Reference
    Immutable,
    /// 可变引用 / Mutable Reference
    Mutable,
    /// 原始指针 / Raw Pointer
    RawPointer,
    /// 智能指针 / Smart Pointer
    SmartPointer,
}

/// 线程结构体 / Thread Struct
#[derive(Debug, Clone)]
pub struct Thread {
    /// 线程ID / Thread ID
    pub thread_id: String,
    /// 线程名称 / Thread Name
    pub thread_name: String,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
    /// 内存访问 / Memory Accesses
    pub memory_accesses: Vec<MemoryAccess>,
    /// 同步原语 / Synchronization Primitives
    pub synchronization_primitives: Vec<SynchronizationPrimitive>,
}

/// 内存访问 / Memory Access
#[derive(Debug, Clone)]
pub struct MemoryAccess {
    /// 访问ID / Access ID
    pub access_id: String,
    /// 访问类型 / Access Type
    pub access_type: AccessType,
    /// 目标分配 / Target Allocation
    pub target_allocation: String,
    /// 访问位置 / Access Location
    pub location: AllocationLocation,
    /// 访问时间 / Access Time
    pub access_time: Instant,
    /// 线程ID / Thread ID
    pub thread_id: String,
}

/// 访问类型枚举 / Access Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum AccessType {
    /// 读取 / Read
    Read,
    /// 写入 / Write
    Write,
    /// 读写 / ReadWrite
    ReadWrite,
    /// 释放 / Free
    Free,
}

/// 同步原语 / Synchronization Primitive
#[derive(Debug, Clone)]
pub struct SynchronizationPrimitive {
    /// 原语ID / Primitive ID
    pub primitive_id: String,
    /// 原语类型 / Primitive Type
    pub primitive_type: PrimitiveType,
    /// 保护的内存 / Protected Memory
    pub protected_memory: Vec<String>,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
}

/// 原语类型枚举 / Primitive Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    /// 互斥锁 / Mutex
    Mutex,
    /// 读写锁 / RwLock
    RwLock,
    /// 信号量 / Semaphore
    Semaphore,
    /// 条件变量 / Condition Variable
    ConditionVariable,
    /// 原子操作 / Atomic Operation
    Atomic,
}

/// 内存分配跟踪器 / Memory Allocation Tracker
pub struct MemoryAllocationTracker {
    /// 分配记录 / Allocation Records
    allocations: HashMap<String, MemoryAllocation>,
    /// 分配统计 / Allocation Statistics
    statistics: AllocationStatistics,
}

impl MemoryAllocationTracker {
    /// 创建新的内存分配跟踪器 / Create New Memory Allocation Tracker
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            statistics: AllocationStatistics::new(),
        }
    }
    
    /// 检查内存分配 / Check Memory Allocations
    pub fn check_allocations(&self, program: &Program) -> Result<AllocationReport, MemorySafetyError> {
        let mut report = AllocationReport::new();
        
        // 检查双重释放
        for allocation in &program.allocations {
            if allocation.is_freed {
                if let Some(freed_at) = allocation.freed_at {
                    // 检查是否有其他释放操作
                    for other_allocation in &program.allocations {
                        if other_allocation.allocation_id != allocation.allocation_id
                            && other_allocation.target_allocation == allocation.target_allocation
                            && other_allocation.is_freed
                        {
                            report.add_violation(AllocationViolation {
                                allocation_id: allocation.allocation_id.clone(),
                                violation_type: ViolationType::DoubleFree,
                                description: format!(
                                    "Double free detected for allocation {}",
                                    allocation.allocation_id
                                ),
                                severity: Severity::Critical,
                            });
                        }
                    }
                }
            }
        }
        
        // 检查内存泄漏
        for allocation in &program.allocations {
            if !allocation.is_freed {
                // 检查分配是否仍然被引用
                let mut is_referenced = false;
                for reference in &program.references {
                    if reference.target_allocation == allocation.allocation_id && reference.is_valid {
                        is_referenced = true;
                        break;
                    }
                }
                
                if !is_referenced {
                    report.add_violation(AllocationViolation {
                        allocation_id: allocation.allocation_id.clone(),
                        violation_type: ViolationType::MemoryLeak,
                        description: format!(
                            "Memory leak detected for allocation {}",
                            allocation.allocation_id
                        ),
                        severity: Severity::High,
                    });
                }
            }
        }
        
        Ok(report)
    }
}

/// 引用有效性检查器 / Reference Validity Checker
pub struct ReferenceValidityChecker {
    /// 引用记录 / Reference Records
    references: HashMap<String, Reference>,
    /// 检查统计 / Check Statistics
    statistics: ReferenceCheckStatistics,
}

impl ReferenceValidityChecker {
    /// 创建新的引用有效性检查器 / Create New Reference Validity Checker
    pub fn new() -> Self {
        Self {
            references: HashMap::new(),
            statistics: ReferenceCheckStatistics::new(),
        }
    }
    
    /// 检查引用 / Check References
    pub fn check_references(&self, program: &Program) -> Result<ReferenceReport, MemorySafetyError> {
        let mut report = ReferenceReport::new();
        
        // 检查悬垂引用
        for reference in &program.references {
            if reference.is_valid {
                // 检查目标分配是否仍然有效
                let mut target_valid = false;
                for allocation in &program.allocations {
                    if allocation.allocation_id == reference.target_allocation && !allocation.is_freed {
                        target_valid = true;
                        break;
                    }
                }
                
                if !target_valid {
                    report.add_violation(ReferenceViolation {
                        reference_id: reference.reference_id.clone(),
                        violation_type: ViolationType::DanglingReference,
                        description: format!(
                            "Dangling reference detected for reference {}",
                            reference.reference_id
                        ),
                        severity: Severity::Critical,
                    });
                }
            }
        }
        
        // 检查释放后使用
        for reference in &program.references {
            if reference.is_valid {
                for allocation in &program.allocations {
                    if allocation.allocation_id == reference.target_allocation
                        && allocation.is_freed
                        && allocation.freed_at.is_some()
                        && reference.created_at < allocation.freed_at.unwrap()
                    {
                        report.add_violation(ReferenceViolation {
                            reference_id: reference.reference_id.clone(),
                            violation_type: ViolationType::UseAfterFree,
                            description: format!(
                                "Use after free detected for reference {}",
                                reference.reference_id
                            ),
                            severity: Severity::Critical,
                        });
                    }
                }
            }
        }
        
        Ok(report)
    }
}

/// 数据竞争检测器 / Data Race Detector
pub struct DataRaceDetector {
    /// 访问记录 / Access Records
    access_records: Vec<MemoryAccess>,
    /// 检测统计 / Detection Statistics
    statistics: DataRaceDetectionStatistics,
}

impl DataRaceDetector {
    /// 创建新的数据竞争检测器 / Create New Data Race Detector
    pub fn new() -> Self {
        Self {
            access_records: Vec::new(),
            statistics: DataRaceDetectionStatistics::new(),
        }
    }
    
    /// 检测数据竞争 / Detect Data Races
    pub fn detect_races(&self, program: &Program) -> Result<DataRaceReport, MemorySafetyError> {
        let mut report = DataRaceReport::new();
        
        // 收集所有内存访问
        let mut all_accesses = Vec::new();
        for thread in &program.threads {
            all_accesses.extend(thread.memory_accesses.clone());
        }
        
        // 检查数据竞争
        for i in 0..all_accesses.len() {
            for j in i + 1..all_accesses.len() {
                if self.is_data_race(&all_accesses[i], &all_accesses[j]) {
                    report.add_race(DataRace {
                        access1: all_accesses[i].clone(),
                        access2: all_accesses[j].clone(),
                        race_type: RaceType::DataRace,
                        description: format!(
                            "Data race between {} and {}",
                            all_accesses[i].access_id, all_accesses[j].access_id
                        ),
                        severity: Severity::High,
                    });
                }
            }
        }
        
        Ok(report)
    }
    
    /// 检查是否为数据竞争 / Check if Data Race
    fn is_data_race(&self, access1: &MemoryAccess, access2: &MemoryAccess) -> bool {
        // 检查是否为同一内存地址
        if access1.target_allocation != access2.target_allocation {
            return false;
        }
        
        // 检查是否为不同线程
        if access1.thread_id == access2.thread_id {
            return false;
        }
        
        // 检查是否至少有一个是写操作
        matches!(access1.access_type, AccessType::Write) || matches!(access2.access_type, AccessType::Write)
    }
}

/// 内存泄漏检测器 / Memory Leak Detector
pub struct MemoryLeakDetector {
    /// 泄漏记录 / Leak Records
    leak_records: Vec<MemoryLeak>,
    /// 检测统计 / Detection Statistics
    statistics: LeakDetectionStatistics,
}

impl MemoryLeakDetector {
    /// 创建新的内存泄漏检测器 / Create New Memory Leak Detector
    pub fn new() -> Self {
        Self {
            leak_records: Vec::new(),
            statistics: LeakDetectionStatistics::new(),
        }
    }
    
    /// 检测内存泄漏 / Detect Memory Leaks
    pub fn detect_leaks(&self, program: &Program) -> Result<LeakReport, MemorySafetyError> {
        let mut report = LeakReport::new();
        
        // 检查未释放的分配
        for allocation in &program.allocations {
            if !allocation.is_freed {
                // 检查分配是否仍然被引用
                let mut is_referenced = false;
                for reference in &program.references {
                    if reference.target_allocation == allocation.allocation_id && reference.is_valid {
                        is_referenced = true;
                        break;
                    }
                }
                
                if !is_referenced {
                    report.add_leak(MemoryLeak {
                        allocation_id: allocation.allocation_id.clone(),
                        leak_type: LeakType::UnfreedAllocation,
                        description: format!(
                            "Memory leak detected for allocation {}",
                            allocation.allocation_id
                        ),
                        severity: Severity::High,
                        leaked_size: allocation.size,
                    });
                }
            }
        }
        
        Ok(report)
    }
}

/// 缓冲区安全检查器 / Buffer Safety Checker
pub struct BufferSafetyChecker {
    /// 缓冲区记录 / Buffer Records
    buffer_records: Vec<Buffer>,
    /// 检查统计 / Check Statistics
    statistics: BufferCheckStatistics,
}

impl BufferSafetyChecker {
    /// 创建新的缓冲区安全检查器 / Create New Buffer Safety Checker
    pub fn new() -> Self {
        Self {
            buffer_records: Vec::new(),
            statistics: BufferCheckStatistics::new(),
        }
    }
    
    /// 检查缓冲区 / Check Buffers
    pub fn check_buffers(&self, program: &Program) -> Result<BufferReport, MemorySafetyError> {
        let mut report = BufferReport::new();
        
        // 检查缓冲区溢出
        for allocation in &program.allocations {
            if allocation.allocation_type == AllocationType::Stack {
                // 检查栈溢出
                if allocation.size > 1024 * 1024 { // 1MB 限制
                    report.add_violation(BufferViolation {
                        buffer_id: allocation.allocation_id.clone(),
                        violation_type: ViolationType::BufferOverflow,
                        description: format!(
                            "Stack overflow detected for allocation {}",
                            allocation.allocation_id
                        ),
                        severity: Severity::Critical,
                    });
                }
            }
        }
        
        Ok(report)
    }
}

/// 缓冲区结构体 / Buffer Struct
#[derive(Debug, Clone)]
pub struct Buffer {
    /// 缓冲区ID / Buffer ID
    pub buffer_id: String,
    /// 缓冲区大小 / Buffer Size
    pub size: usize,
    /// 缓冲区类型 / Buffer Type
    pub buffer_type: BufferType,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
}

/// 缓冲区类型枚举 / Buffer Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum BufferType {
    /// 数组 / Array
    Array,
    /// 向量 / Vector
    Vector,
    /// 字符串 / String
    String,
    /// 字节缓冲区 / Byte Buffer
    ByteBuffer,
}

/// 内存泄漏 / Memory Leak
#[derive(Debug, Clone)]
pub struct MemoryLeak {
    /// 分配ID / Allocation ID
    pub allocation_id: String,
    /// 泄漏类型 / Leak Type
    pub leak_type: LeakType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
    /// 泄漏大小 / Leaked Size
    pub leaked_size: usize,
}

/// 泄漏类型枚举 / Leak Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum LeakType {
    /// 未释放分配 / Unfreed Allocation
    UnfreedAllocation,
    /// 循环引用 / Circular Reference
    CircularReference,
    /// 资源泄漏 / Resource Leak
    ResourceLeak,
}

/// 数据竞争 / Data Race
#[derive(Debug, Clone)]
pub struct DataRace {
    /// 访问1 / Access 1
    pub access1: MemoryAccess,
    /// 访问2 / Access 2
    pub access2: MemoryAccess,
    /// 竞争类型 / Race Type
    pub race_type: RaceType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
}

/// 竞争类型枚举 / Race Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum RaceType {
    /// 数据竞争 / Data Race
    DataRace,
    /// 借用竞争 / Borrow Race
    BorrowRace,
    /// 生命周期竞争 / Lifetime Race
    LifetimeRace,
}

/// 严重程度枚举 / Severity Enum
#[derive(Debug, Clone, PartialEq)]
pub enum Severity {
    /// 低 / Low
    Low,
    /// 中 / Medium
    Medium,
    /// 高 / High
    High,
    /// 严重 / Critical
    Critical,
}

/// 违规类型枚举 / Violation Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum ViolationType {
    /// 悬垂引用 / Dangling Reference
    DanglingReference,
    /// 释放后使用 / Use After Free
    UseAfterFree,
    /// 双重释放 / Double Free
    DoubleFree,
    /// 内存泄漏 / Memory Leak
    MemoryLeak,
    /// 缓冲区溢出 / Buffer Overflow
    BufferOverflow,
    /// 数据竞争 / Data Race
    DataRace,
}

/// 内存安全报告 / Memory Safety Report
#[derive(Debug, Clone)]
pub struct MemorySafetyReport {
    /// 分配报告 / Allocation Report
    pub allocation_report: Option<AllocationReport>,
    /// 引用报告 / Reference Report
    pub reference_report: Option<ReferenceReport>,
    /// 数据竞争报告 / Data Race Report
    pub data_race_report: Option<DataRaceReport>,
    /// 泄漏报告 / Leak Report
    pub leak_report: Option<LeakReport>,
    /// 缓冲区报告 / Buffer Report
    pub buffer_report: Option<BufferReport>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
    /// 是否安全 / Is Safe
    pub is_safe: bool,
}

impl MemorySafetyReport {
    /// 创建新的内存安全报告 / Create New Memory Safety Report
    pub fn new() -> Self {
        Self {
            allocation_report: None,
            reference_report: None,
            data_race_report: None,
            leak_report: None,
            buffer_report: None,
            check_time: Duration::from_secs(0),
            is_safe: true,
        }
    }
    
    /// 添加分配报告 / Add Allocation Report
    pub fn add_allocation_report(&mut self, report: AllocationReport) {
        self.allocation_report = Some(report);
        if let Some(ref allocation_report) = self.allocation_report {
            if !allocation_report.violations.is_empty() {
                self.is_safe = false;
            }
        }
    }
    
    /// 添加引用报告 / Add Reference Report
    pub fn add_reference_report(&mut self, report: ReferenceReport) {
        self.reference_report = Some(report);
        if let Some(ref reference_report) = self.reference_report {
            if !reference_report.violations.is_empty() {
                self.is_safe = false;
            }
        }
    }
    
    /// 添加数据竞争报告 / Add Data Race Report
    pub fn add_data_race_report(&mut self, report: DataRaceReport) {
        self.data_race_report = Some(report);
        if let Some(ref data_race_report) = self.data_race_report {
            if !data_race_report.races.is_empty() {
                self.is_safe = false;
            }
        }
    }
    
    /// 添加泄漏报告 / Add Leak Report
    pub fn add_leak_report(&mut self, report: LeakReport) {
        self.leak_report = Some(report);
        if let Some(ref leak_report) = self.leak_report {
            if !leak_report.leaks.is_empty() {
                self.is_safe = false;
            }
        }
    }
    
    /// 添加缓冲区报告 / Add Buffer Report
    pub fn add_buffer_report(&mut self, report: BufferReport) {
        self.buffer_report = Some(report);
        if let Some(ref buffer_report) = self.buffer_report {
            if !buffer_report.violations.is_empty() {
                self.is_safe = false;
            }
        }
    }
}

/// 分配报告 / Allocation Report
#[derive(Debug, Clone)]
pub struct AllocationReport {
    /// 违规列表 / Violations
    pub violations: Vec<AllocationViolation>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
}

impl AllocationReport {
    /// 创建新的分配报告 / Create New Allocation Report
    pub fn new() -> Self {
        Self {
            violations: Vec::new(),
            check_time: Duration::from_secs(0),
        }
    }
    
    /// 添加违规 / Add Violation
    pub fn add_violation(&mut self, violation: AllocationViolation) {
        self.violations.push(violation);
    }
}

/// 分配违规 / Allocation Violation
#[derive(Debug, Clone)]
pub struct AllocationViolation {
    /// 分配ID / Allocation ID
    pub allocation_id: String,
    /// 违规类型 / Violation Type
    pub violation_type: ViolationType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
}

/// 引用报告 / Reference Report
#[derive(Debug, Clone)]
pub struct ReferenceReport {
    /// 违规列表 / Violations
    pub violations: Vec<ReferenceViolation>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
}

impl ReferenceReport {
    /// 创建新的引用报告 / Create New Reference Report
    pub fn new() -> Self {
        Self {
            violations: Vec::new(),
            check_time: Duration::from_secs(0),
        }
    }
    
    /// 添加违规 / Add Violation
    pub fn add_violation(&mut self, violation: ReferenceViolation) {
        self.violations.push(violation);
    }
}

/// 引用违规 / Reference Violation
#[derive(Debug, Clone)]
pub struct ReferenceViolation {
    /// 引用ID / Reference ID
    pub reference_id: String,
    /// 违规类型 / Violation Type
    pub violation_type: ViolationType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
}

/// 数据竞争报告 / Data Race Report
#[derive(Debug, Clone)]
pub struct DataRaceReport {
    /// 竞争列表 / Races
    pub races: Vec<DataRace>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
}

impl DataRaceReport {
    /// 创建新的数据竞争报告 / Create New Data Race Report
    pub fn new() -> Self {
        Self {
            races: Vec::new(),
            check_time: Duration::from_secs(0),
        }
    }
    
    /// 添加竞争 / Add Race
    pub fn add_race(&mut self, race: DataRace) {
        self.races.push(race);
    }
}

/// 泄漏报告 / Leak Report
#[derive(Debug, Clone)]
pub struct LeakReport {
    /// 泄漏列表 / Leaks
    pub leaks: Vec<MemoryLeak>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
}

impl LeakReport {
    /// 创建新的泄漏报告 / Create New Leak Report
    pub fn new() -> Self {
        Self {
            leaks: Vec::new(),
            check_time: Duration::from_secs(0),
        }
    }
    
    /// 添加泄漏 / Add Leak
    pub fn add_leak(&mut self, leak: MemoryLeak) {
        self.leaks.push(leak);
    }
}

/// 缓冲区报告 / Buffer Report
#[derive(Debug, Clone)]
pub struct BufferReport {
    /// 违规列表 / Violations
    pub violations: Vec<BufferViolation>,
    /// 检查时间 / Check Time
    pub check_time: Duration,
}

impl BufferReport {
    /// 创建新的缓冲区报告 / Create New Buffer Report
    pub fn new() -> Self {
        Self {
            violations: Vec::new(),
            check_time: Duration::from_secs(0),
        }
    }
    
    /// 添加违规 / Add Violation
    pub fn add_violation(&mut self, violation: BufferViolation) {
        self.violations.push(violation);
    }
}

/// 缓冲区违规 / Buffer Violation
#[derive(Debug, Clone)]
pub struct BufferViolation {
    /// 缓冲区ID / Buffer ID
    pub buffer_id: String,
    /// 违规类型 / Violation Type
    pub violation_type: ViolationType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
}

/// 内存安全统计 / Memory Safety Statistics
#[derive(Debug, Clone)]
pub struct MemorySafetyStatistics {
    /// 总检查次数 / Total Checks
    pub total_checks: usize,
    /// 检查开始时间 / Check Start Time
    pub check_start_time: Instant,
    /// 最后检查持续时间 / Last Check Duration
    pub last_check_duration: Duration,
    /// 总检查时间 / Total Check Time
    pub total_check_time: Duration,
    /// 平均检查时间 / Average Check Time
    pub average_check_time: Duration,
}

impl MemorySafetyStatistics {
    /// 创建新的内存安全统计 / Create New Memory Safety Statistics
    pub fn new() -> Self {
        Self {
            total_checks: 0,
            check_start_time: Instant::now(),
            last_check_duration: Duration::from_secs(0),
            total_check_time: Duration::from_secs(0),
            average_check_time: Duration::from_secs(0),
        }
    }
}

/// 分配统计 / Allocation Statistics
#[derive(Debug, Clone)]
pub struct AllocationStatistics {
    /// 总分配次数 / Total Allocations
    pub total_allocations: usize,
    /// 总分配大小 / Total Allocation Size
    pub total_allocation_size: usize,
    /// 平均分配大小 / Average Allocation Size
    pub average_allocation_size: usize,
}

impl AllocationStatistics {
    /// 创建新的分配统计 / Create New Allocation Statistics
    pub fn new() -> Self {
        Self {
            total_allocations: 0,
            total_allocation_size: 0,
            average_allocation_size: 0,
        }
    }
}

/// 引用检查统计 / Reference Check Statistics
#[derive(Debug, Clone)]
pub struct ReferenceCheckStatistics {
    /// 总引用数量 / Total References
    pub total_references: usize,
    /// 有效引用数量 / Valid References
    pub valid_references: usize,
    /// 无效引用数量 / Invalid References
    pub invalid_references: usize,
}

impl ReferenceCheckStatistics {
    /// 创建新的引用检查统计 / Create New Reference Check Statistics
    pub fn new() -> Self {
        Self {
            total_references: 0,
            valid_references: 0,
            invalid_references: 0,
        }
    }
}

/// 数据竞争检测统计 / Data Race Detection Statistics
#[derive(Debug, Clone)]
pub struct DataRaceDetectionStatistics {
    /// 总检测次数 / Total Detections
    pub total_detections: usize,
    /// 检测到的竞争数量 / Detected Races
    pub detected_races: usize,
    /// 误报数量 / False Positives
    pub false_positives: usize,
}

impl DataRaceDetectionStatistics {
    /// 创建新的数据竞争检测统计 / Create New Data Race Detection Statistics
    pub fn new() -> Self {
        Self {
            total_detections: 0,
            detected_races: 0,
            false_positives: 0,
        }
    }
}

/// 泄漏检测统计 / Leak Detection Statistics
#[derive(Debug, Clone)]
pub struct LeakDetectionStatistics {
    /// 总检测次数 / Total Detections
    pub total_detections: usize,
    /// 检测到的泄漏数量 / Detected Leaks
    pub detected_leaks: usize,
    /// 泄漏总大小 / Total Leaked Size
    pub total_leaked_size: usize,
}

impl LeakDetectionStatistics {
    /// 创建新的泄漏检测统计 / Create New Leak Detection Statistics
    pub fn new() -> Self {
        Self {
            total_detections: 0,
            detected_leaks: 0,
            total_leaked_size: 0,
        }
    }
}

/// 缓冲区检查统计 / Buffer Check Statistics
#[derive(Debug, Clone)]
pub struct BufferCheckStatistics {
    /// 总检查次数 / Total Checks
    pub total_checks: usize,
    /// 检测到的违规数量 / Detected Violations
    pub detected_violations: usize,
    /// 缓冲区总大小 / Total Buffer Size
    pub total_buffer_size: usize,
}

impl BufferCheckStatistics {
    /// 创建新的缓冲区检查统计 / Create New Buffer Check Statistics
    pub fn new() -> Self {
        Self {
            total_checks: 0,
            detected_violations: 0,
            total_buffer_size: 0,
        }
    }
}

/// 内存安全错误类型 / Memory Safety Error Types
#[derive(Debug, Clone)]
pub enum MemorySafetyError {
    /// 检查失败 / Check Failed
    CheckFailed,
    /// 无效程序 / Invalid Program
    InvalidProgram,
    /// 安全检查失败 / Safety Check Failed
    SafetyCheckFailed,
    /// 内存访问错误 / Memory Access Error
    MemoryAccessError,
}

impl fmt::Display for MemorySafetyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemorySafetyError::CheckFailed => write!(f, "Memory safety check failed"),
            MemorySafetyError::InvalidProgram => write!(f, "Invalid program structure"),
            MemorySafetyError::SafetyCheckFailed => write!(f, "Memory safety check failed"),
            MemorySafetyError::MemoryAccessError => write!(f, "Memory access error"),
        }
    }
}

impl std::error::Error for MemorySafetyError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_safety_manager_creation() {
        let manager = MemorySafetyManager::new();
        let stats = manager.get_statistics();
        assert_eq!(stats.total_checks, 0);
    }

    #[test]
    fn test_program_creation() {
        let program = Program {
            name: "test_program".to_string(),
            functions: Vec::new(),
            global_variables: Vec::new(),
            allocations: Vec::new(),
            references: Vec::new(),
            threads: Vec::new(),
        };
        assert_eq!(program.name, "test_program");
    }

    #[test]
    fn test_memory_allocation_creation() {
        let allocation = MemoryAllocation {
            allocation_id: "alloc1".to_string(),
            size: 1024,
            allocation_type: AllocationType::Heap,
            location: AllocationLocation {
                file_path: "test.rs".to_string(),
                line_number: 10,
                column_number: 5,
                function_name: "test_function".to_string(),
            },
            allocated_at: Instant::now(),
            is_freed: false,
            freed_at: None,
        };
        assert_eq!(allocation.allocation_id, "alloc1");
        assert_eq!(allocation.size, 1024);
        assert_eq!(allocation.allocation_type, AllocationType::Heap);
    }

    #[test]
    fn test_reference_creation() {
        let reference = Reference {
            reference_id: "ref1".to_string(),
            reference_type: ReferenceType::Immutable,
            target_allocation: "alloc1".to_string(),
            location: AllocationLocation {
                file_path: "test.rs".to_string(),
                line_number: 15,
                column_number: 10,
                function_name: "test_function".to_string(),
            },
            created_at: Instant::now(),
            is_valid: true,
            lifetime: Some("'a".to_string()),
        };
        assert_eq!(reference.reference_id, "ref1");
        assert_eq!(reference.reference_type, ReferenceType::Immutable);
        assert_eq!(reference.target_allocation, "alloc1");
    }

    #[test]
    fn test_memory_safety_report_creation() {
        let report = MemorySafetyReport::new();
        assert!(report.is_safe);
        assert!(report.allocation_report.is_none());
        assert!(report.reference_report.is_none());
        assert!(report.data_race_report.is_none());
        assert!(report.leak_report.is_none());
        assert!(report.buffer_report.is_none());
    }
}
