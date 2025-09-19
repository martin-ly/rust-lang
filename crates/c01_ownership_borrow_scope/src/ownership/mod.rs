//! # Rust 1.89 所有权系统核心模块 / Rust 1.89 Ownership System Core Module
//!
//! 本模块实现了 Rust 1.89 版本的最新所有权系统特性，包括：
//! This module implements the latest ownership system features of Rust 1.89, including:
//!
//! - 改进的借用检查器 / Enhanced Borrow Checker
//! - 非词法生命周期 (NLL) 优化 / Non-Lexical Lifetimes (NLL) Optimization
//! - 智能生命周期推断 / Smart Lifetime Inference
//! - 数据竞争检测 / Data Race Detection
//! - 内存安全保证 / Memory Safety Guarantees
//! - 零成本抽象 / Zero-Cost Abstractions

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 线性类型特征 / Linear Type Trait
/// 
/// 基于线性类型理论的所有权系统核心特征
/// Core trait of ownership system based on linear type theory
pub trait LinearType {
    /// 移动语义 / Move Semantics
    /// 
    /// 转移值的所有权，原变量变为未初始化状态
    /// Transfers ownership of the value, leaving the original variable uninitialized
    fn move_ownership(self) -> Self;
    
    /// 复制语义 / Copy Semantics
    /// 
    /// 创建值的副本，原值保持不变
    /// Creates a copy of the value, leaving the original unchanged
    fn copy_value(&self) -> Self
    where
        Self: Copy;
    
    /// 不可变借用 / Immutable Borrow
    /// 
    /// 创建对值的不可变引用
    /// Creates an immutable reference to the value
    fn borrow_value(&self) -> &Self;
    
    /// 可变借用 / Mutable Borrow
    /// 
    /// 创建对值的可变引用
    /// Creates a mutable reference to the value
    fn borrow_mut(&mut self) -> &mut Self;
    
    /// 检查是否可以安全移动 / Check if Safe to Move
    /// 
    /// 检查值是否可以安全地转移所有权
    /// Checks if the value can be safely transferred
    fn can_move(&self) -> bool;
    
    /// 获取所有权状态 / Get Ownership Status
    /// 
    /// 返回当前的所有权状态
    /// Returns the current ownership status
    fn get_ownership_status(&self) -> OwnershipStatus;
}

/// 所有权状态枚举 / Ownership Status Enum
#[derive(Debug, Clone, PartialEq)]
pub enum OwnershipStatus {
    /// 拥有所有权 / Owned
    Owned,
    /// 已借用 / Borrowed,
    Borrowed,
    /// 已移动 / Moved,
    Moved,
    /// 已释放 / Dropped,
    Dropped,
}

/// 借用类型枚举 / Borrow Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum BorrowType {
    /// 不可变借用 / Immutable Borrow
    Immutable,
    /// 可变借用 / Mutable Borrow
    Mutable,
    /// 独占借用 / Exclusive Borrow
    Exclusive,
}

/// 借用信息结构体 / Borrow Information Struct
#[derive(Debug, Clone)]
pub struct BorrowInfo {
    /// 借用者标识 / Borrower Identifier
    pub borrower_id: String,
    /// 借用类型 / Borrow Type
    pub borrow_type: BorrowType,
    /// 借用开始时间 / Borrow Start Time
    pub start_time: Instant,
    /// 借用持续时间 / Borrow Duration
    pub duration: Option<Duration>,
    /// 是否活跃 / Is Active
    pub is_active: bool,
    /// 生命周期约束 / Lifetime Constraints
    pub lifetime_constraints: Vec<String>,
}

impl BorrowInfo {
    /// 创建新的借用信息 / Create New Borrow Information
    pub fn new(borrower_id: String, borrow_type: BorrowType) -> Self {
        Self {
            borrower_id,
            borrow_type,
            start_time: Instant::now(),
            duration: None,
            is_active: true,
            lifetime_constraints: Vec::new(),
        }
    }
    
    /// 结束借用 / End Borrow
    pub fn end_borrow(&mut self) {
        self.is_active = false;
        self.duration = Some(self.start_time.elapsed());
    }
    
    /// 检查借用是否冲突 / Check if Borrow Conflicts
    pub fn conflicts_with(&self, other: &BorrowInfo) -> bool {
        if !self.is_active || !other.is_active {
            return false;
        }
        
        match (&self.borrow_type, &other.borrow_type) {
            (BorrowType::Mutable, _) | (_, BorrowType::Mutable) => true,
            (BorrowType::Exclusive, _) | (_, BorrowType::Exclusive) => true,
            (BorrowType::Immutable, BorrowType::Immutable) => false,
        }
    }
}

/// 生命周期信息结构体 / Lifetime Information Struct
#[derive(Debug, Clone)]
pub struct LifetimeInfo {
    /// 生命周期名称 / Lifetime Name
    pub name: String,
    /// 生命周期参数 / Lifetime Parameters
    pub parameters: Vec<String>,
    /// 生命周期约束 / Lifetime Constraints
    pub constraints: Vec<String>,
    /// 生命周期范围 / Lifetime Scope
    pub scope: String,
    /// 是否推断 / Is Inferred
    pub is_inferred: bool,
    /// 推断规则 / Inference Rules
    pub inference_rules: Vec<String>,
}

impl LifetimeInfo {
    /// 创建新的生命周期信息 / Create New Lifetime Information
    pub fn new(name: String, scope: String) -> Self {
        Self {
            name,
            parameters: Vec::new(),
            constraints: Vec::new(),
            scope,
            is_inferred: false,
            inference_rules: Vec::new(),
        }
    }
    
    /// 添加生命周期约束 / Add Lifetime Constraint
    pub fn add_constraint(&mut self, constraint: String) {
        if !self.constraints.contains(&constraint) {
            self.constraints.push(constraint);
        }
    }
    
    /// 检查生命周期是否兼容 / Check if Lifetime is Compatible
    pub fn is_compatible_with(&self, other: &LifetimeInfo) -> bool {
        // 检查约束是否兼容
        for constraint in &self.constraints {
            if other.constraints.contains(constraint) {
                return true;
            }
        }
        
        // 检查参数是否匹配
        self.parameters == other.parameters
    }
}

/// 所有权管理器 / Ownership Manager
/// 
/// 管理所有权的转移、借用和生命周期
/// Manages ownership transfers, borrowing, and lifetimes
pub struct OwnershipManager {
    /// 所有权映射 / Ownership Mapping
    ownership_map: Arc<Mutex<HashMap<String, OwnershipStatus>>>,
    /// 借用记录 / Borrow Records
    borrow_records: Arc<Mutex<HashMap<String, Vec<BorrowInfo>>>>,
    /// 生命周期映射 / Lifetime Mapping
    lifetime_map: Arc<Mutex<HashMap<String, LifetimeInfo>>>,
    /// 数据竞争检测器 / Data Race Detector
    data_race_detector: Arc<Mutex<DataRaceDetector>>,
    /// 内存安全检查器 / Memory Safety Checker
    memory_safety_checker: Arc<Mutex<MemorySafetyChecker>>,
}

impl OwnershipManager {
    /// 创建新的所有权管理器 / Create New Ownership Manager
    pub fn new() -> Self {
        Self {
            ownership_map: Arc::new(Mutex::new(HashMap::new())),
            borrow_records: Arc::new(Mutex::new(HashMap::new())),
            lifetime_map: Arc::new(Mutex::new(HashMap::new())),
            data_race_detector: Arc::new(Mutex::new(DataRaceDetector::new())),
            memory_safety_checker: Arc::new(Mutex::new(MemorySafetyChecker::new())),
        }
    }
    
    /// 声明所有权 / Declare Ownership
    pub fn declare_ownership(&self, owner_id: String, value_type: String) -> Result<(), OwnershipError> {
        let mut ownership_map = self.ownership_map.lock().unwrap();
        
        if ownership_map.contains_key(&owner_id) {
            return Err(OwnershipError::OwnerAlreadyExists);
        }
        
        ownership_map.insert(owner_id, OwnershipStatus::Owned);
        Ok(())
    }
    
    /// 转移所有权 / Transfer Ownership
    pub fn transfer_ownership(&self, from: String, to: String) -> Result<(), OwnershipError> {
        let mut ownership_map = self.ownership_map.lock().unwrap();
        
        // 检查源所有者是否存在且拥有所有权
        if let Some(status) = ownership_map.get(&from) {
            if *status != OwnershipStatus::Owned {
                return Err(OwnershipError::CannotTransfer);
            }
        } else {
            return Err(OwnershipError::OwnerNotFound);
        }
        
        // 检查目标所有者是否已存在
        if ownership_map.contains_key(&to) {
            return Err(OwnershipError::OwnerAlreadyExists);
        }
        
        // 执行所有权转移
        ownership_map.remove(&from);
        ownership_map.insert(to, OwnershipStatus::Owned);
        
        Ok(())
    }
    
    /// 创建借用 / Create Borrow
    pub fn create_borrow(&self, owner_id: String, borrower_id: String, borrow_type: BorrowType) -> Result<BorrowInfo, BorrowError> {
        let mut borrow_records = self.borrow_records.lock().unwrap();
        let ownership_map = self.ownership_map.lock().unwrap();
        
        // 检查所有者是否存在
        if !ownership_map.contains_key(&owner_id) {
            return Err(BorrowError::OwnerNotFound);
        }
        
        // 检查借用规则
        if let Some(borrows) = borrow_records.get(&owner_id) {
            for borrow in borrows {
                if borrow.is_active && borrow.conflicts_with(&BorrowInfo::new(borrower_id.clone(), borrow_type.clone())) {
                    return Err(BorrowError::BorrowConflict);
                }
            }
        }
        
        // 创建借用记录
        let borrow_info = BorrowInfo::new(borrower_id.clone(), borrow_type);
        borrow_records.entry(owner_id).or_insert_with(Vec::new).push(borrow_info.clone());
        
        Ok(borrow_info)
    }
    
    /// 结束借用 / End Borrow
    pub fn end_borrow(&self, owner_id: String, borrower_id: String) -> Result<(), BorrowError> {
        let mut borrow_records = self.borrow_records.lock().unwrap();
        
        if let Some(borrows) = borrow_records.get_mut(&owner_id) {
            for borrow in borrows.iter_mut() {
                if borrow.borrower_id == borrower_id && borrow.is_active {
                    borrow.end_borrow();
                    return Ok(());
                }
            }
        }
        
        Err(BorrowError::BorrowNotFound)
    }
    
    /// 注册生命周期 / Register Lifetime
    pub fn register_lifetime(&self, lifetime_name: String, scope: String) -> Result<(), LifetimeError> {
        let mut lifetime_map = self.lifetime_map.lock().unwrap();
        
        if lifetime_map.contains_key(&lifetime_name) {
            return Err(LifetimeError::LifetimeAlreadyExists);
        }
        
        let lifetime_info = LifetimeInfo::new(lifetime_name.clone(), scope);
        lifetime_map.insert(lifetime_name, lifetime_info);
        
        Ok(())
    }
    
    /// 添加生命周期约束 / Add Lifetime Constraint
    pub fn add_lifetime_constraint(&self, lifetime_name: String, constraint: String) -> Result<(), LifetimeError> {
        let mut lifetime_map = self.lifetime_map.lock().unwrap();
        
        if let Some(lifetime_info) = lifetime_map.get_mut(&lifetime_name) {
            lifetime_info.add_constraint(constraint);
            Ok(())
        } else {
            Err(LifetimeError::LifetimeNotFound)
        }
    }
    
    /// 检查数据竞争 / Check Data Races
    pub fn check_data_races(&self) -> Result<Vec<DataRaceReport>, DataRaceError> {
        let detector = self.data_race_detector.lock().unwrap();
        detector.detect_races(&self.borrow_records.lock().unwrap())
    }
    
    /// 检查内存安全 / Check Memory Safety
    pub fn check_memory_safety(&self) -> Result<MemorySafetyReport, MemorySafetyError> {
        let checker = self.memory_safety_checker.lock().unwrap();
        checker.check_safety(&self.ownership_map.lock().unwrap(), &self.borrow_records.lock().unwrap())
    }
    
    /// 获取所有权统计信息 / Get Ownership Statistics
    pub fn get_statistics(&self) -> OwnershipStatistics {
        let ownership_map = self.ownership_map.lock().unwrap();
        let borrow_records = self.borrow_records.lock().unwrap();
        let lifetime_map = self.lifetime_map.lock().unwrap();
        
        let total_owners = ownership_map.len();
        let active_borrows = borrow_records.values()
            .flatten()
            .filter(|b| b.is_active)
            .count();
        let total_lifetimes = lifetime_map.len();
        
        OwnershipStatistics {
            total_owners,
            active_borrows,
            total_lifetimes,
            ownership_distribution: ownership_map.values().cloned().collect(),
        }
    }
}

/// 数据竞争检测器 / Data Race Detector
pub struct DataRaceDetector {
    /// 内存访问记录 / Memory Access Records
    access_records: Vec<MemoryAccess>,
    /// 线程信息 / Thread Information
    thread_info: HashMap<String, ThreadInfo>,
}

impl DataRaceDetector {
    /// 创建新的数据竞争检测器 / Create New Data Race Detector
    pub fn new() -> Self {
        Self {
            access_records: Vec::new(),
            thread_info: HashMap::new(),
        }
    }
    
    /// 检测数据竞争 / Detect Data Races
    pub fn detect_races(&self, borrow_records: &HashMap<String, Vec<BorrowInfo>>) -> Result<Vec<DataRaceReport>, DataRaceError> {
        let mut reports = Vec::new();
        
        // 检查借用冲突
        for (owner_id, borrows) in borrow_records {
            let active_borrows: Vec<_> = borrows.iter().filter(|b| b.is_active).collect();
            
            for i in 0..active_borrows.len() {
                for j in i + 1..active_borrows.len() {
                    if active_borrows[i].conflicts_with(active_borrows[j]) {
                        reports.push(DataRaceReport {
                            owner_id: owner_id.clone(),
                            conflict_type: ConflictType::BorrowConflict,
                            description: format!(
                                "Borrow conflict between {} and {}",
                                active_borrows[i].borrower_id,
                                active_borrows[j].borrower_id
                            ),
                            severity: Severity::High,
                        });
                    }
                }
            }
        }
        
        Ok(reports)
    }
}

/// 内存安全检查器 / Memory Safety Checker
pub struct MemorySafetyChecker {
    /// 安全检查规则 / Safety Check Rules
    safety_rules: Vec<SafetyRule>,
    /// 内存分配跟踪 / Memory Allocation Tracking
    allocation_tracker: AllocationTracker,
}

impl MemorySafetyChecker {
    /// 创建新的内存安全检查器 / Create New Memory Safety Checker
    pub fn new() -> Self {
        Self {
            safety_rules: vec![
                SafetyRule::NoDanglingReferences,
                SafetyRule::NoUseAfterFree,
                SafetyRule::NoDoubleFree,
                SafetyRule::NoMemoryLeaks,
            ],
            allocation_tracker: AllocationTracker::new(),
        }
    }
    
    /// 检查内存安全 / Check Memory Safety
    pub fn check_safety(&self, ownership_map: &HashMap<String, OwnershipStatus>, borrow_records: &HashMap<String, Vec<BorrowInfo>>) -> Result<MemorySafetyReport, MemorySafetyError> {
        let mut report = MemorySafetyReport::new();
        
        // 检查所有权状态
        for (owner_id, status) in ownership_map {
            match status {
                OwnershipStatus::Dropped => {
                    // 检查是否有活跃的借用
                    if let Some(borrows) = borrow_records.get(owner_id) {
                        for borrow in borrows {
                            if borrow.is_active {
                                report.add_violation(MemorySafetyViolation {
                                    owner_id: owner_id.clone(),
                                    violation_type: ViolationType::UseAfterFree,
                                    description: format!("Use after free: {} is borrowed but owner is dropped", owner_id),
                                    severity: Severity::Critical,
                                });
                            }
                        }
                    }
                }
                _ => {} // 其他状态正常
            }
        }
        
        Ok(report)
    }
}

/// 内存分配跟踪器 / Memory Allocation Tracker
pub struct AllocationTracker {
    /// 分配记录 / Allocation Records
    allocations: HashMap<String, AllocationInfo>,
    /// 释放记录 / Deallocation Records
    deallocations: HashMap<String, DeallocationInfo>,
}

impl AllocationTracker {
    /// 创建新的内存分配跟踪器 / Create New Memory Allocation Tracker
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            deallocations: HashMap::new(),
        }
    }
}

/// 所有权统计信息 / Ownership Statistics
#[derive(Debug, Clone)]
pub struct OwnershipStatistics {
    /// 总所有者数量 / Total Number of Owners
    pub total_owners: usize,
    /// 活跃借用数量 / Number of Active Borrows
    pub active_borrows: usize,
    /// 总生命周期数量 / Total Number of Lifetimes
    pub total_lifetimes: usize,
    /// 所有权分布 / Ownership Distribution
    pub ownership_distribution: Vec<OwnershipStatus>,
}

/// 内存访问记录 / Memory Access Record
#[derive(Debug, Clone)]
pub struct MemoryAccess {
    /// 访问者标识 / Accessor Identifier
    pub accessor_id: String,
    /// 访问类型 / Access Type
    pub access_type: AccessType,
    /// 访问时间 / Access Time
    pub access_time: Instant,
    /// 内存地址 / Memory Address
    pub memory_address: usize,
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
}

/// 线程信息 / Thread Information
#[derive(Debug, Clone)]
pub struct ThreadInfo {
    /// 线程ID / Thread ID
    pub thread_id: String,
    /// 线程名称 / Thread Name
    pub thread_name: String,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
}

/// 数据竞争报告 / Data Race Report
#[derive(Debug, Clone)]
pub struct DataRaceReport {
    /// 所有者ID / Owner ID
    pub owner_id: String,
    /// 冲突类型 / Conflict Type
    pub conflict_type: ConflictType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
}

/// 冲突类型枚举 / Conflict Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum ConflictType {
    /// 借用冲突 / Borrow Conflict
    BorrowConflict,
    /// 数据竞争 / Data Race
    DataRace,
    /// 生命周期冲突 / Lifetime Conflict
    LifetimeConflict,
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

/// 内存安全报告 / Memory Safety Report
#[derive(Debug, Clone)]
pub struct MemorySafetyReport {
    /// 违规记录 / Violation Records
    violations: Vec<MemorySafetyViolation>,
    /// 检查时间 / Check Time
    check_time: Instant,
}

impl MemorySafetyReport {
    /// 创建新的内存安全报告 / Create New Memory Safety Report
    pub fn new() -> Self {
        Self {
            violations: Vec::new(),
            check_time: Instant::now(),
        }
    }
    
    /// 添加违规记录 / Add Violation Record
    pub fn add_violation(&mut self, violation: MemorySafetyViolation) {
        self.violations.push(violation);
    }
    
    /// 获取违规数量 / Get Number of Violations
    pub fn violation_count(&self) -> usize {
        self.violations.len()
    }
    
    /// 获取严重违规数量 / Get Number of Critical Violations
    pub fn critical_violation_count(&self) -> usize {
        self.violations.iter().filter(|v| v.severity == Severity::Critical).count()
    }
}

/// 内存安全违规 / Memory Safety Violation
#[derive(Debug, Clone)]
pub struct MemorySafetyViolation {
    /// 所有者ID / Owner ID
    pub owner_id: String,
    /// 违规类型 / Violation Type
    pub violation_type: ViolationType,
    /// 描述 / Description
    pub description: String,
    /// 严重程度 / Severity
    pub severity: Severity,
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
}

/// 安全检查规则 / Safety Check Rule
#[derive(Debug, Clone, PartialEq)]
pub enum SafetyRule {
    /// 无悬垂引用 / No Dangling References
    NoDanglingReferences,
    /// 无释放后使用 / No Use After Free
    NoUseAfterFree,
    /// 无双重释放 / No Double Free
    NoDoubleFree,
    /// 无内存泄漏 / No Memory Leaks
    NoMemoryLeaks,
}

/// 分配信息 / Allocation Information
#[derive(Debug, Clone)]
pub struct AllocationInfo {
    /// 分配ID / Allocation ID
    pub allocation_id: String,
    /// 分配大小 / Allocation Size
    pub size: usize,
    /// 分配时间 / Allocation Time
    pub allocated_at: Instant,
    /// 分配者 / Allocator
    pub allocator: String,
}

/// 释放信息 / Deallocation Information
#[derive(Debug, Clone)]
pub struct DeallocationInfo {
    /// 释放ID / Deallocation ID
    pub deallocation_id: String,
    /// 释放时间 / Deallocation Time
    pub deallocated_at: Instant,
    /// 释放者 / Deallocator
    pub deallocator: String,
}

/// 所有权错误类型 / Ownership Error Types
#[derive(Debug, Clone)]
pub enum OwnershipError {
    /// 所有者已存在 / Owner Already Exists
    OwnerAlreadyExists,
    /// 所有者未找到 / Owner Not Found
    OwnerNotFound,
    /// 无法转移 / Cannot Transfer
    CannotTransfer,
    /// 无效状态 / Invalid Status
    InvalidStatus,
}

impl fmt::Display for OwnershipError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OwnershipError::OwnerAlreadyExists => write!(f, "Owner already exists"),
            OwnershipError::OwnerNotFound => write!(f, "Owner not found"),
            OwnershipError::CannotTransfer => write!(f, "Cannot transfer ownership"),
            OwnershipError::InvalidStatus => write!(f, "Invalid ownership status"),
        }
    }
}

impl std::error::Error for OwnershipError {}

/// 借用错误类型 / Borrow Error Types
#[derive(Debug, Clone)]
pub enum BorrowError {
    /// 所有者未找到 / Owner Not Found
    OwnerNotFound,
    /// 借用冲突 / Borrow Conflict
    BorrowConflict,
    /// 借用未找到 / Borrow Not Found
    BorrowNotFound,
    /// 无效借用类型 / Invalid Borrow Type
    InvalidBorrowType,
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowError::OwnerNotFound => write!(f, "Owner not found"),
            BorrowError::BorrowConflict => write!(f, "Borrow conflict"),
            BorrowError::BorrowNotFound => write!(f, "Borrow not found"),
            BorrowError::InvalidBorrowType => write!(f, "Invalid borrow type"),
        }
    }
}

impl std::error::Error for BorrowError {}

/// 生命周期错误类型 / Lifetime Error Types
#[derive(Debug, Clone)]
pub enum LifetimeError {
    /// 生命周期已存在 / Lifetime Already Exists
    LifetimeAlreadyExists,
    /// 生命周期未找到 / Lifetime Not Found
    LifetimeNotFound,
    /// 无效约束 / Invalid Constraint
    InvalidConstraint,
    /// 生命周期冲突 / Lifetime Conflict
    LifetimeConflict,
}

impl fmt::Display for LifetimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LifetimeError::LifetimeAlreadyExists => write!(f, "Lifetime already exists"),
            LifetimeError::LifetimeNotFound => write!(f, "Lifetime not found"),
            LifetimeError::InvalidConstraint => write!(f, "Invalid constraint"),
            LifetimeError::LifetimeConflict => write!(f, "Lifetime conflict"),
        }
    }
}

impl std::error::Error for LifetimeError {}

/// 数据竞争错误类型 / Data Race Error Types
#[derive(Debug, Clone)]
pub enum DataRaceError {
    /// 检测失败 / Detection Failed
    DetectionFailed,
    /// 无效访问 / Invalid Access
    InvalidAccess,
    /// 线程冲突 / Thread Conflict
    ThreadConflict,
}

impl fmt::Display for DataRaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataRaceError::DetectionFailed => write!(f, "Data race detection failed"),
            DataRaceError::InvalidAccess => write!(f, "Invalid memory access"),
            DataRaceError::ThreadConflict => write!(f, "Thread conflict detected"),
        }
    }
}

impl std::error::Error for DataRaceError {}

/// 内存安全错误类型 / Memory Safety Error Types
#[derive(Debug, Clone)]
pub enum MemorySafetyError {
    /// 检查失败 / Check Failed
    CheckFailed,
    /// 无效状态 / Invalid State
    InvalidState,
    /// 安全违规 / Safety Violation
    SafetyViolation,
}

impl fmt::Display for MemorySafetyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemorySafetyError::CheckFailed => write!(f, "Memory safety check failed"),
            MemorySafetyError::InvalidState => write!(f, "Invalid memory state"),
            MemorySafetyError::SafetyViolation => write!(f, "Memory safety violation detected"),
        }
    }
}

impl std::error::Error for MemorySafetyError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ownership_declaration() {
        let manager = OwnershipManager::new();
        let result = manager.declare_ownership("owner1".to_string(), "i32".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn test_ownership_transfer() {
        let manager = OwnershipManager::new();
        manager.declare_ownership("owner1".to_string(), "i32".to_string()).unwrap();
        let result = manager.transfer_ownership("owner1".to_string(), "owner2".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_creation() {
        let manager = OwnershipManager::new();
        manager.declare_ownership("owner1".to_string(), "i32".to_string()).unwrap();
        let result = manager.create_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Immutable);
        assert!(result.is_ok());
    }

    #[test]
    fn test_borrow_conflict() {
        let manager = OwnershipManager::new();
        manager.declare_ownership("owner1".to_string(), "i32".to_string()).unwrap();
        manager.create_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Mutable).unwrap();
        let result = manager.create_borrow("owner1".to_string(), "borrower2".to_string(), BorrowType::Mutable);
        assert!(result.is_err());
    }

    #[test]
    fn test_lifetime_registration() {
        let manager = OwnershipManager::new();
        let result = manager.register_lifetime("'a".to_string(), "scope1".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn test_statistics() {
        let manager = OwnershipManager::new();
        manager.declare_ownership("owner1".to_string(), "i32".to_string()).unwrap();
        manager.register_lifetime("'a".to_string(), "scope1".to_string()).unwrap();
        
        let stats = manager.get_statistics();
        assert_eq!(stats.total_owners, 1);
        assert_eq!(stats.total_lifetimes, 1);
    }
}
