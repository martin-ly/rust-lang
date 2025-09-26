//! # Rust 所有权系统实用工具库
//!
//! 本模块提供了 Rust 所有权系统的实用工具函数和类型，帮助开发者更好地管理所有权、借用和生命周期
//! This module provides utility functions and types for Rust's ownership system to help developers better manage ownership, borrowing, and lifetimes

use std::collections::HashMap;
use std::fmt;
use std::time::{Duration, Instant};

/// 所有权跟踪器 / Ownership Tracker
///
/// 用于跟踪和管理所有权转移的工具
/// Utility for tracking and managing ownership transfers
pub struct OwnershipTracker {
    /// 所有权记录 / Ownership Records
    ownership_records: HashMap<String, OwnershipRecord>,
    /// 跟踪开始时间 / Tracking Start Time
    start_time: Instant,
}

/// 所有权记录 / Ownership Record
#[derive(Debug, Clone)]
pub struct OwnershipRecord {
    /// 所有者ID / Owner ID
    pub owner_id: String,
    /// 值类型 / Value Type
    pub value_type: String,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
    /// 最后访问时间 / Last Access Time
    pub last_accessed: Instant,
    /// 访问次数 / Access Count
    pub access_count: usize,
    /// 是否活跃 / Is Active
    pub is_active: bool,
}

impl Default for OwnershipTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl OwnershipTracker {
    /// 创建新的所有权跟踪器 / Create New Ownership Tracker
    pub fn new() -> Self {
        Self {
            ownership_records: HashMap::new(),
            start_time: Instant::now(),
        }
    }

    /// 记录所有权声明 / Record Ownership Declaration
    pub fn record_ownership(&mut self, owner_id: String, value_type: String) {
        let record = OwnershipRecord {
            owner_id: owner_id.clone(),
            value_type,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            access_count: 0,
            is_active: true,
        };

        self.ownership_records.insert(owner_id, record);
    }

    /// 记录所有权转移 / Record Ownership Transfer
    pub fn record_transfer(&mut self, from: String, to: String) -> Result<(), OwnershipError> {
        if let Some(mut record) = self.ownership_records.remove(&from) {
            record.owner_id = to.clone();
            record.last_accessed = Instant::now();
            record.access_count += 1;

            self.ownership_records.insert(to, record);
            Ok(())
        } else {
            Err(OwnershipError::OwnerNotFound)
        }
    }

    /// 记录访问 / Record Access
    pub fn record_access(&mut self, owner_id: &str) -> Result<(), OwnershipError> {
        if let Some(record) = self.ownership_records.get_mut(owner_id) {
            record.last_accessed = Instant::now();
            record.access_count += 1;
            Ok(())
        } else {
            Err(OwnershipError::OwnerNotFound)
        }
    }

    /// 记录所有权释放 / Record Ownership Release
    pub fn record_release(&mut self, owner_id: &str) -> Result<(), OwnershipError> {
        if let Some(record) = self.ownership_records.get_mut(owner_id) {
            record.is_active = false;
            record.last_accessed = Instant::now();
            Ok(())
        } else {
            Err(OwnershipError::OwnerNotFound)
        }
    }

    /// 获取所有权统计信息 / Get Ownership Statistics
    pub fn get_statistics(&self) -> OwnershipStatistics {
        let total_owners = self.ownership_records.len();
        let active_owners = self.ownership_records.values().filter(|r| r.is_active).count();
        let total_accesses: usize = self.ownership_records.values().map(|r| r.access_count).sum();
        let average_accesses = if total_owners > 0 {
            total_accesses as f64 / total_owners as f64
        } else {
            0.0
        };

        OwnershipStatistics {
            total_owners,
            active_owners,
            total_accesses,
            average_accesses,
            tracking_duration: self.start_time.elapsed(),
        }
    }

    /// 获取所有权记录 / Get Ownership Records
    pub fn get_records(&self) -> &HashMap<String, OwnershipRecord> {
        &self.ownership_records
    }
}

/// 所有权统计信息 / Ownership Statistics
#[derive(Debug, Clone)]
pub struct OwnershipStatistics {
    /// 总所有者数量 / Total Number of Owners
    pub total_owners: usize,
    /// 活跃所有者数量 / Number of Active Owners
    pub active_owners: usize,
    /// 总访问次数 / Total Number of Accesses
    pub total_accesses: usize,
    /// 平均访问次数 / Average Number of Accesses
    pub average_accesses: f64,
    /// 跟踪持续时间 / Tracking Duration
    pub tracking_duration: Duration,
}

/// 借用跟踪器 / Borrow Tracker
///
/// 用于跟踪和管理借用关系的工具
/// Utility for tracking and managing borrow relationships
pub struct BorrowTracker {
    /// 借用记录 / Borrow Records
    borrow_records: HashMap<String, Vec<BorrowRecord>>,
    /// 跟踪开始时间 / Tracking Start Time
    start_time: Instant,
}

/// 借用记录 / Borrow Record
#[derive(Debug, Clone)]
pub struct BorrowRecord {
    /// 借用者ID / Borrower ID
    pub borrower_id: String,
    /// 借用类型 / Borrow Type
    pub borrow_type: BorrowType,
    /// 借用开始时间 / Borrow Start Time
    pub start_time: Instant,
    /// 借用持续时间 / Borrow Duration
    pub duration: Option<Duration>,
    /// 是否活跃 / Is Active
    pub is_active: bool,
}

/// 借用类型 / Borrow Type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowType {
    /// 不可变借用 / Immutable Borrow
    Immutable,
    /// 可变借用 / Mutable Borrow
    Mutable,
    /// 独占借用 / Exclusive Borrow
    Exclusive,
}

impl Default for BorrowTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowTracker {
    /// 创建新的借用跟踪器 / Create New Borrow Tracker
    pub fn new() -> Self {
        Self {
            borrow_records: HashMap::new(),
            start_time: Instant::now(),
        }
    }

    /// 记录借用 / Record Borrow
    pub fn record_borrow(&mut self, owner_id: String, borrower_id: String, borrow_type: BorrowType) -> Result<(), BorrowError> {
        // 检查借用冲突 / Check for borrow conflicts
        if let Some(borrows) = self.borrow_records.get(&owner_id) {
            for borrow in borrows {
                if borrow.is_active && self.conflicts_with(&borrow_type, &borrow.borrow_type) {
                    return Err(BorrowError::BorrowConflict);
                }
            }
        }

        let record = BorrowRecord {
            borrower_id: borrower_id.clone(),
            borrow_type,
            start_time: Instant::now(),
            duration: None,
            is_active: true,
        };

        self.borrow_records.entry(owner_id).or_default().push(record);
        Ok(())
    }

    /// 记录借用结束 / Record Borrow End
    pub fn record_borrow_end(&mut self, owner_id: &str, borrower_id: &str) -> Result<(), BorrowError> {
        if let Some(borrows) = self.borrow_records.get_mut(owner_id) {
            for borrow in borrows.iter_mut() {
                if borrow.borrower_id == borrower_id && borrow.is_active {
                    borrow.is_active = false;
                    borrow.duration = Some(borrow.start_time.elapsed());
                    return Ok(());
                }
            }
        }
        Err(BorrowError::BorrowNotFound)
    }

    /// 检查借用冲突 / Check Borrow Conflicts
    fn conflicts_with(&self, borrow_type1: &BorrowType, borrow_type2: &BorrowType) -> bool {
        match (borrow_type1, borrow_type2) {
            (BorrowType::Mutable, _) | (_, BorrowType::Mutable) => true,
            (BorrowType::Exclusive, _) | (_, BorrowType::Exclusive) => true,
            (BorrowType::Immutable, BorrowType::Immutable) => false,
        }
    }

    /// 获取借用统计信息 / Get Borrow Statistics
    pub fn get_statistics(&self) -> BorrowStatistics {
        let total_borrows: usize = self.borrow_records.values().map(|v| v.len()).sum();
        let active_borrows: usize = self.borrow_records.values()
            .flatten()
            .filter(|b| b.is_active)
            .count();

        let mut borrow_type_counts = HashMap::new();
        for borrows in self.borrow_records.values() {
            for borrow in borrows {
                *borrow_type_counts.entry(borrow.borrow_type.clone()).or_insert(0) += 1;
            }
        }

        BorrowStatistics {
            total_borrows,
            active_borrows,
            borrow_type_counts,
            tracking_duration: self.start_time.elapsed(),
        }
    }

    /// 获取借用记录 / Get Borrow Records
    pub fn get_records(&self) -> &HashMap<String, Vec<BorrowRecord>> {
        &self.borrow_records
    }
}

/// 借用统计信息 / Borrow Statistics
#[derive(Debug, Clone)]
pub struct BorrowStatistics {
    /// 总借用次数 / Total Number of Borrows
    pub total_borrows: usize,
    /// 活跃借用次数 / Number of Active Borrows
    pub active_borrows: usize,
    /// 借用类型统计 / Borrow Type Statistics
    pub borrow_type_counts: HashMap<BorrowType, usize>,
    /// 跟踪持续时间 / Tracking Duration
    pub tracking_duration: Duration,
}

/// 生命周期跟踪器 / Lifetime Tracker
///
/// 用于跟踪和管理生命周期的工具
/// Utility for tracking and managing lifetimes
pub struct LifetimeTracker {
    /// 生命周期记录 / Lifetime Records
    lifetime_records: HashMap<String, LifetimeRecord>,
    /// 跟踪开始时间 / Tracking Start Time
    start_time: Instant,
}

/// 生命周期记录 / Lifetime Record
#[derive(Debug, Clone)]
pub struct LifetimeRecord {
    /// 生命周期名称 / Lifetime Name
    pub name: String,
    /// 生命周期范围 / Lifetime Scope
    pub scope: String,
    /// 创建时间 / Creation Time
    pub created_at: Instant,
    /// 结束时间 / End Time
    pub ended_at: Option<Instant>,
    /// 是否活跃 / Is Active
    pub is_active: bool,
    /// 关联的引用数量 / Number of Associated References
    pub reference_count: usize,
}

impl Default for LifetimeTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl LifetimeTracker {
    /// 创建新的生命周期跟踪器 / Create New Lifetime Tracker
    pub fn new() -> Self {
        Self {
            lifetime_records: HashMap::new(),
            start_time: Instant::now(),
        }
    }

    /// 记录生命周期开始 / Record Lifetime Start
    pub fn record_lifetime_start(&mut self, name: String, scope: String) {
        let record = LifetimeRecord {
            name: name.clone(),
            scope,
            created_at: Instant::now(),
            ended_at: None,
            is_active: true,
            reference_count: 0,
        };

        self.lifetime_records.insert(name, record);
    }

    /// 记录生命周期结束 / Record Lifetime End
    pub fn record_lifetime_end(&mut self, name: &str) -> Result<(), LifetimeError> {
        if let Some(record) = self.lifetime_records.get_mut(name) {
            record.is_active = false;
            record.ended_at = Some(Instant::now());
            Ok(())
        } else {
            Err(LifetimeError::LifetimeNotFound)
        }
    }

    /// 记录引用关联 / Record Reference Association
    pub fn record_reference_association(&mut self, lifetime_name: &str) -> Result<(), LifetimeError> {
        if let Some(record) = self.lifetime_records.get_mut(lifetime_name) {
            record.reference_count += 1;
            Ok(())
        } else {
            Err(LifetimeError::LifetimeNotFound)
        }
    }

    /// 获取生命周期统计信息 / Get Lifetime Statistics
    pub fn get_statistics(&self) -> LifetimeStatistics {
        let total_lifetimes = self.lifetime_records.len();
        let active_lifetimes = self.lifetime_records.values().filter(|r| r.is_active).count();
        let total_references: usize = self.lifetime_records.values().map(|r| r.reference_count).sum();
        let average_references = if total_lifetimes > 0 {
            total_references as f64 / total_lifetimes as f64
        } else {
            0.0
        };

        LifetimeStatistics {
            total_lifetimes,
            active_lifetimes,
            total_references,
            average_references,
            tracking_duration: self.start_time.elapsed(),
        }
    }

    /// 获取生命周期记录 / Get Lifetime Records
    pub fn get_records(&self) -> &HashMap<String, LifetimeRecord> {
        &self.lifetime_records
    }
}

/// 生命周期统计信息 / Lifetime Statistics
#[derive(Debug, Clone)]
pub struct LifetimeStatistics {
    /// 总生命周期数量 / Total Number of Lifetimes
    pub total_lifetimes: usize,
    /// 活跃生命周期数量 / Number of Active Lifetimes
    pub active_lifetimes: usize,
    /// 总引用数量 / Total Number of References
    pub total_references: usize,
    /// 平均引用数量 / Average Number of References
    pub average_references: f64,
    /// 跟踪持续时间 / Tracking Duration
    pub tracking_duration: Duration,
}

/// 所有权系统管理器 / Ownership System Manager
///
/// 统一管理所有权、借用和生命周期的工具
/// Utility for unified management of ownership, borrowing, and lifetimes
pub struct OwnershipSystemManager {
    /// 所有权跟踪器 / Ownership Tracker
    ownership_tracker: OwnershipTracker,
    /// 借用跟踪器 / Borrow Tracker
    borrow_tracker: BorrowTracker,
    /// 生命周期跟踪器 / Lifetime Tracker
    lifetime_tracker: LifetimeTracker,
}

impl Default for OwnershipSystemManager {
    fn default() -> Self {
        Self::new()
    }
}

impl OwnershipSystemManager {
    /// 创建新的所有权系统管理器 / Create New Ownership System Manager
    pub fn new() -> Self {
        Self {
            ownership_tracker: OwnershipTracker::new(),
            borrow_tracker: BorrowTracker::new(),
            lifetime_tracker: LifetimeTracker::new(),
        }
    }

    /// 获取所有权跟踪器 / Get Ownership Tracker
    pub fn ownership_tracker(&mut self) -> &mut OwnershipTracker {
        &mut self.ownership_tracker
    }

    /// 获取借用跟踪器 / Get Borrow Tracker
    pub fn borrow_tracker(&mut self) -> &mut BorrowTracker {
        &mut self.borrow_tracker
    }

    /// 获取生命周期跟踪器 / Get Lifetime Tracker
    pub fn lifetime_tracker(&mut self) -> &mut LifetimeTracker {
        &mut self.lifetime_tracker
    }

    /// 获取系统统计信息 / Get System Statistics
    pub fn get_system_statistics(&self) -> SystemStatistics {
        SystemStatistics {
            ownership: self.ownership_tracker.get_statistics(),
            borrowing: self.borrow_tracker.get_statistics(),
            lifetime: self.lifetime_tracker.get_statistics(),
        }
    }
}

/// 系统统计信息 / System Statistics
#[derive(Debug, Clone)]
pub struct SystemStatistics {
    /// 所有权统计 / Ownership Statistics
    pub ownership: OwnershipStatistics,
    /// 借用统计 / Borrow Statistics
    pub borrowing: BorrowStatistics,
    /// 生命周期统计 / Lifetime Statistics
    pub lifetime: LifetimeStatistics,
}

/// 所有权错误类型 / Ownership Error Types
#[derive(Debug, Clone)]
pub enum OwnershipError {
    /// 所有者未找到 / Owner Not Found
    OwnerNotFound,
    /// 所有者已存在 / Owner Already Exists
    OwnerAlreadyExists,
    /// 无法转移 / Cannot Transfer
    CannotTransfer,
    /// 无效状态 / Invalid Status
    InvalidStatus,
}

impl fmt::Display for OwnershipError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OwnershipError::OwnerNotFound => write!(f, "Owner not found"),
            OwnershipError::OwnerAlreadyExists => write!(f, "Owner already exists"),
            OwnershipError::CannotTransfer => write!(f, "Cannot transfer ownership"),
            OwnershipError::InvalidStatus => write!(f, "Invalid ownership status"),
        }
    }
}

impl std::error::Error for OwnershipError {}

/// 借用错误类型 / Borrow Error Types
#[derive(Debug, Clone)]
pub enum BorrowError {
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
    /// 生命周期未找到 / Lifetime Not Found
    LifetimeNotFound,
    /// 生命周期已存在 / Lifetime Already Exists
    LifetimeAlreadyExists,
    /// 无效约束 / Invalid Constraint
    InvalidConstraint,
}

impl fmt::Display for LifetimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LifetimeError::LifetimeNotFound => write!(f, "Lifetime not found"),
            LifetimeError::LifetimeAlreadyExists => write!(f, "Lifetime already exists"),
            LifetimeError::InvalidConstraint => write!(f, "Invalid constraint"),
        }
    }
}

impl std::error::Error for LifetimeError {}

/// 实用工具函数 / Utility Functions
/// 安全的所有权转移 / Safe Ownership Transfer
pub fn safe_ownership_transfer<T>(value: T) -> T {
    value
}

/// 安全的借用检查 / Safe Borrow Check
pub fn safe_borrow_check<T>(value: &T) -> &T {
    value
}

/// 安全的可变借用检查 / Safe Mutable Borrow Check
pub fn safe_mutable_borrow_check<T>(value: &mut T) -> &mut T {
    value
}

/// 安全的生命周期检查 / Safe Lifetime Check
pub fn safe_lifetime_check<T>(value: &T) -> &T {
    value
}

/// 所有权系统性能分析器 / Ownership System Performance Analyzer
pub struct PerformanceAnalyzer {
    /// 性能指标 / Performance Metrics
    metrics: HashMap<String, PerformanceMetric>,
}

/// 性能指标 / Performance Metric
#[derive(Debug, Clone)]
pub struct PerformanceMetric {
    /// 指标名称 / Metric Name
    pub name: String,
    /// 指标值 / Metric Value
    pub value: f64,
    /// 单位 / Unit
    pub unit: String,
    /// 时间戳 / Timestamp
    pub timestamp: Instant,
}

impl Default for PerformanceAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceAnalyzer {
    /// 创建新的性能分析器 / Create New Performance Analyzer
    pub fn new() -> Self {
        Self {
            metrics: HashMap::new(),
        }
    }

    /// 记录性能指标 / Record Performance Metric
    pub fn record_metric(&mut self, name: String, value: f64, unit: String) {
        let metric = PerformanceMetric {
            name: name.clone(),
            value,
            unit,
            timestamp: Instant::now(),
        };

        self.metrics.insert(name, metric);
    }

    /// 获取性能指标 / Get Performance Metric
    pub fn get_metric(&self, name: &str) -> Option<&PerformanceMetric> {
        self.metrics.get(name)
    }

    /// 获取所有性能指标 / Get All Performance Metrics
    pub fn get_all_metrics(&self) -> &HashMap<String, PerformanceMetric> {
        &self.metrics
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ownership_tracker() {
        let mut tracker = OwnershipTracker::new();

        tracker.record_ownership("owner1".to_string(), "String".to_string());
        tracker.record_access("owner1").unwrap();

        let stats = tracker.get_statistics();
        assert_eq!(stats.total_owners, 1);
        assert_eq!(stats.active_owners, 1);
    }

    #[test]
    fn test_borrow_tracker() {
        let mut tracker = BorrowTracker::new();

        tracker.record_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Immutable).unwrap();
        tracker.record_borrow_end("owner1", "borrower1").unwrap();

        let stats = tracker.get_statistics();
        assert_eq!(stats.total_borrows, 1);
        assert_eq!(stats.active_borrows, 0);
    }

    #[test]
    fn test_lifetime_tracker() {
        let mut tracker = LifetimeTracker::new();

        tracker.record_lifetime_start("'a".to_string(), "scope1".to_string());
        tracker.record_reference_association("'a").unwrap();
        tracker.record_lifetime_end("'a").unwrap();

        let stats = tracker.get_statistics();
        assert_eq!(stats.total_lifetimes, 1);
        assert_eq!(stats.active_lifetimes, 0);
    }

    #[test]
    fn test_ownership_system_manager() {
        let mut manager = OwnershipSystemManager::new();

        manager.ownership_tracker().record_ownership("owner1".to_string(), "String".to_string());
        manager.borrow_tracker().record_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Immutable).unwrap();
        manager.lifetime_tracker().record_lifetime_start("'a".to_string(), "scope1".to_string());

        let stats = manager.get_system_statistics();
        assert_eq!(stats.ownership.total_owners, 1);
        assert_eq!(stats.borrowing.total_borrows, 1);
        assert_eq!(stats.lifetime.total_lifetimes, 1);
    }
}
