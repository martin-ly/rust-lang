use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

/// 分布式系统一致性级别
///
/// 基于CAP定理和PACELC定理，提供不同的一致性保证
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[derive(Default)]
pub enum ConsistencyLevel {
    /// 强一致性 - 所有节点立即看到相同的数据
    Strong,
    /// 线性一致性 - 所有操作都有全局顺序
    Linearizable,
    /// 顺序一致性 - 每个节点的操作保持顺序
    Sequential,
    /// 因果一致性 - 保持因果关系
    Causal,
    /// 最终一致性 - 最终所有节点会收敛到相同状态
    #[default]
    Eventual,
    /// 会话一致性 - 在同一会话内保持一致性
    Session,
    /// 单调读一致性 - 读操作不会返回比之前更旧的数据
    MonotonicRead,
    /// 单调写一致性 - 写操作按顺序执行
    MonotonicWrite,
    /// 法定人数一致性 - 基于多数节点的确认
    Quorum,
}


impl ConsistencyLevel {
    /// 获取一致性级别的描述
    pub fn description(&self) -> &'static str {
        match self {
            ConsistencyLevel::Strong => "强一致性：所有节点立即看到相同的数据",
            ConsistencyLevel::Linearizable => "线性一致性：所有操作都有全局顺序",
            ConsistencyLevel::Sequential => "顺序一致性：每个节点的操作保持顺序",
            ConsistencyLevel::Causal => "因果一致性：保持因果关系",
            ConsistencyLevel::Eventual => "最终一致性：最终所有节点会收敛到相同状态",
            ConsistencyLevel::Session => "会话一致性：在同一会话内保持一致性",
            ConsistencyLevel::MonotonicRead => "单调读一致性：读操作不会返回比之前更旧的数据",
            ConsistencyLevel::MonotonicWrite => "单调写一致性：写操作按顺序执行",
            ConsistencyLevel::Quorum => "法定人数一致性：基于多数节点的确认",
        }
    }

    /// 检查是否支持分区容忍性
    pub fn supports_partition_tolerance(&self) -> bool {
        match self {
            ConsistencyLevel::Strong | ConsistencyLevel::Linearizable => false,
            _ => true,
        }
    }

    /// 检查是否支持高可用性
    pub fn supports_high_availability(&self) -> bool {
        match self {
            ConsistencyLevel::Strong | ConsistencyLevel::Linearizable => false,
            _ => true,
        }
    }
}

/// CAP定理权衡策略
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[derive(Default)]
pub enum CAPStrategy {
    /// 一致性优先 (CP) - 牺牲可用性保证一致性
    ConsistencyPartition,
    /// 可用性优先 (AP) - 牺牲一致性保证可用性
    AvailabilityPartition,
    /// 平衡策略 - 在一致性和可用性之间动态权衡
    #[default]
    Balanced,
}


impl CAPStrategy {
    /// 根据网络分区状态选择一致性级别
    pub fn select_consistency_level(&self, is_partitioned: bool) -> ConsistencyLevel {
        match (self, is_partitioned) {
            (CAPStrategy::ConsistencyPartition, _) => ConsistencyLevel::Strong,
            (CAPStrategy::AvailabilityPartition, _) => ConsistencyLevel::Eventual,
            (CAPStrategy::Balanced, true) => ConsistencyLevel::Causal,
            (CAPStrategy::Balanced, false) => ConsistencyLevel::Linearizable,
        }
    }
}

/// 因果一致性向量时钟
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorClock {
    clocks: HashMap<String, u64>,
}

impl VectorClock {
    /// 创建新的向量时钟
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }

    /// 为指定节点增加时钟值
    pub fn increment(&mut self, node_id: &str) {
        let entry = self.clocks.entry(node_id.to_string()).or_insert(0);
        *entry += 1;
    }

    /// 更新向量时钟（取最大值）
    pub fn update(&mut self, other: &VectorClock) {
        for (node_id, clock_value) in &other.clocks {
            let entry = self.clocks.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(*clock_value);
        }
    }

    /// 检查是否在因果关系上先于另一个向量时钟
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        let mut strictly_less = false;

        for (node_id, &self_clock) in &self.clocks {
            let other_clock = other.clocks.get(node_id).unwrap_or(&0);
            if self_clock > *other_clock {
                return false;
            }
            if self_clock < *other_clock {
                strictly_less = true;
            }
        }

        // 检查是否有其他节点在other中存在但在self中不存在
        for node_id in other.clocks.keys() {
            if !self.clocks.contains_key(node_id) {
                strictly_less = true;
            }
        }

        strictly_less
    }

    /// 检查是否并发（既不在前也不在后，且不相等）
    pub fn is_concurrent(&self, other: &VectorClock) -> bool {
        !self.happens_before(other) && !other.happens_before(self) && !self.is_equal(other)
    }

    /// 检查两个向量时钟是否相等
    pub fn is_equal(&self, other: &VectorClock) -> bool {
        if self.clocks.len() != other.clocks.len() {
            return false;
        }

        for (node_id, &self_clock) in &self.clocks {
            let other_clock = other.clocks.get(node_id).unwrap_or(&0);
            if self_clock != *other_clock {
                return false;
            }
        }

        true
    }
}

impl Default for VectorClock {
    fn default() -> Self {
        Self::new()
    }
}

/// 会话一致性管理器
#[derive(Debug, Clone)]
pub struct SessionConsistencyManager {
    sessions: HashMap<String, SessionInfo>,
}

#[derive(Debug, Clone)]
struct SessionInfo {
    last_read_version: Option<VectorClock>,
    last_write_version: Option<VectorClock>,
    created_at: SystemTime,
}

impl SessionConsistencyManager {
    /// 创建新的会话管理器
    pub fn new() -> Self {
        Self {
            sessions: HashMap::new(),
        }
    }

    /// 创建新会话
    pub fn create_session(&mut self, session_id: String) {
        self.sessions.insert(
            session_id,
            SessionInfo {
                last_read_version: None,
                last_write_version: None,
                created_at: SystemTime::now(),
            },
        );
    }

    /// 更新会话的读版本
    pub fn update_read_version(&mut self, session_id: &str, version: VectorClock) {
        if let Some(session) = self.sessions.get_mut(session_id) {
            session.last_read_version = Some(version);
        }
    }

    /// 更新会话的写版本
    pub fn update_write_version(&mut self, session_id: &str, version: VectorClock) {
        if let Some(session) = self.sessions.get_mut(session_id) {
            session.last_write_version = Some(version);
        }
    }

    /// 检查读操作是否满足会话一致性
    pub fn can_read(&self, session_id: &str, current_version: &VectorClock) -> bool {
        if let Some(session) = self.sessions.get(session_id)
            && let Some(ref last_read) = session.last_read_version {
                return !current_version.happens_before(last_read);
            }
        true
    }

    /// 检查写操作是否满足会话一致性
    pub fn can_write(&self, session_id: &str, current_version: &VectorClock) -> bool {
        if let Some(session) = self.sessions.get(session_id)
            && let Some(ref last_write) = session.last_write_version {
                return !current_version.happens_before(last_write);
            }
        true
    }

    /// 清理过期会话
    pub fn cleanup_expired_sessions(&mut self, max_age: Duration) {
        let now = SystemTime::now();
        self.sessions.retain(|_, session| {
            now.duration_since(session.created_at)
                .unwrap_or(Duration::from_secs(0))
                < max_age
        });
    }
}

impl Default for SessionConsistencyManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 单调一致性管理器
#[derive(Debug, Clone)]
pub struct MonotonicConsistencyManager {
    read_versions: HashMap<String, VectorClock>,
    write_versions: HashMap<String, VectorClock>,
}

impl MonotonicConsistencyManager {
    /// 创建新的单调一致性管理器
    pub fn new() -> Self {
        Self {
            read_versions: HashMap::new(),
            write_versions: HashMap::new(),
        }
    }

    /// 检查单调读一致性
    pub fn check_monotonic_read(&mut self, client_id: &str, version: &VectorClock) -> bool {
        if let Some(last_read) = self.read_versions.get(client_id)
            && version.happens_before(last_read) {
                return false; // 违反了单调读一致性
            }
        self.read_versions
            .insert(client_id.to_string(), version.clone());
        true
    }

    /// 检查单调写一致性
    pub fn check_monotonic_write(&mut self, client_id: &str, version: &VectorClock) -> bool {
        if let Some(last_write) = self.write_versions.get(client_id)
            && version.happens_before(last_write) {
                return false; // 违反了单调写一致性
            }
        self.write_versions
            .insert(client_id.to_string(), version.clone());
        true
    }
}

impl Default for MonotonicConsistencyManager {
    fn default() -> Self {
        Self::new()
    }
}
