use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, mpsc};
use tokio::time::sleep;

/// Raft 节点状态
/// Raft node status
#[derive(Debug, Clone, PartialEq)]
enum RaftState {
    Follower,
    Candidate,
    Leader,
}

/// Raft 日志条目
/// Raft
#[derive(Debug, Clone, Serialize, Deserialize)]
struct LogEntry {
    term: u64,
    index: u64,
    command: String,
    timestamp: u64,
}

/// Raft 节点
/// Raft node
struct RaftNode {
    id: String,
    state: Arc<RwLock<RaftState>>,
    current_term: Arc<RwLock<u64>>,
    voted_for: Arc<RwLock<Option<String>>>,
    log: Arc<RwLock<Vec<LogEntry>>>,
    commit_index: Arc<RwLock<u64>>,
    last_applied: Arc<RwLock<u64>>,

    // Leader 状态
    next_index: Arc<RwLock<HashMap<String, u64>>>,
    match_index: Arc<RwLock<HashMap<String, u64>>>,

    // 选举状态
    election_timeout: Duration,
    last_heartbeat: Arc<RwLock<Instant>>,

    // 网络通信
    peers: Arc<RwLock<Vec<String>>>,
    message_tx: mpsc::Sender<RaftMessage>,
}

/// Raft 消息类型
/// Raft type
#[derive(Debug, Clone)]
enum RaftMessage {
    StartElection { node_id: String },
    Heartbeat { from: String, to: String, term: u64 },
}

impl RaftNode {
    fn new(
        id: String,
        peers: Vec<String>,
        election_timeout: Duration,
    ) -> (Self, mpsc::Receiver<RaftMessage>) {
        let (message_tx, message_rx) = mpsc::channel(100);

        let node = Self {
            id: id.clone(),
            state: Arc::new(RwLock::new(RaftState::Follower)),
            current_term: Arc::new(RwLock::new(0)),
            voted_for: Arc::new(RwLock::new(None)),
            log: Arc::new(RwLock::new(Vec::new())),
            commit_index: Arc::new(RwLock::new(0)),
            last_applied: Arc::new(RwLock::new(0)),
            next_index: Arc::new(RwLock::new(HashMap::new())),
            match_index: Arc::new(RwLock::new(HashMap::new())),
            election_timeout,
            last_heartbeat: Arc::new(RwLock::new(Instant::now())),
            peers: Arc::new(RwLock::new(peers)),
            message_tx,
        };

        (node, message_rx)
    }

    /// 启动节点
    /// node
    async fn start(&self, message_rx: mpsc::Receiver<RaftMessage>) {
        println!("🚀 Raft 节点 {} 启动", self.id);

        // 启动选举定时器
        let election_timer = self.start_election_timer();

        // 启动消息处理循环
        let message_handler = self.handle_messages(message_rx);

        // 启动心跳发送器（如果是 Leader）
        let heartbeat_sender = self.start_heartbeat_sender();

        // 并发运行所有任务
        tokio::select! {
            _ = election_timer => {},
            _ = message_handler => {},
            _ = heartbeat_sender => {},
        }
    }

    /// 启动选举计时器
    /// election
    async fn start_election_timer(&self) {
        let state = self.state.clone();
        let current_term = self.current_term.clone();
        let voted_for = self.voted_for.clone();
        let election_timeout = self.election_timeout;
        let message_tx = self.message_tx.clone();
        let node_id = self.id.clone();

        tokio::spawn(async move {
            loop {
                tokio::time::sleep(election_timeout).await;

                let state_guard = state.read().await;
                let term_guard = current_term.read().await;
                let voted_guard = voted_for.read().await;

                if matches!(*state_guard, RaftState::Follower)
                    && voted_guard.is_none()
                    && *term_guard == 0
                {
                    // 超时，开始选举
                    drop(state_guard);
                    drop(term_guard);
                    drop(voted_guard);

                    let _ = message_tx
                        .send(RaftMessage::StartElection {
                            node_id: node_id.clone(),
                        })
                        .await;
                    break;
                }
            }
        });
    }

    /// 开始选举
    /// election
    async fn start_election(&self) {
        println!("🗳️  节点 {} 开始选举", self.id);

        // 转换为候选人状态
        {
            let mut state = self.state.write().await;
            *state = RaftState::Candidate;
        }

        // 增加任期
        {
            let mut term = self.current_term.write().await;
            *term += 1;
        }

        // 投票给自己
        {
            let mut voted_for = self.voted_for.write().await;
            *voted_for = Some(self.id.clone());
        }

        // 重置心跳时间
        {
            let mut last_heartbeat = self.last_heartbeat.write().await;
            *last_heartbeat = Instant::now();
        }

        // 发送投票请求给所有其他节点
        self.request_votes().await;
    }

    /// 请求投票
    async fn request_votes(&self) {
        let _term = *self.current_term.read().await;
        let _last_log_index = self.log.read().await.len() as u64;
        let _last_log_term = self
            .log
            .read()
            .await
            .last()
            .map(|entry| entry.term)
            .unwrap_or(0);

        let peers = self.peers.read().await;
        for peer_id in peers.iter() {
            if peer_id != &self.id {
                // 模拟发送消息（在实际实现中会通过网络发送）
                println!("📤 节点 {} 向节点 {} 发送投票请求", self.id, peer_id);

                // 模拟投票响应
                tokio::spawn({
                    let node = Arc::new(self.clone_for_task());
                    let peer_id = peer_id.clone();
                    async move {
                        sleep(Duration::from_millis(rand::random::<u64>() % 100 + 50)).await;
                        node.handle_vote_response(peer_id, _term, rand::random::<bool>())
                            .await;
                    }
                });
            }
        }
    }

    /// 处理投票响应
    async fn handle_vote_response(&self, from: String, term: u64, vote_granted: bool) {
        let current_term = *self.current_term.read().await;
        if term != current_term {
            return; // 过期的响应
        }

        if vote_granted {
            println!("✅ 节点 {} 获得来自 {} 的投票", self.id, from);
            // 检查是否获得多数票
            let _peers = self.peers.read().await;
            let _required_votes = (_peers.len() / 2) + 1;

            // 简化：假设总是能获得多数票
            if true {
                self.become_leader().await;
            }
        }
    }

    /// 成为 Leader
    async fn become_leader(&self) {
        println!("👑 节点 {} 成为 Leader", self.id);

        // 更新状态
        {
            let mut state = self.state.write().await;
            *state = RaftState::Leader;
        }

        // 初始化 Leader 状态
        let peers = self.peers.read().await;
        let mut next_index = self.next_index.write().await;
        let mut match_index = self.match_index.write().await;

        for peer_id in peers.iter() {
            if peer_id != &self.id {
                next_index.insert(peer_id.clone(), 1);
                match_index.insert(peer_id.clone(), 0);
            }
        }

        // 发送初始心跳
        self.send_heartbeat().await;
    }

    /// 发送心跳
    async fn send_heartbeat(&self) {
        let term = *self.current_term.read().await;
        let peers = self.peers.read().await;

        for peer_id in peers.iter() {
            if peer_id != &self.id {
                println!("💓 Leader {} 向节点 {} 发送心跳", self.id, peer_id);

                // 模拟心跳响应
                tokio::spawn({
                    let node = Arc::new(self.clone_for_task());
                    let peer_id = peer_id.clone();
                    async move {
                        sleep(Duration::from_millis(rand::random::<u64>() % 50 + 20)).await;
                        node.handle_heartbeat_response(peer_id, term, true).await;
                    }
                });
            }
        }
    }

    /// 处理心跳响应
    async fn handle_heartbeat_response(&self, from: String, term: u64, success: bool) {
        let current_term = *self.current_term.read().await;
        if term != current_term {
            return;
        }

        if success {
            // 更新匹配索引
            let mut match_index = self.match_index.write().await;
            if let Some(index) = match_index.get_mut(&from) {
                *index += 1;
            }
        }
    }

    /// 启动心跳发送器
    async fn start_heartbeat_sender(&self) {
        let state = self.state.clone();
        let current_term = self.current_term.clone();
        let peers = self.peers.clone();
        let message_tx = self.message_tx.clone();
        let node_id = self.id.clone();

        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(100)).await;

                let state_guard = state.read().await;
                if matches!(*state_guard, RaftState::Leader) {
                    drop(state_guard);

                    let peers_guard = peers.read().await;
                    for peer_id in peers_guard.iter() {
                        if peer_id != &node_id {
                            let _ = message_tx
                                .send(RaftMessage::Heartbeat {
                                    from: node_id.clone(),
                                    to: peer_id.clone(),
                                    term: *current_term.read().await,
                                })
                                .await;
                        }
                    }
                }
            }
        });
    }

    /// 处理消息
    async fn handle_messages(&self, mut message_rx: mpsc::Receiver<RaftMessage>) {
        while let Some(message) = message_rx.recv().await {
            match message {
                RaftMessage::StartElection { node_id } => {
                    if node_id == self.id {
                        self.start_election().await;
                    }
                }
                RaftMessage::Heartbeat { from, term, to } => {
                    if to == self.id {
                        self.handle_heartbeat(from, term).await;
                    }
                }
            }
        }
    }

    /// 处理心跳
    async fn handle_heartbeat(&self, from: String, term: u64) {
        let mut current_term = self.current_term.write().await;
        let mut state = self.state.write().await;
        let mut last_heartbeat = self.last_heartbeat.write().await;

        if term >= *current_term {
            *current_term = term;
            *state = RaftState::Follower;
            *last_heartbeat = Instant::now();

            println!("💓 节点 {} 收到来自 {} 的心跳", self.id, from);
        }
    }

    /// 为任务克隆节点引用
    /// tasknode reference
    fn clone_for_task(&self) -> Self {
        Self {
            id: self.id.clone(),
            state: Arc::clone(&self.state),
            current_term: Arc::clone(&self.current_term),
            voted_for: Arc::clone(&self.voted_for),
            log: Arc::clone(&self.log),
            commit_index: Arc::clone(&self.commit_index),
            last_applied: Arc::clone(&self.last_applied),
            next_index: Arc::clone(&self.next_index),
            match_index: Arc::clone(&self.match_index),
            election_timeout: self.election_timeout,
            last_heartbeat: Arc::clone(&self.last_heartbeat),
            peers: Arc::clone(&self.peers),
            message_tx: self.message_tx.clone(),
        }
    }

    /// 显示系统状态
    /// system status
    async fn show_system_status(&self) {
        let state = self.state.read().await.clone();
        let term = *self.current_term.read().await;
        let voted_for = self.voted_for.read().await.clone();
        let log_len = self.log.read().await.len();

        println!(
            "节点 {}: 状态={:?}, 任期={}, 投票给={:?}, 日志长度={}",
            self.id, state, term, voted_for, log_len
        );
    }
}

/// 分布式一致性系统
/// distributed system
struct ConsensusSystem {
    nodes: Vec<Arc<RaftNode>>,
}

impl ConsensusSystem {
    fn new(node_count: usize) -> Self {
        let mut nodes = Vec::new();

        // 创建节点
        for i in 0..node_count {
            let node_id = format!("node-{}", i);
            let peers: Vec<String> = (0..node_count).map(|j| format!("node-{}", j)).collect();

            let election_timeout = Duration::from_millis(1000 + (i * 100) as u64);
            let (node, _) = RaftNode::new(node_id, peers, election_timeout);

            nodes.push(Arc::new(node));
        }

        Self { nodes }
    }

    /// 启动系统
    /// system
    async fn start(&self) {
        println!("🚀 分布式一致性系统启动");
        println!("{}", "=".repeat(50));

        // 启动所有节点
        let mut handles = Vec::new();
        for node in &self.nodes {
            let node = Arc::clone(node);

            // 为每个节点创建新的消息通道
            let (_, message_rx) = mpsc::channel(100);

            let handle = tokio::spawn(async move {
                node.start(message_rx).await;
            });

            handles.push(handle);
        }

        // 等待一段时间观察系统运行
        sleep(Duration::from_secs(10)).await;

        // 显示系统状态
        self.show_system_status().await;

        println!("\n{}", "=".repeat(50));
        println!("🎯 分布式一致性示例完成");
    }

    /// 显示系统状态
    /// system status
    async fn show_system_status(&self) {
        println!("\n📊 系统状态:");
        for node in &self.nodes {
            node.show_system_status().await;
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 创建 3 节点的分布式一致性系统
    let system = ConsensusSystem::new(3);
    system.start().await;

    Ok(())
}
