# 15.6 网络协议栈

## 目录

- [15.6 网络协议栈](#156-网络协议栈)
  - [目录](#目录)
  - [15.6.1 P2P协议设计](#1561-p2p协议设计)
  - [15.6.2 节点发现协议](#1562-节点发现协议)
  - [15.6.3 区块传播协议](#1563-区块传播协议)
  - [15.6.4 交易广播协议](#1564-交易广播协议)
  - [15.6.5 网络分区处理](#1565-网络分区处理)
    - [与 Rust 的语义映射（补充）](#与-rust-的语义映射补充)
    - [练习与思考](#练习与思考)
    - [快速导航](#快速导航)
  - [协议安全测试矩阵与门禁](#协议安全测试矩阵与门禁)

## 15.6.1 P2P协议设计

**定义 15.6.1** (P2P协议)
P2P协议定义了区块链节点间的通信规则和消息格式。

**协议层次**：

```rust
pub struct P2PProtocol {
    application_layer: ApplicationLayer,
    transport_layer: TransportLayer,
    network_layer: NetworkLayer,
    data_link_layer: DataLinkLayer,
}

pub struct ApplicationLayer {
    message_handler: MessageHandler,
    protocol_version: ProtocolVersion,
}

pub struct TransportLayer {
    connection_manager: ConnectionManager,
    message_ordering: MessageOrdering,
}

pub struct NetworkLayer {
    routing_table: RoutingTable,
    address_resolution: AddressResolution,
}

pub struct DataLinkLayer {
    frame_handler: FrameHandler,
    error_detection: ErrorDetection,
}

impl P2PProtocol {
    pub async fn send_message(&self, peer: &PeerId, message: Message) -> Result<(), ProtocolError> {
        let serialized = self.serialize_message(message)?;
        let frame = self.data_link_layer.create_frame(serialized);
        self.network_layer.route_message(peer, frame).await?;
        Ok(())
    }
    
    pub async fn receive_message(&self) -> Result<Message, ProtocolError> {
        let frame = self.data_link_layer.receive_frame().await?;
        let serialized = self.data_link_layer.extract_payload(frame)?;
        let message = self.deserialize_message(serialized)?;
        Ok(message)
    }
}
```

## 15.6.2 节点发现协议

**定义 15.6.2** (节点发现)
节点发现协议帮助新节点找到网络中的其他节点并建立连接。

**发现机制**：

```rust
pub struct NodeDiscovery {
    bootstrap_nodes: Vec<BootstrapNode>,
    peer_table: PeerTable,
    discovery_algorithm: DiscoveryAlgorithm,
}

pub struct BootstrapNode {
    address: SocketAddr,
    public_key: PublicKey,
    last_seen: SystemTime,
}

pub struct PeerTable {
    buckets: Vec<PeerBucket>,
    max_peers_per_bucket: usize,
}

pub struct PeerBucket {
    peers: Vec<Peer>,
    last_updated: SystemTime,
}

impl NodeDiscovery {
    pub async fn discover_peers(&mut self) -> Result<Vec<Peer>, DiscoveryError> {
        let mut discovered_peers = Vec::new();
        
        // 从引导节点获取初始对等节点
        for bootstrap_node in &self.bootstrap_nodes {
            let peers = self.query_bootstrap_node(bootstrap_node).await?;
            discovered_peers.extend(peers);
        }
        
        // 使用Kademlia算法发现更多对等节点
        let kademlia_peers = self.discovery_algorithm.discover_peers().await?;
        discovered_peers.extend(kademlia_peers);
        
        // 更新对等节点表
        for peer in discovered_peers {
            self.peer_table.add_peer(peer);
        }
        
        Ok(self.peer_table.get_all_peers())
    }
    
    async fn query_bootstrap_node(&self, bootstrap_node: &BootstrapNode) -> Result<Vec<Peer>, DiscoveryError> {
        // 实现引导节点查询逻辑
        Ok(vec![])
    }
}
```

## 15.6.3 区块传播协议

**定义 15.6.3** (区块传播)
区块传播协议确保新区块能够快速、可靠地传播到整个网络。

**传播策略**：

```rust
pub struct BlockPropagation {
    block_cache: BlockCache,
    propagation_strategy: PropagationStrategy,
    duplicate_detection: DuplicateDetection,
}

pub struct BlockCache {
    recent_blocks: HashMap<BlockHash, Block>,
    cache_size: usize,
}

pub enum PropagationStrategy {
    Flooding,           // 洪泛传播
    Selective,          // 选择性传播
    Adaptive,           // 自适应传播
}

impl BlockPropagation {
    pub async fn propagate_block(&mut self, block: Block) -> Result<(), PropagationError> {
        let block_hash = block.hash();
        
        // 检查是否已经传播过
        if self.duplicate_detection.is_duplicate(&block_hash) {
            return Ok(());
        }
        
        // 缓存区块
        self.block_cache.cache_block(block.clone());
        
        // 根据策略传播区块
        match self.propagation_strategy {
            PropagationStrategy::Flooding => {
                self.flood_propagate(block).await
            }
            PropagationStrategy::Selective => {
                self.selective_propagate(block).await
            }
            PropagationStrategy::Adaptive => {
                self.adaptive_propagate(block).await
            }
        }
    }
    
    async fn flood_propagate(&self, block: Block) -> Result<(), PropagationError> {
        // 向所有连接的节点传播区块
        for peer in self.get_connected_peers() {
            peer.send_block(block.clone()).await?;
        }
        Ok(())
    }
    
    async fn selective_propagate(&self, block: Block) -> Result<(), PropagationError> {
        // 只向特定的节点传播区块
        let selected_peers = self.select_peers_for_propagation();
        for peer in selected_peers {
            peer.send_block(block.clone()).await?;
        }
        Ok(())
    }
}
```

## 15.6.4 交易广播协议

**定义 15.6.4** (交易广播)
交易广播协议负责将新交易快速传播到网络中的其他节点。

**广播机制**：

```rust
pub struct TransactionBroadcast {
    transaction_pool: TransactionPool,
    broadcast_strategy: BroadcastStrategy,
    transaction_filter: TransactionFilter,
}

pub struct TransactionPool {
    pending_transactions: HashMap<TxHash, Transaction>,
    confirmed_transactions: HashSet<TxHash>,
}

pub enum BroadcastStrategy {
    Immediate,          // 立即广播
    Batched,           // 批量广播
    Prioritized,       // 优先级广播
}

impl TransactionBroadcast {
    pub async fn broadcast_transaction(&mut self, transaction: Transaction) -> Result<(), BroadcastError> {
        let tx_hash = transaction.hash();
        
        // 检查交易是否有效
        if !self.transaction_filter.is_valid(&transaction) {
            return Err(BroadcastError::InvalidTransaction);
        }
        
        // 添加到交易池
        self.transaction_pool.add_transaction(transaction.clone());
        
        // 根据策略广播交易
        match self.broadcast_strategy {
            BroadcastStrategy::Immediate => {
                self.immediate_broadcast(transaction).await
            }
            BroadcastStrategy::Batched => {
                self.batched_broadcast(transaction).await
            }
            BroadcastStrategy::Prioritized => {
                self.prioritized_broadcast(transaction).await
            }
        }
    }
    
    async fn immediate_broadcast(&self, transaction: Transaction) -> Result<(), BroadcastError> {
        // 立即向所有节点广播交易
        for peer in self.get_connected_peers() {
            peer.send_transaction(transaction.clone()).await?;
        }
        Ok(())
    }
    
    async fn batched_broadcast(&mut self, transaction: Transaction) -> Result<(), BroadcastError> {
        // 将交易添加到批量广播队列
        self.add_to_batch(transaction);
        
        // 如果批量大小达到阈值，则广播整个批量
        if self.batch_size() >= self.batch_threshold() {
            self.broadcast_batch().await?;
        }
        
        Ok(())
    }
}
```

## 15.6.5 网络分区处理

**定义 15.6.5** (网络分区)
网络分区处理机制确保在网络分割时系统能够正确运行和恢复。

**分区检测**：

```rust
pub struct NetworkPartitionHandler {
    partition_detector: PartitionDetector,
    consensus_manager: ConsensusManager,
    recovery_strategy: RecoveryStrategy,
}

pub struct PartitionDetector {
    heartbeat_interval: Duration,
    timeout_threshold: Duration,
    node_status: HashMap<NodeId, NodeStatus>,
}

pub enum RecoveryStrategy {
    Automatic,          // 自动恢复
    Manual,            // 手动恢复
    Hybrid,            // 混合恢复
}

impl NetworkPartitionHandler {
    pub async fn detect_partitions(&mut self) -> Result<Vec<Partition>, PartitionError> {
        let mut partitions = Vec::new();
        let mut visited = HashSet::new();
        
        for node_id in self.partition_detector.node_status.keys() {
            if !visited.contains(node_id) {
                let partition = self.dfs_partition(*node_id, &mut visited).await?;
                if partition.len() > 1 {
                    partitions.push(partition);
                }
            }
        }
        
        Ok(partitions)
    }
    
    async fn dfs_partition(&self, start_node: NodeId, visited: &mut HashSet<NodeId>) -> Result<Vec<NodeId>, PartitionError> {
        let mut partition = Vec::new();
        let mut stack = vec![start_node];
        
        while let Some(node_id) = stack.pop() {
            if visited.insert(node_id) {
                partition.push(node_id);
                
                // 获取节点的邻居
                let neighbors = self.get_node_neighbors(node_id).await?;
                for neighbor in neighbors {
                    if !visited.contains(&neighbor) {
                        stack.push(neighbor);
                    }
                }
            }
        }
        
        Ok(partition)
    }
    
    pub async fn handle_partition(&mut self, partition: &Partition) -> Result<(), PartitionError> {
        match self.recovery_strategy {
            RecoveryStrategy::Automatic => {
                self.automatic_recovery(partition).await
            }
            RecoveryStrategy::Manual => {
                self.manual_recovery(partition).await
            }
            RecoveryStrategy::Hybrid => {
                self.hybrid_recovery(partition).await
            }
        }
    }
}
```

---

**结论**：网络协议栈为区块链系统提供了可靠、高效的通信基础设施。

### 与 Rust 的语义映射（补充）

- P2P 协议 ↔ `libp2p`/`quinn`/自研 RPC；消息用 `serde` 编解码
- 发现/路由 ↔ Kademlia 实现与路由表维护；健康检查与打点
- 传输语义 ↔ 幂等/重试/超时，`tower` 中间件抽象

### 练习与思考

1. 实现最小节点发现（Kademlia 子集），在本地多进程跑通发现/连接/心跳。
2. 对比 Flooding/Selective/Adaptive 三种区块传播策略的延迟与带宽消耗，给出实验报告。
3. 设计交易广播的优先级与批量策略，在高负载下保持尾延迟稳定。

### 快速导航

- 区块链理论：`01_blockchain_theory.md`
- 共识机制：`03_consensus_mechanisms.md`
- 分布式系统FAQ：`../../../crates/c20_distributed/docs/FAQ.md`

---

## 协议安全测试矩阵与门禁

- 基线门禁
  - 格式/静态：fmt/clippy -D warnings、deny/audit（许可证/漏洞）
  - 互操作：版本/握手能力协商；不兼容变更列入升级指引
- 握手与密钥轮换
  - 握手不变量：挑战-应答、重放保护、协商失败显式错误
  - 密钥轮换：有效期/重协商流程/KAT；旧会话清理
- 消息与抗 DoS
  - 帧长/速率/并发连接上限；洪泛与畸形帧丢弃
  - 去重与重传策略；反压（backpressure）与优先级
- 测试矩阵（摘要）

| 维度 | 场景 | 期望 | 工具 |
|---|---|---|---|
| 握手 | 协商失败/重放 | 拒绝且记录 | 单元/属性 |
| 编解码 | 畸形/边界帧 | 不崩溃/拒绝 | fuzz |
| 传播 | 洪泛/掉线 | 稳定/限流 | 压测/仿真 |
| 轮换 | 密钥到期 | 平滑重协商 | KAT/集成 |
