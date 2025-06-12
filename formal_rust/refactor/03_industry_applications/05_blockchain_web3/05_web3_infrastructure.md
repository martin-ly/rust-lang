# 5.5 Web3基础设施 (Web3 Infrastructure)

## 概述

Web3基础设施为去中心化应用提供底层支持，包括P2P网络、分布式存储、身份管理和计算平台。本节将建立Web3基础设施的形式化模型，并提供Rust实现。

## 形式化定义

### 5.5.1 Web3基础设施定义

**定义 5.5.1** (Web3基础设施)
Web3基础设施是一个五元组 $WI = (N, S, I, C, P)$，其中：
- $N$ 是网络层
- $S$ 是存储层
- $I$ 是身份层
- $C$ 是计算层
- $P$ 是协议层

**定义 5.5.2** (P2P网络)
P2P网络是一个四元组 $P2P = (N, M, R, T)$，其中：
- $N$ 是节点集合
- $M$ 是消息集合
- $R$ 是路由算法
- $T$ 是传输协议

**定义 5.5.3** (分布式存储)
分布式存储是一个四元组 $DS = (N, D, R, A)$，其中：
- $N$ 是存储节点集合
- $D$ 是数据集合
- $R$ 是复制策略
- $A$ 是访问控制

## 核心定理

### 定理 5.5.1 (网络连通性)

**定理**: 对于P2P网络，如果节点度大于等于2，则网络是连通的：

$$degree(n) \geq 2 \Rightarrow connected(N)$$

### 定理 5.5.2 (存储可用性)

**定理**: 分布式存储的可用性满足：

$$A_{storage} = 1 - (1 - A_{node})^r$$

其中 $r$ 是复制因子，$A_{node}$ 是单个节点的可用性。

## Rust实现

### 5.5.1 P2P网络实现

```rust
use std::collections::{HashMap, HashSet};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

/// 节点ID
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct NodeId {
    pub value: [u8; 32],
}

impl NodeId {
    pub fn new() -> Self {
        let mut value = [0u8; 32];
        rand::thread_rng().fill(&mut value);
        Self { value }
    }
    
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        Self { value: bytes }
    }
    
    pub fn distance(&self, other: &NodeId) -> u32 {
        let mut distance = 0;
        for i in 0..32 {
            let xor = self.value[i] ^ other.value[i];
            distance += xor.count_ones();
        }
        distance
    }
}

/// P2P消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum P2PMessage {
    Ping { from: NodeId, timestamp: u64 },
    Pong { from: NodeId, timestamp: u64 },
    FindNode { from: NodeId, target: NodeId },
    FindNodeResponse { from: NodeId, nodes: Vec<NodeInfo> },
    Store { from: NodeId, key: Vec<u8>, value: Vec<u8> },
    Get { from: NodeId, key: Vec<u8> },
    GetResponse { from: NodeId, key: Vec<u8>, value: Option<Vec<u8>> },
}

/// 节点信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeInfo {
    pub id: NodeId,
    pub address: String,
    pub port: u16,
    pub last_seen: u64,
}

/// P2P节点
pub struct P2PNode {
    pub id: NodeId,
    pub address: String,
    pub port: u16,
    pub peers: Arc<Mutex<HashMap<NodeId, NodeInfo>>>,
    pub k_buckets: Arc<Mutex<Vec<KBucket>>>,
    pub message_sender: mpsc::Sender<P2PMessage>,
    pub message_receiver: mpsc::Receiver<P2PMessage>,
}

impl P2PNode {
    pub fn new(address: String, port: u16) -> Self {
        let (tx, rx) = mpsc::channel(1000);
        
        Self {
            id: NodeId::new(),
            address,
            port,
            peers: Arc::new(Mutex::new(HashMap::new())),
            k_buckets: Arc::new(Mutex::new(vec![KBucket::new(); 256])),
            message_sender: tx,
            message_receiver: rx,
        }
    }
    
    pub async fn start(&mut self) -> Result<(), Web3Error> {
        let listener = TcpListener::bind(format!("{}:{}", self.address, self.port))?;
        
        println!("P2P node started on {}:{}", self.address, self.port);
        println!("Node ID: {:?}", self.id);
        
        // 启动消息处理循环
        tokio::spawn(self.handle_messages());
        
        // 接受连接
        for stream in listener.incoming() {
            match stream {
                Ok(stream) => {
                    let node_id = self.id.clone();
                    let peers = self.peers.clone();
                    tokio::spawn(async move {
                        Self::handle_connection(stream, node_id, peers).await;
                    });
                }
                Err(e) => eprintln!("Connection error: {}", e),
            }
        }
        
        Ok(())
    }
    
    pub async fn ping(&self, target: &NodeInfo) -> Result<(), Web3Error> {
        let message = P2PMessage::Ping {
            from: self.id.clone(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };
        
        self.send_message(target, message).await?;
        Ok(())
    }
    
    pub async fn find_node(&self, target: &NodeId) -> Result<Vec<NodeInfo>, Web3Error> {
        let message = P2PMessage::FindNode {
            from: self.id.clone(),
            target: target.clone(),
        };
        
        // 发送到最近的k个节点
        let closest_nodes = self.get_closest_nodes(target, 8).await;
        
        for node in closest_nodes {
            self.send_message(&node, message.clone()).await?;
        }
        
        // 等待响应
        Ok(vec![]) // 简化实现
    }
    
    pub async fn store(&self, key: Vec<u8>, value: Vec<u8>) -> Result<(), Web3Error> {
        let message = P2PMessage::Store {
            from: self.id.clone(),
            key: key.clone(),
            value: value.clone(),
        };
        
        // 找到负责存储的节点
        let target_id = NodeId::from_bytes(key.try_into().unwrap());
        let closest_nodes = self.get_closest_nodes(&target_id, 3).await;
        
        for node in closest_nodes {
            self.send_message(&node, message.clone()).await?;
        }
        
        Ok(())
    }
    
    pub async fn get(&self, key: Vec<u8>) -> Result<Option<Vec<u8>>, Web3Error> {
        let message = P2PMessage::Get {
            from: self.id.clone(),
            key: key.clone(),
        };
        
        // 找到负责存储的节点
        let target_id = NodeId::from_bytes(key.try_into().unwrap());
        let closest_nodes = self.get_closest_nodes(&target_id, 8).await;
        
        for node in closest_nodes {
            self.send_message(&node, message.clone()).await?;
        }
        
        Ok(None) // 简化实现
    }
    
    async fn send_message(&self, target: &NodeInfo, message: P2PMessage) -> Result<(), Web3Error> {
        let mut stream = TcpStream::connect(format!("{}:{}", target.address, target.port)).await?;
        
        let message_bytes = bincode::serialize(&message)?;
        stream.write_all(&message_bytes).await?;
        
        Ok(())
    }
    
    async fn handle_connection(stream: TcpStream, node_id: NodeId, peers: Arc<Mutex<HashMap<NodeId, NodeInfo>>>) {
        // 处理接收到的消息
        let mut buffer = [0u8; 1024];
        
        loop {
            match stream.read(&mut buffer).await {
                Ok(n) if n > 0 => {
                    if let Ok(message) = bincode::deserialize::<P2PMessage>(&buffer[..n]) {
                        Self::process_message(message, &node_id, &peers).await;
                    }
                }
                _ => break,
            }
        }
    }
    
    async fn process_message(message: P2PMessage, node_id: &NodeId, peers: &Arc<Mutex<HashMap<NodeId, NodeInfo>>>) {
        match message {
            P2PMessage::Ping { from, timestamp } => {
                // 回复Pong
                let pong = P2PMessage::Pong {
                    from: node_id.clone(),
                    timestamp,
                };
                // 发送pong响应
            }
            P2PMessage::FindNode { from, target } => {
                // 查找最近的节点
                let mut peers_guard = peers.lock().unwrap();
                let mut closest_nodes = Vec::new();
                
                for (_, node_info) in peers_guard.iter() {
                    closest_nodes.push(node_info.clone());
                }
                
                // 按距离排序
                closest_nodes.sort_by(|a, b| {
                    a.id.distance(&target).cmp(&b.id.distance(&target))
                });
                
                let response = P2PMessage::FindNodeResponse {
                    from: node_id.clone(),
                    nodes: closest_nodes.into_iter().take(8).collect(),
                };
                // 发送响应
            }
            P2PMessage::Store { from, key, value } => {
                // 存储数据
                println!("Storing key: {:?}, value: {:?}", key, value);
            }
            P2PMessage::Get { from, key } => {
                // 获取数据
                let response = P2PMessage::GetResponse {
                    from: node_id.clone(),
                    key,
                    value: None, // 简化实现
                };
                // 发送响应
            }
            _ => {}
        }
    }
    
    async fn get_closest_nodes(&self, target: &NodeId, k: usize) -> Vec<NodeInfo> {
        let mut peers_guard = self.peers.lock().unwrap();
        let mut closest_nodes = Vec::new();
        
        for (_, node_info) in peers_guard.iter() {
            closest_nodes.push(node_info.clone());
        }
        
        // 按距离排序
        closest_nodes.sort_by(|a, b| {
            a.id.distance(target).cmp(&b.id.distance(target))
        });
        
        closest_nodes.into_iter().take(k).collect()
    }
    
    async fn handle_messages(&mut self) {
        while let Some(message) = self.message_receiver.recv().await {
            // 处理内部消息
            println!("Received message: {:?}", message);
        }
    }
}

/// K桶
#[derive(Debug, Clone)]
pub struct KBucket {
    pub nodes: Vec<NodeInfo>,
    pub max_size: usize,
}

impl KBucket {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            max_size: 20,
        }
    }
    
    pub fn add_node(&mut self, node: NodeInfo) {
        if self.nodes.len() < self.max_size {
            self.nodes.push(node);
        } else {
            // 替换最旧的节点
            self.nodes.remove(0);
            self.nodes.push(node);
        }
    }
    
    pub fn remove_node(&mut self, node_id: &NodeId) {
        self.nodes.retain(|node| node.id != *node_id);
    }
}
```

### 5.5.2 分布式存储实现

```rust
/// 分布式存储节点
pub struct StorageNode {
    pub id: NodeId,
    pub address: String,
    pub port: u16,
    pub data: Arc<Mutex<HashMap<Vec<u8>, StoredData>>>,
    pub replication_factor: usize,
}

impl StorageNode {
    pub fn new(address: String, port: u16, replication_factor: usize) -> Self {
        Self {
            id: NodeId::new(),
            address,
            port,
            data: Arc::new(Mutex::new(HashMap::new())),
            replication_factor,
        }
    }
    
    pub async fn store(&self, key: Vec<u8>, value: Vec<u8>) -> Result<(), Web3Error> {
        let stored_data = StoredData {
            value,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            checksum: self.calculate_checksum(&value),
        };
        
        let mut data_guard = self.data.lock().unwrap();
        data_guard.insert(key, stored_data);
        
        Ok(())
    }
    
    pub async fn retrieve(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Web3Error> {
        let data_guard = self.data.lock().unwrap();
        
        if let Some(stored_data) = data_guard.get(key) {
            // 验证校验和
            if stored_data.checksum == self.calculate_checksum(&stored_data.value) {
                Ok(Some(stored_data.value.clone()))
            } else {
                Err(Web3Error::DataCorruption)
            }
        } else {
            Ok(None)
        }
    }
    
    pub async fn delete(&self, key: &[u8]) -> Result<bool, Web3Error> {
        let mut data_guard = self.data.lock().unwrap();
        
        if data_guard.remove(key).is_some() {
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    pub async fn list_keys(&self) -> Vec<Vec<u8>> {
        let data_guard = self.data.lock().unwrap();
        data_guard.keys().cloned().collect()
    }
    
    fn calculate_checksum(&self, data: &[u8]) -> u32 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        hasher.finish() as u32
    }
}

/// 存储数据
#[derive(Debug, Clone)]
pub struct StoredData {
    pub value: Vec<u8>,
    pub timestamp: u64,
    pub checksum: u32,
}

/// 分布式存储系统
pub struct DistributedStorage {
    pub nodes: Vec<StorageNode>,
    pub replication_factor: usize,
}

impl DistributedStorage {
    pub fn new(replication_factor: usize) -> Self {
        Self {
            nodes: Vec::new(),
            replication_factor,
        }
    }
    
    pub fn add_node(&mut self, node: StorageNode) {
        self.nodes.push(node);
    }
    
    pub async fn store(&self, key: Vec<u8>, value: Vec<u8>) -> Result<(), Web3Error> {
        // 确定负责存储的节点
        let responsible_nodes = self.get_responsible_nodes(&key);
        
        // 复制到多个节点
        let mut success_count = 0;
        for node in responsible_nodes {
            if node.store(key.clone(), value.clone()).await.is_ok() {
                success_count += 1;
            }
        }
        
        if success_count >= self.replication_factor {
            Ok(())
        } else {
            Err(Web3Error::InsufficientReplication)
        }
    }
    
    pub async fn retrieve(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Web3Error> {
        // 从负责的节点获取数据
        let responsible_nodes = self.get_responsible_nodes(key);
        
        for node in responsible_nodes {
            if let Ok(Some(value)) = node.retrieve(key).await {
                return Ok(Some(value));
            }
        }
        
        Ok(None)
    }
    
    pub async fn delete(&self, key: &[u8]) -> Result<bool, Web3Error> {
        let responsible_nodes = self.get_responsible_nodes(key);
        let mut deleted = false;
        
        for node in responsible_nodes {
            if node.delete(key).await.unwrap_or(false) {
                deleted = true;
            }
        }
        
        Ok(deleted)
    }
    
    fn get_responsible_nodes(&self, key: &[u8]) -> Vec<&StorageNode> {
        // 简化的节点选择策略
        let key_hash = self.hash_key(key);
        let mut nodes = Vec::new();
        
        for i in 0..self.replication_factor {
            let index = (key_hash + i as u32) as usize % self.nodes.len();
            nodes.push(&self.nodes[index]);
        }
        
        nodes
    }
    
    fn hash_key(&self, key: &[u8]) -> u32 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as u32
    }
}
```

### 5.5.3 身份管理实现

```rust
/// 去中心化身份
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecentralizedIdentity {
    pub did: String,
    pub public_key: Vec<u8>,
    pub attributes: HashMap<String, String>,
    pub verifiable_credentials: Vec<VerifiableCredential>,
}

impl DecentralizedIdentity {
    pub fn new(public_key: Vec<u8>) -> Self {
        let did = format!("did:web3:{}", hex::encode(&public_key[..16]));
        
        Self {
            did,
            public_key,
            attributes: HashMap::new(),
            verifiable_credentials: Vec::new(),
        }
    }
    
    pub fn add_attribute(&mut self, key: String, value: String) {
        self.attributes.insert(key, value);
    }
    
    pub fn get_attribute(&self, key: &str) -> Option<&String> {
        self.attributes.get(key)
    }
    
    pub fn add_credential(&mut self, credential: VerifiableCredential) {
        self.verifiable_credentials.push(credential);
    }
    
    pub fn verify_credential(&self, credential_id: &str) -> bool {
        self.verifiable_credentials.iter()
            .any(|cred| cred.id == credential_id && cred.verify())
    }
}

/// 可验证凭证
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiableCredential {
    pub id: String,
    pub issuer: String,
    pub subject: String,
    pub claims: HashMap<String, String>,
    pub signature: Vec<u8>,
    pub expiration: u64,
}

impl VerifiableCredential {
    pub fn new(issuer: String, subject: String, claims: HashMap<String, String>) -> Self {
        let id = format!("vc:{}", uuid::Uuid::new_v4());
        
        Self {
            id,
            issuer,
            subject,
            claims,
            signature: Vec::new(),
            expiration: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs() + 365 * 24 * 60 * 60, // 1年有效期
        }
    }
    
    pub fn sign(&mut self, private_key: &[u8]) -> Result<(), Web3Error> {
        // 简化的签名实现
        let mut hasher = Sha256::new();
        hasher.update(&self.id.as_bytes());
        hasher.update(&self.issuer.as_bytes());
        hasher.update(&self.subject.as_bytes());
        
        for (key, value) in &self.claims {
            hasher.update(key.as_bytes());
            hasher.update(value.as_bytes());
        }
        
        let hash = hasher.finalize();
        self.signature = hash.to_vec();
        
        Ok(())
    }
    
    pub fn verify(&self) -> bool {
        // 简化的验证实现
        let mut hasher = Sha256::new();
        hasher.update(&self.id.as_bytes());
        hasher.update(&self.issuer.as_bytes());
        hasher.update(&self.subject.as_bytes());
        
        for (key, value) in &self.claims {
            hasher.update(key.as_bytes());
            hasher.update(value.as_bytes());
        }
        
        let expected_hash = hasher.finalize();
        self.signature == expected_hash.to_vec()
    }
    
    pub fn is_expired(&self) -> bool {
        let current_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        current_time > self.expiration
    }
}

/// 身份管理系统
pub struct IdentityManager {
    pub identities: HashMap<String, DecentralizedIdentity>,
    pub issuers: HashMap<String, Vec<u8>>, // 发行者公钥
}

impl IdentityManager {
    pub fn new() -> Self {
        Self {
            identities: HashMap::new(),
            issuers: HashMap::new(),
        }
    }
    
    pub fn create_identity(&mut self, public_key: Vec<u8>) -> String {
        let identity = DecentralizedIdentity::new(public_key);
        let did = identity.did.clone();
        self.identities.insert(did.clone(), identity);
        did
    }
    
    pub fn get_identity(&self, did: &str) -> Option<&DecentralizedIdentity> {
        self.identities.get(did)
    }
    
    pub fn update_identity(&mut self, did: &str, attributes: HashMap<String, String>) -> Result<(), Web3Error> {
        if let Some(identity) = self.identities.get_mut(did) {
            for (key, value) in attributes {
                identity.add_attribute(key, value);
            }
            Ok(())
        } else {
            Err(Web3Error::IdentityNotFound)
        }
    }
    
    pub fn issue_credential(&mut self, issuer: &str, subject: &str, claims: HashMap<String, String>) -> Result<VerifiableCredential, Web3Error> {
        let mut credential = VerifiableCredential::new(
            issuer.to_string(),
            subject.to_string(),
            claims,
        );
        
        // 使用发行者私钥签名（简化实现）
        let issuer_private_key = vec![0u8; 32]; // 实际应该从安全存储获取
        credential.sign(&issuer_private_key)?;
        
        Ok(credential)
    }
    
    pub fn verify_credential(&self, credential: &VerifiableCredential) -> bool {
        if credential.is_expired() {
            return false;
        }
        
        credential.verify()
    }
    
    pub fn register_issuer(&mut self, issuer_id: String, public_key: Vec<u8>) {
        self.issuers.insert(issuer_id, public_key);
    }
}
```

### 5.5.4 错误处理

```rust
/// Web3基础设施错误
#[derive(Debug, thiserror::Error)]
pub enum Web3Error {
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Storage error: {0}")]
    StorageError(String),
    
    #[error("Identity not found")]
    IdentityNotFound,
    
    #[error("Invalid credential")]
    InvalidCredential,
    
    #[error("Data corruption")]
    DataCorruption,
    
    #[error("Insufficient replication")]
    InsufficientReplication,
    
    #[error("Node not found")]
    NodeNotFound,
    
    #[error("Connection failed")]
    ConnectionFailed,
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

## 应用示例

### 5.5.1 P2P网络示例

```rust
pub async fn p2p_network_example() {
    let mut node1 = P2PNode::new("127.0.0.1".to_string(), 8080);
    let mut node2 = P2PNode::new("127.0.0.1".to_string(), 8081);
    
    // 启动节点
    tokio::spawn(async move {
        if let Err(e) = node1.start().await {
            eprintln!("Node1 error: {}", e);
        }
    });
    
    tokio::spawn(async move {
        if let Err(e) = node2.start().await {
            eprintln!("Node2 error: {}", e);
        }
    });
    
    // 等待节点启动
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    // 存储数据
    node1.store(vec![1, 2, 3], vec![4, 5, 6]).await.unwrap();
    
    // 获取数据
    let value = node2.get(vec![1, 2, 3]).await.unwrap();
    println!("Retrieved value: {:?}", value);
}
```

### 5.5.2 分布式存储示例

```rust
pub async fn distributed_storage_example() {
    let mut storage = DistributedStorage::new(3);
    
    // 添加存储节点
    for i in 0..5 {
        let node = StorageNode::new(
            format!("127.0.0.1:{}", 9000 + i),
            9000 + i,
            3,
        );
        storage.add_node(node);
    }
    
    // 存储数据
    let key = b"hello".to_vec();
    let value = b"world".to_vec();
    
    match storage.store(key.clone(), value).await {
        Ok(()) => println!("Data stored successfully"),
        Err(e) => eprintln!("Storage failed: {}", e),
    }
    
    // 检索数据
    match storage.retrieve(&key).await {
        Ok(Some(retrieved_value)) => {
            println!("Retrieved: {:?}", String::from_utf8_lossy(&retrieved_value));
        }
        Ok(None) => println!("Data not found"),
        Err(e) => eprintln!("Retrieval failed: {}", e),
    }
}
```

### 5.5.3 身份管理示例

```rust
pub fn identity_management_example() {
    let mut identity_manager = IdentityManager::new();
    
    // 创建身份
    let public_key = vec![1u8; 32];
    let did = identity_manager.create_identity(public_key);
    println!("Created identity: {}", did);
    
    // 更新属性
    let mut attributes = HashMap::new();
    attributes.insert("name".to_string(), "Alice".to_string());
    attributes.insert("email".to_string(), "alice@example.com".to_string());
    
    match identity_manager.update_identity(&did, attributes) {
        Ok(()) => println!("Identity updated"),
        Err(e) => eprintln!("Update failed: {}", e),
    }
    
    // 发行凭证
    let mut claims = HashMap::new();
    claims.insert("degree".to_string(), "Bachelor of Science".to_string());
    claims.insert("university".to_string(), "MIT".to_string());
    
    match identity_manager.issue_credential("university", &did, claims) {
        Ok(credential) => {
            println!("Credential issued: {}", credential.id);
            
            // 验证凭证
            if identity_manager.verify_credential(&credential) {
                println!("Credential verified successfully");
            } else {
                println!("Credential verification failed");
            }
        }
        Err(e) => eprintln!("Credential issuance failed: {}", e),
    }
}
```

## 性能分析

### 5.5.1 网络性能分析

**定理 5.5.3** (P2P网络性能)

P2P网络的消息传递复杂度为：

$$T_{message} = O(\log n)$$

其中 $n$ 是网络中的节点数量。

### 5.5.2 存储性能分析

**定理 5.5.4** (分布式存储性能)

分布式存储的读写复杂度为：

$$T_{read} = O(1), T_{write} = O(r)$$

其中 $r$ 是复制因子。

## 总结

本节建立了Web3基础设施的完整形式化模型，包括：

1. **形式化定义**: Web3基础设施、P2P网络、分布式存储的定义
2. **核心定理**: 网络连通性、存储可用性定理
3. **Rust实现**: 完整的P2P网络、分布式存储、身份管理实现
4. **应用示例**: 实际的基础设施使用示例
5. **性能分析**: 网络和存储性能分析

Web3基础设施为去中心化应用提供了底层支持，是实现Web3愿景的重要基础。 