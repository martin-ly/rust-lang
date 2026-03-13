//! 区块链异步演示
//!
//! 本示例展示了异步编程在区块链应用中的使用：
//! - 异步交易处理
//! - 区块验证和挖矿
//! - 智能合约执行
//! - 共识机制
//! - 网络同步
//! - 钱包管理
//! - 挖矿池
//! - 区块链浏览器
//!
//! 运行方式：
//! ```bash
//! cargo run --example blockchain_async_demo
//! ```
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, VecDeque};
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::RwLock;
use tokio::time::sleep;
use uuid::Uuid;

/// 交易
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub id: String,
    pub from: String,
    pub to: String,
    pub amount: u64,
    pub fee: u64,
    pub timestamp: SystemTime,
    pub signature: String,
    pub data: Option<Vec<u8>>,
}

/// 区块
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    pub index: u64,
    pub previous_hash: String,
    pub timestamp: SystemTime,
    pub transactions: Vec<Transaction>,
    pub nonce: u64,
    pub hash: String,
    pub merkle_root: String,
    pub difficulty: u32,
}

/// 区块链
pub struct Blockchain {
    blocks: Arc<RwLock<VecDeque<Block>>>,
    pending_transactions: Arc<RwLock<VecDeque<Transaction>>>,
    accounts: Arc<RwLock<HashMap<String, u64>>>,
    difficulty: u32,
    mining_reward: u64,
}

impl Blockchain {
    pub async fn new(difficulty: u32, mining_reward: u64) -> Self {
        let blockchain = Self {
            blocks: Arc::new(RwLock::new(VecDeque::new())),
            pending_transactions: Arc::new(RwLock::new(VecDeque::new())),
            accounts: Arc::new(RwLock::new(HashMap::new())),
            difficulty,
            mining_reward,
        };

        // 创建创世区块
        blockchain.create_genesis_block().await;
        blockchain
    }

    async fn create_genesis_block(&self) {
        let genesis_block = Block {
            index: 0,
            previous_hash: "0".to_string(),
            timestamp: SystemTime::now(),
            transactions: vec![],
            nonce: 0,
            hash: "genesis".to_string(),
            merkle_root: "0".to_string(),
            difficulty: self.difficulty,
        };

        let mut blocks = self.blocks.write().await;
        blocks.push_back(genesis_block);
    }

    pub async fn add_transaction(&self, transaction: Transaction) -> Result<()> {
        // 验证交易
        if !self.validate_transaction(&transaction).await {
            return Err(anyhow::anyhow!("交易验证失败"));
        }

        let mut pending = self.pending_transactions.write().await;
        pending.push_back(transaction);
        Ok(())
    }

    async fn validate_transaction(&self, transaction: &Transaction) -> bool {
        let accounts = self.accounts.read().await;
        let balance = accounts.get(&transaction.from).copied().unwrap_or(0);

        // 检查余额是否足够
        balance >= transaction.amount + transaction.fee
    }

    pub async fn mine_block(&self, miner_address: String) -> Result<Block> {
        let mut pending = self.pending_transactions.write().await;
        let mut accounts = self.accounts.write().await;
        let mut blocks = self.blocks.write().await;

        if pending.is_empty() {
            return Err(anyhow::anyhow!("没有待处理的交易"));
        }

        // 获取上一个区块
        let previous_block = blocks.back().unwrap();
        let index = previous_block.index + 1;
        let previous_hash = previous_block.hash.clone();

        // 创建挖矿奖励交易
        let mining_reward_tx = Transaction {
            id: Uuid::new_v4().to_string(),
            from: "system".to_string(),
            to: miner_address.clone(),
            amount: self.mining_reward,
            fee: 0,
            timestamp: SystemTime::now(),
            signature: "mining_reward".to_string(),
            data: None,
        };

        // 准备区块中的交易
        let mut block_transactions = vec![mining_reward_tx];
        let mut tx_count = 0;
        let max_transactions = 10;

        while let Some(tx) = pending.pop_front() {
            block_transactions.push(tx);
            tx_count += 1;
            if tx_count >= max_transactions {
                break;
            }
        }

        // 计算 Merkle 根
        let merkle_root = self.calculate_merkle_root(&block_transactions);

        // 挖矿
        let (nonce, hash) = self
            .mine_block_hash(index, &previous_hash, &merkle_root)
            .await;

        let new_block = Block {
            index,
            previous_hash,
            timestamp: SystemTime::now(),
            transactions: block_transactions.clone(),
            nonce,
            hash,
            merkle_root,
            difficulty: self.difficulty,
        };

        // 更新账户余额
        for tx in &block_transactions {
            if tx.from != "system" {
                let from_balance = accounts.get(&tx.from).copied().unwrap_or(0);
                accounts.insert(
                    tx.from.clone(),
                    from_balance.saturating_sub(tx.amount + tx.fee),
                );
            }

            let to_balance = accounts.get(&tx.to).copied().unwrap_or(0);
            accounts.insert(tx.to.clone(), to_balance + tx.amount);
        }

        blocks.push_back(new_block.clone());
        Ok(new_block)
    }

    async fn mine_block_hash(
        &self,
        index: u64,
        previous_hash: &str,
        merkle_root: &str,
    ) -> (u64, String) {
        let mut nonce = 0u64;

        loop {
            let data = format!("{}{}{}{}", index, previous_hash, merkle_root, nonce);
            let hash = self.calculate_hash(&data);

            // 检查是否满足难度要求
            if self.is_valid_hash(&hash) {
                return (nonce, hash);
            }

            nonce += 1;

            // 模拟挖矿延迟
            if nonce % 10000 == 0 {
                sleep(Duration::from_micros(1)).await;
            }
        }
    }

    fn calculate_hash(&self, data: &str) -> String {
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    fn is_valid_hash(&self, hash: &str) -> bool {
        let target = "0".repeat(self.difficulty as usize);
        hash.starts_with(&target)
    }

    fn calculate_merkle_root(&self, transactions: &[Transaction]) -> String {
        if transactions.is_empty() {
            return "0".to_string();
        }

        let mut hashes: Vec<String> = transactions
            .iter()
            .map(|tx| self.calculate_hash(&tx.id))
            .collect();

        while hashes.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in hashes.chunks(2) {
                let combined = if chunk.len() == 2 {
                    format!("{}{}", chunk[0], chunk[1])
                } else {
                    chunk[0].clone()
                };
                next_level.push(self.calculate_hash(&combined));
            }
            hashes = next_level;
        }

        hashes[0].clone()
    }

    pub async fn get_balance(&self, address: &str) -> u64 {
        let accounts = self.accounts.read().await;
        accounts.get(address).copied().unwrap_or(0)
    }

    pub async fn get_block_count(&self) -> usize {
        let blocks = self.blocks.read().await;
        blocks.len()
    }

    pub async fn get_pending_transaction_count(&self) -> usize {
        let pending = self.pending_transactions.read().await;
        pending.len()
    }
}

/// 智能合约
pub struct SmartContract {
    pub id: String,
    pub name: String,
    pub bytecode: Vec<u8>,
    pub abi: ContractABI,
    pub state: Arc<RwLock<HashMap<String, String>>>,
    pub creator: String,
    pub created_at: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractABI {
    pub functions: Vec<ContractFunction>,
    pub events: Vec<ContractEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractFunction {
    pub name: String,
    pub inputs: Vec<ContractParameter>,
    pub outputs: Vec<ContractParameter>,
    pub constant: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractEvent {
    pub name: String,
    pub parameters: Vec<ContractParameter>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContractParameter {
    pub name: String,
    pub param_type: String,
}

impl SmartContract {
    pub fn new(name: String, abi: ContractABI, creator: String) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            name,
            bytecode: vec![0x60, 0x60, 0x60, 0x40, 0x52], // 示例字节码
            abi,
            state: Arc::new(RwLock::new(HashMap::new())),
            creator,
            created_at: SystemTime::now(),
        }
    }

    pub async fn execute_function(
        &self,
        function_name: &str,
        inputs: Vec<String>,
        caller: String,
    ) -> Result<String> {
        // 查找函数定义
        let _function = self
            .abi
            .functions
            .iter()
            .find(|f| f.name == function_name)
            .ok_or_else(|| anyhow::anyhow!("函数不存在: {}", function_name))?;

        // 模拟函数执行
        match function_name {
            "setValue" => {
                if inputs.len() >= 2 {
                    let key = inputs[0].clone();
                    let value = inputs[1].clone();
                    let mut state = self.state.write().await;
                    state.insert(key, value);
                    Ok("Value set successfully".to_string())
                } else {
                    Err(anyhow::anyhow!("参数不足"))
                }
            }
            "getValue" => {
                if inputs.len() >= 1 {
                    let key = inputs[0].clone();
                    let state = self.state.read().await;
                    Ok(state
                        .get(&key)
                        .cloned()
                        .unwrap_or_else(|| "Not found".to_string()))
                } else {
                    Err(anyhow::anyhow!("参数不足"))
                }
            }
            "transfer" => {
                if inputs.len() >= 2 {
                    let to = inputs[0].clone();
                    let amount = inputs[1].parse::<u64>()?;

                    // 模拟转账逻辑
                    let mut state = self.state.write().await;
                    let caller_balance = state
                        .get(&caller)
                        .unwrap_or(&"0".to_string())
                        .parse::<u64>()
                        .unwrap_or(0);
                    let to_balance = state
                        .get(&to)
                        .unwrap_or(&"0".to_string())
                        .parse::<u64>()
                        .unwrap_or(0);

                    if caller_balance >= amount {
                        state.insert(caller.clone(), (caller_balance - amount).to_string());
                        state.insert(to.clone(), (to_balance + amount).to_string());
                        Ok("Transfer successful".to_string())
                    } else {
                        Err(anyhow::anyhow!("余额不足"))
                    }
                } else {
                    Err(anyhow::anyhow!("参数不足"))
                }
            }
            _ => Err(anyhow::anyhow!("未知函数: {}", function_name)),
        }
    }

    pub async fn get_state(&self) -> HashMap<String, String> {
        self.state.read().await.clone()
    }
}

/// 挖矿池
pub struct MiningPool {
    pub name: String,
    pub miners: Arc<RwLock<HashMap<String, Miner>>>,
    pub blockchain: Arc<Blockchain>,
    pub reward_distribution: Arc<RwLock<HashMap<String, u64>>>,
    pub pool_fee_percentage: f32,
}

#[derive(Debug, Clone)]
pub struct Miner {
    pub id: String,
    pub address: String,
    pub hashrate: u64, // hashes per second
    pub shares: u64,
    pub last_share_time: Instant,
}

impl MiningPool {
    pub fn new(name: String, blockchain: Arc<Blockchain>, pool_fee_percentage: f32) -> Self {
        Self {
            name,
            miners: Arc::new(RwLock::new(HashMap::new())),
            blockchain,
            reward_distribution: Arc::new(RwLock::new(HashMap::new())),
            pool_fee_percentage,
        }
    }

    pub async fn add_miner(&self, miner: Miner) -> Result<()> {
        let mut miners = self.miners.write().await;
        miners.insert(miner.id.clone(), miner);
        Ok(())
    }

    pub async fn submit_share(&self, miner_id: &str, share: u64) -> Result<()> {
        let mut miners = self.miners.write().await;
        if let Some(miner) = miners.get_mut(miner_id) {
            miner.shares += share;
            miner.last_share_time = Instant::now();
        }
        Ok(())
    }

    pub async fn distribute_rewards(&self, block_reward: u64) -> Result<()> {
        let miners = self.miners.read().await;
        let total_shares: u64 = miners.values().map(|m| m.shares).sum();

        if total_shares == 0 {
            return Ok(());
        }

        let pool_fee = (block_reward as f32 * self.pool_fee_percentage) as u64;
        let distributed_reward = block_reward - pool_fee;

        let mut rewards = self.reward_distribution.write().await;

        for miner in miners.values() {
            let miner_reward = (distributed_reward * miner.shares) / total_shares;
            *rewards.entry(miner.address.clone()).or_insert(0) += miner_reward;
        }

        Ok(())
    }

    pub async fn get_pool_stats(&self) -> PoolStats {
        let miners = self.miners.read().await;
        let total_hashrate: u64 = miners.values().map(|m| m.hashrate).sum();
        let total_shares: u64 = miners.values().map(|m| m.shares).sum();
        let active_miners = miners
            .values()
            .filter(|m| m.last_share_time.elapsed() < Duration::from_secs(600))
            .count();

        PoolStats {
            name: self.name.clone(),
            total_miners: miners.len(),
            active_miners,
            total_hashrate,
            total_shares,
        }
    }
}

#[derive(Debug)]
pub struct PoolStats {
    pub name: String,
    pub total_miners: usize,
    pub active_miners: usize,
    pub total_hashrate: u64,
    pub total_shares: u64,
}

/// 区块链网络节点
pub struct BlockchainNode {
    pub id: String,
    pub address: String,
    pub blockchain: Arc<Blockchain>,
    pub peers: Arc<RwLock<Vec<String>>>,
    pub transaction_pool: Arc<RwLock<VecDeque<Transaction>>>,
    pub is_mining: Arc<RwLock<bool>>,
}

impl BlockchainNode {
    pub fn new(id: String, address: String, blockchain: Arc<Blockchain>) -> Self {
        Self {
            id,
            address,
            blockchain,
            peers: Arc::new(RwLock::new(Vec::new())),
            transaction_pool: Arc::new(RwLock::new(VecDeque::new())),
            is_mining: Arc::new(RwLock::new(false)),
        }
    }

    pub async fn add_peer(&self, peer_address: String) {
        let mut peers = self.peers.write().await;
        if !peers.contains(&peer_address) {
            peers.push(peer_address);
        }
    }

    pub async fn start_mining(&self) {
        let mut is_mining = self.is_mining.write().await;
        *is_mining = true;
        drop(is_mining);

        let blockchain = Arc::clone(&self.blockchain);
        let address = self.address.clone();
        let is_mining = Arc::clone(&self.is_mining);

        tokio::spawn(async move {
            loop {
                {
                    let mining_status = is_mining.read().await;
                    if !*mining_status {
                        break;
                    }
                }

                match blockchain.mine_block(address.clone()).await {
                    Ok(block) => {
                        println!("      挖到新区块 #{}", block.index);
                        println!("        哈希: {}", block.hash);
                        println!("        交易数: {}", block.transactions.len());
                        println!("        Nonce: {}", block.nonce);
                    }
                    Err(e) => {
                        println!("      挖矿失败: {}", e);
                        sleep(Duration::from_secs(1)).await;
                    }
                }
            }
        });
    }

    pub async fn stop_mining(&self) {
        let mut is_mining = self.is_mining.write().await;
        *is_mining = false;
    }

    pub async fn broadcast_transaction(&self, transaction: Transaction) -> Result<()> {
        // 添加到本地区块链
        self.blockchain.add_transaction(transaction.clone()).await?;

        // 广播给所有对等节点
        let peers = self.peers.read().await;
        for peer in peers.iter() {
            // 模拟网络延迟
            sleep(Duration::from_millis(rand::random::<u64>() % 100)).await;
            println!("      广播交易到节点: {}", peer);
        }

        Ok(())
    }

    pub async fn sync_with_peers(&self) -> Result<()> {
        let peers = self.peers.read().await;
        let local_block_count = self.blockchain.get_block_count().await;

        println!("      同步区块 (本地: {})", local_block_count);

        for peer in peers.iter() {
            // 模拟从对等节点获取区块
            let peer_block_count = local_block_count + (rand::random::<u32>() as usize) % 3;

            if peer_block_count > local_block_count {
                println!(
                    "        从 {} 同步 {} 个新区块",
                    peer,
                    peer_block_count - local_block_count
                );
                // 这里应该实际下载和验证区块
            }
        }

        Ok(())
    }
}

struct BlockchainAsyncDemo;

impl BlockchainAsyncDemo {
    async fn run() -> Result<()> {
        println!("⛓️ 区块链异步演示");
        println!("================================");

        // 1. 基础区块链演示
        println!("\n🔗 1. 基础区块链演示");
        Self::demo_basic_blockchain().await?;

        // 2. 智能合约演示
        println!("\n📜 2. 智能合约演示");
        Self::demo_smart_contracts().await?;

        // 3. 挖矿池演示
        println!("\n⛏️ 3. 挖矿池演示");
        Self::demo_mining_pool().await?;

        // 4. 网络节点演示
        println!("\n🌐 4. 网络节点演示");
        Self::demo_network_nodes().await?;

        // 5. 完整区块链系统演示
        println!("\n🎯 5. 完整区块链系统演示");
        Self::demo_complete_blockchain_system().await?;

        Ok(())
    }

    async fn demo_basic_blockchain() -> Result<()> {
        let blockchain = Arc::new(Blockchain::new(2, 100).await);

        // 初始化一些账户
        {
            let mut accounts = blockchain.accounts.write().await;
            accounts.insert("alice".to_string(), 1000);
            accounts.insert("bob".to_string(), 500);
            accounts.insert("charlie".to_string(), 200);
        }

        println!("    初始账户余额:");
        println!(
            "      Alice: {} coins",
            blockchain.get_balance("alice").await
        );
        println!("      Bob: {} coins", blockchain.get_balance("bob").await);
        println!(
            "      Charlie: {} coins",
            blockchain.get_balance("charlie").await
        );

        // 创建交易
        let transaction1 = Transaction {
            id: Uuid::new_v4().to_string(),
            from: "alice".to_string(),
            to: "bob".to_string(),
            amount: 100,
            fee: 10,
            timestamp: SystemTime::now(),
            signature: "signature1".to_string(),
            data: None,
        };

        let transaction2 = Transaction {
            id: Uuid::new_v4().to_string(),
            from: "bob".to_string(),
            to: "charlie".to_string(),
            amount: 50,
            fee: 5,
            timestamp: SystemTime::now(),
            signature: "signature2".to_string(),
            data: None,
        };

        // 添加交易
        blockchain.add_transaction(transaction1).await?;
        blockchain.add_transaction(transaction2).await?;

        println!(
            "    添加了 {} 个待处理交易",
            blockchain.get_pending_transaction_count().await
        );

        // 挖矿
        println!("    开始挖矿...");
        let block = blockchain.mine_block("miner1".to_string()).await?;

        println!("    挖到新区块:");
        println!("      索引: {}", block.index);
        println!("      哈希: {}", block.hash);
        println!("      交易数: {}", block.transactions.len());
        println!("      Nonce: {}", block.nonce);

        // 显示更新后的余额
        println!("    交易后的账户余额:");
        println!(
            "      Alice: {} coins",
            blockchain.get_balance("alice").await
        );
        println!("      Bob: {} coins", blockchain.get_balance("bob").await);
        println!(
            "      Charlie: {} coins",
            blockchain.get_balance("charlie").await
        );
        println!(
            "      Miner1: {} coins",
            blockchain.get_balance("miner1").await
        );

        Ok(())
    }

    async fn demo_smart_contracts() -> Result<()> {
        // 创建智能合约 ABI
        let abi = ContractABI {
            functions: vec![
                ContractFunction {
                    name: "setValue".to_string(),
                    inputs: vec![
                        ContractParameter {
                            name: "key".to_string(),
                            param_type: "string".to_string(),
                        },
                        ContractParameter {
                            name: "value".to_string(),
                            param_type: "string".to_string(),
                        },
                    ],
                    outputs: vec![ContractParameter {
                        name: "result".to_string(),
                        param_type: "string".to_string(),
                    }],
                    constant: false,
                },
                ContractFunction {
                    name: "getValue".to_string(),
                    inputs: vec![ContractParameter {
                        name: "key".to_string(),
                        param_type: "string".to_string(),
                    }],
                    outputs: vec![ContractParameter {
                        name: "value".to_string(),
                        param_type: "string".to_string(),
                    }],
                    constant: true,
                },
                ContractFunction {
                    name: "transfer".to_string(),
                    inputs: vec![
                        ContractParameter {
                            name: "to".to_string(),
                            param_type: "address".to_string(),
                        },
                        ContractParameter {
                            name: "amount".to_string(),
                            param_type: "uint256".to_string(),
                        },
                    ],
                    outputs: vec![ContractParameter {
                        name: "success".to_string(),
                        param_type: "bool".to_string(),
                    }],
                    constant: false,
                },
            ],
            events: vec![],
        };

        let contract =
            SmartContract::new("StorageContract".to_string(), abi, "deployer".to_string());
        println!("    创建智能合约: {}", contract.name);

        // 初始化合约状态
        {
            let mut state = contract.state.write().await;
            state.insert("deployer".to_string(), "1000".to_string());
        }

        // 执行合约函数
        println!("    执行合约函数:");

        // setValue
        let result1 = contract
            .execute_function(
                "setValue",
                vec!["name".to_string(), "Alice".to_string()],
                "deployer".to_string(),
            )
            .await?;
        println!("      setValue('name', 'Alice'): {}", result1);

        // getValue
        let result2 = contract
            .execute_function("getValue", vec!["name".to_string()], "alice".to_string())
            .await?;
        println!("      getValue('name'): {}", result2);

        // transfer
        let result3 = contract
            .execute_function(
                "transfer",
                vec!["alice".to_string(), "100".to_string()],
                "deployer".to_string(),
            )
            .await?;
        println!("      transfer('alice', 100): {}", result3);

        // 显示合约状态
        let state = contract.get_state().await;
        println!("    合约状态:");
        for (key, value) in state {
            println!("      {}: {}", key, value);
        }

        Ok(())
    }

    async fn demo_mining_pool() -> Result<()> {
        let blockchain = Arc::new(Blockchain::new(2, 100).await);
        let pool = MiningPool::new("SuperMiningPool".to_string(), blockchain, 0.05); // 5% 手续费

        // 添加矿工
        let miners = vec![
            Miner {
                id: "miner1".to_string(),
                address: "miner1_address".to_string(),
                hashrate: 1000,
                shares: 0,
                last_share_time: Instant::now(),
            },
            Miner {
                id: "miner2".to_string(),
                address: "miner2_address".to_string(),
                hashrate: 1500,
                shares: 0,
                last_share_time: Instant::now(),
            },
            Miner {
                id: "miner3".to_string(),
                address: "miner3_address".to_string(),
                hashrate: 800,
                shares: 0,
                last_share_time: Instant::now(),
            },
        ];

        for miner in miners {
            pool.add_miner(miner).await?;
        }

        // 模拟提交份额
        println!("    矿工提交份额:");
        for i in 0..10 {
            let miner_id = format!("miner{}", (i % 3) + 1);
            let shares = rand::random::<u64>() % 100 + 1;
            pool.submit_share(&miner_id, shares).await?;
            println!("      {} 提交 {} 份额", miner_id, shares);
        }

        // 显示矿池统计
        let stats = pool.get_pool_stats().await;
        println!("    矿池统计:");
        println!("      矿池名: {}", stats.name);
        println!("      总矿工数: {}", stats.total_miners);
        println!("      活跃矿工数: {}", stats.active_miners);
        println!("      总算力: {} H/s", stats.total_hashrate);
        println!("      总份额: {}", stats.total_shares);

        // 分配奖励
        let block_reward = 100;
        pool.distribute_rewards(block_reward).await?;

        let rewards = pool.reward_distribution.read().await;
        println!("    奖励分配 (总奖励: {}):", block_reward);
        for (address, reward) in rewards.iter() {
            println!("      {}: {} coins", address, reward);
        }

        Ok(())
    }

    async fn demo_network_nodes() -> Result<()> {
        let blockchain = Arc::new(Blockchain::new(2, 100).await);
        let node =
            BlockchainNode::new("node1".to_string(), "192.168.1.100".to_string(), blockchain);

        // 添加对等节点
        let peers = vec![
            "192.168.1.101".to_string(),
            "192.168.1.102".to_string(),
            "192.168.1.103".to_string(),
        ];

        for peer in peers {
            node.add_peer(peer).await;
        }

        println!(
            "    节点 {} 已连接到 {} 个对等节点",
            node.id,
            node.peers.read().await.len()
        );

        // 广播交易
        let transaction = Transaction {
            id: Uuid::new_v4().to_string(),
            from: "alice".to_string(),
            to: "bob".to_string(),
            amount: 50,
            fee: 5,
            timestamp: SystemTime::now(),
            signature: "signature".to_string(),
            data: None,
        };

        node.broadcast_transaction(transaction).await?;

        // 同步区块
        node.sync_with_peers().await?;

        // 启动挖矿
        node.start_mining().await;
        println!("    节点开始挖矿...");

        // 挖矿一段时间
        sleep(Duration::from_secs(2)).await;

        // 停止挖矿
        node.stop_mining().await;
        println!("    节点停止挖矿");

        Ok(())
    }

    async fn demo_complete_blockchain_system() -> Result<()> {
        println!("    创建完整区块链系统...");

        // 创建区块链
        let blockchain = Arc::new(Blockchain::new(2, 100).await);

        // 初始化账户
        {
            let mut accounts = blockchain.accounts.write().await;
            accounts.insert("alice".to_string(), 10000);
            accounts.insert("bob".to_string(), 5000);
            accounts.insert("charlie".to_string(), 2000);
        }

        // 创建挖矿池
        let pool = MiningPool::new("MainPool".to_string(), Arc::clone(&blockchain), 0.03);

        // 添加矿工到矿池
        for i in 1..=5 {
            let miner = Miner {
                id: format!("pool_miner_{}", i),
                address: format!("pool_miner_{}_addr", i),
                hashrate: 1000 + i * 200,
                shares: 0,
                last_share_time: Instant::now(),
            };
            pool.add_miner(miner).await?;
        }

        // 创建网络节点
        let node = BlockchainNode::new(
            "main_node".to_string(),
            "10.0.0.1".to_string(),
            Arc::clone(&blockchain),
        );

        // 模拟系统运行
        println!("    系统运行中...");

        // 1. 创建和广播交易
        for i in 0..5 {
            let transaction = Transaction {
                id: Uuid::new_v4().to_string(),
                from: "alice".to_string(),
                to: "bob".to_string(),
                amount: 100 + i * 50,
                fee: 10,
                timestamp: SystemTime::now(),
                signature: format!("signature_{}", i),
                data: None,
            };

            node.broadcast_transaction(transaction).await?;
            sleep(Duration::from_millis(200)).await;
        }

        // 2. 矿工提交份额
        for _ in 0..20 {
            let miner_id = format!("pool_miner_{}", (rand::random::<u32>() as usize) % 5 + 1);
            let shares = rand::random::<u64>() % 50 + 1;
            pool.submit_share(&miner_id, shares).await?;
        }

        // 3. 挖矿
        println!("    开始挖矿...");
        let block = blockchain.mine_block("pool_miner_1".to_string()).await?;
        println!("    挖到区块 #{}", block.index);

        // 4. 分配奖励
        pool.distribute_rewards(
            block
                .transactions
                .iter()
                .find(|tx| tx.from == "system")
                .unwrap()
                .amount,
        )
        .await?;

        // 5. 显示系统状态
        println!("    系统状态:");
        println!("      区块数: {}", blockchain.get_block_count().await);
        println!(
            "      待处理交易: {}",
            blockchain.get_pending_transaction_count().await
        );

        let pool_stats = pool.get_pool_stats().await;
        println!("      矿池矿工数: {}", pool_stats.active_miners);
        println!("      矿池总算力: {} H/s", pool_stats.total_hashrate);

        let rewards = pool.reward_distribution.read().await;
        println!("      奖励分配:");
        for (address, reward) in rewards.iter() {
            println!("        {}: {} coins", address, reward);
        }

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    BlockchainAsyncDemo::run().await?;

    println!("\n🎉 区块链异步演示完成！");
    Ok(())
}
