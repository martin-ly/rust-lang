//! # 简化版区块链实现
//!
//! 展示 Rust 1.89 特性的简化版区块链实现
//! Simplified blockchain implementation demonstrating Rust 1.89 features
#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

// Rust 1.89 特性：使用常量泛型推断优化哈希计算
/// 区块链哈希结构，支持不同长度的哈希
/// Blockchain hash structure supporting different hash lengths
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockHash<const N: usize = 32> {
    pub data: [u8; N],
}

impl<const N: usize> BlockHash<N> {
    /// 从数据创建哈希
    /// Create hash from data
    pub fn from_data(data: &[u8]) -> BlockHash<32> {
        let mut hasher = Sha256::new();
        hasher.update(data);
        let result = hasher.finalize();

        BlockHash {
            data: result.into(),
        }
    }

    /// 验证哈希
    /// Verify hash
    pub fn verify(&self, other: &BlockHash<N>) -> bool {
        self.data == other.data
    }

    /// 转换为字符串
    /// Convert to string
    pub fn to_string(&self) -> String {
        self.data.iter().map(|b| format!("{:02x}", b)).collect()
    }

    /// 检查是否满足难度要求
    /// Check if meets difficulty requirement
    pub fn meets_difficulty(&self, difficulty: usize) -> bool {
        self.data.iter().take(difficulty).all(|&b| b == 0)
    }
}

/// 交易结构（使用 String 避免生命周期问题）
/// Transaction structure (using String to avoid lifetime issues)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub sender: String,
    pub receiver: String,
    pub amount: u64,
    pub timestamp: u64,
    pub signature: Vec<u8>,
}

impl Transaction {
    /// 创建新交易
    /// Create new transaction
    pub fn new(sender: String, receiver: String, amount: u64) -> Self {
        Self {
            sender,
            receiver,
            amount,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            signature: Vec::new(),
        }
    }

    /// 验证交易
    /// Validate transaction
    pub fn validate(&self) -> ValidationResult {
        let mut errors = Vec::new();

        // 验证金额
        if self.amount == 0 {
            errors.push("Amount must be greater than 0".to_string());
        }

        // 验证发送者和接收者
        if self.sender.is_empty() {
            errors.push("Sender cannot be empty".to_string());
        }

        if self.receiver.is_empty() {
            errors.push("Receiver cannot be empty".to_string());
        }

        ValidationResult {
            is_valid: errors.is_empty(),
            errors,
        }
    }

    /// 序列化为字节
    /// Serialize to bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).unwrap_or_default()
    }

    /// 计算交易哈希
    /// Calculate transaction hash
    pub fn calculate_hash(&self) -> BlockHash<32> {
        let data = self.to_bytes();
        BlockHash::<32>::from_data(&data)
    }
}

/// 验证结果
/// Validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    pub is_valid: bool,
    pub errors: Vec<String>,
}

/// 区块链区块结构
/// Blockchain block structure
#[derive(Debug, Clone)]
pub struct Block {
    pub index: u64,
    pub prev_hash: BlockHash<32>,
    pub timestamp: u64,
    pub transactions: Vec<Transaction>,
    pub hash: BlockHash<32>,
    pub nonce: u64,
    pub difficulty: usize,
}

impl Block {
    /// 创建新区块
    /// Create new block
    pub fn new(
        index: u64,
        prev_hash: BlockHash<32>,
        transactions: Vec<Transaction>,
        difficulty: usize,
    ) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut block = Self {
            index,
            prev_hash,
            timestamp,
            transactions,
            hash: BlockHash { data: [0; 32] },
            nonce: 0,
            difficulty,
        };

        block.hash = block.calculate_hash();
        block
    }

    /// 计算区块哈希
    /// Calculate block hash
    fn calculate_hash(&self) -> BlockHash<32> {
        let mut hasher = Sha256::new();
        hasher.update(self.index.to_le_bytes());
        hasher.update(self.prev_hash.data);
        hasher.update(self.timestamp.to_le_bytes());
        hasher.update(self.nonce.to_le_bytes());

        // 添加交易哈希
        for tx in &self.transactions {
            hasher.update(tx.calculate_hash().data);
        }

        let result = hasher.finalize();
        BlockHash {
            data: result.into(),
        }
    }

    /// 挖矿
    /// Mining
    pub fn mine(&mut self) -> Result<(), String> {
        let start_time = SystemTime::now();
        let timeout = Duration::from_secs(300); // 5分钟超时

        loop {
            // 检查超时
            if start_time.elapsed().unwrap_or(Duration::ZERO) > timeout {
                return Err("Mining timeout".to_string());
            }

            // 检查是否满足难度要求
            if self.hash.meets_difficulty(self.difficulty) {
                return Ok(());
            }

            // 增加随机数并重新计算哈希
            self.nonce += 1;
            self.hash = self.calculate_hash();

            // 防止无限循环
            if self.nonce > 10_000_000 {
                return Err("Mining limit exceeded".to_string());
            }
        }
    }

    /// 验证区块
    /// Validate block
    pub fn validate(&self, prev_block: &Block) -> Result<(), String> {
        // 验证索引
        if self.index != prev_block.index + 1 {
            return Err("Invalid block index".to_string());
        }

        // 验证前一个区块哈希
        if self.prev_hash != prev_block.hash {
            return Err("Invalid previous hash".to_string());
        }

        // 验证工作量证明
        if !self.hash.meets_difficulty(self.difficulty) {
            return Err("Invalid proof of work".to_string());
        }

        // 验证交易
        for tx in &self.transactions {
            if tx.amount == 0 {
                return Err("Invalid transaction amount".to_string());
            }
        }

        Ok(())
    }
}

/// 区块链结构
/// Blockchain structure
#[derive(Debug, Clone)]
pub struct Blockchain {
    pub chain: Vec<Block>,
    pub pending_transactions: Vec<Transaction>,
    pub difficulty: usize,
    pub balances: HashMap<String, u64>,
}

impl Blockchain {
    /// 创建新区块链
    /// Create new blockchain
    pub fn new(difficulty: usize) -> Self {
        let genesis_transactions = vec![Transaction::new(
            "genesis".to_string(),
            "genesis".to_string(),
            0,
        )];
        let genesis_block = Block::new(
            0,
            BlockHash { data: [0; 32] },
            genesis_transactions,
            difficulty,
        );

        let mut blockchain = Self {
            chain: vec![genesis_block],
            pending_transactions: Vec::new(),
            difficulty,
            balances: HashMap::new(),
        };

        // 初始化创世账户余额
        blockchain.balances.insert("genesis".to_string(), 1_000_000);

        blockchain
    }

    /// 添加交易
    /// Add transaction
    pub fn add_transaction(&mut self, transaction: Transaction) -> Result<(), String> {
        // 验证交易
        let validation = transaction.validate();
        if !validation.is_valid {
            return Err(format!(
                "Transaction validation failed: {:?}",
                validation.errors
            ));
        }

        // 检查余额
        let balance = self.get_balance(&transaction.sender);
        if balance < transaction.amount {
            return Err("Insufficient balance".to_string());
        }

        self.pending_transactions.push(transaction);
        Ok(())
    }

    /// 挖矿待处理交易
    /// Mine pending transactions
    pub fn mine_pending_transactions(
        &mut self,
        mining_reward_address: String,
    ) -> Result<(), String> {
        // 添加挖矿奖励交易
        let reward_transaction = Transaction::new("system".to_string(), mining_reward_address, 10);
        self.pending_transactions.push(reward_transaction);

        // 创建新区块
        let mut block = Block::new(
            self.chain.len() as u64,
            self.chain.last().unwrap().hash.clone(),
            self.pending_transactions.clone(),
            self.difficulty,
        );

        // 挖矿
        block.mine()?;

        // 验证区块
        if let Some(prev_block) = self.chain.last() {
            block.validate(prev_block)?;
        }

        // 添加到链中
        self.chain.push(block);

        // 更新余额
        self.update_balances();

        // 清空待处理交易
        self.pending_transactions.clear();

        Ok(())
    }

    /// 更新余额
    /// Update balances
    fn update_balances(&mut self) {
        if let Some(last_block) = self.chain.last() {
            for tx in &last_block.transactions {
                // 减少发送者余额
                if tx.sender != "system" && tx.sender != "genesis" {
                    let current_balance = self.balances.get(&tx.sender).unwrap_or(&0);
                    self.balances
                        .insert(tx.sender.clone(), current_balance.saturating_sub(tx.amount));
                }

                // 增加接收者余额
                let current_balance = self.balances.get(&tx.receiver).unwrap_or(&0);
                self.balances.insert(
                    tx.receiver.clone(),
                    current_balance.saturating_add(tx.amount),
                );
            }
        }
    }

    /// 获取余额
    /// Get balance
    pub fn get_balance(&self, address: &str) -> u64 {
        *self.balances.get(address).unwrap_or(&0)
    }

    /// 验证整个链
    /// Validate entire chain
    pub fn is_valid_chain(&self) -> bool {
        for i in 1..self.chain.len() {
            if let Some(prev_block) = self.chain.get(i - 1)
                && self.chain[i].validate(prev_block).is_err() {
                    return false;
                }
        }
        true
    }

    /// 获取链长度
    /// Get chain length
    pub fn get_chain_length(&self) -> usize {
        self.chain.len()
    }

    /// 获取最新区块
    /// Get latest block
    pub fn get_latest_block(&self) -> Option<&Block> {
        self.chain.last()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_hash_creation() {
        let data = b"test data";
        let hash = BlockHash::<32>::from_data(data);
        assert_eq!(hash.data.len(), 32);
    }

    #[test]
    fn test_transaction_validation() {
        let transaction = Transaction::new("alice".to_string(), "bob".to_string(), 100);
        let result = transaction.validate();
        assert!(result.is_valid);
    }

    #[test]
    fn test_blockchain_creation() {
        let blockchain = Blockchain::new(2);
        assert_eq!(blockchain.get_chain_length(), 1);
        assert_eq!(blockchain.get_balance("genesis"), 1_000_000);
    }

    #[test]
    fn test_mining() {
        let mut blockchain = Blockchain::new(1); // 低难度用于测试
        let transaction = Transaction::new("genesis".to_string(), "alice".to_string(), 100);
        blockchain.add_transaction(transaction).unwrap();

        let result = blockchain.mine_pending_transactions("miner".to_string());
        assert!(result.is_ok());
        assert_eq!(blockchain.get_chain_length(), 2);
    }

    #[test]
    fn test_chain_validation() {
        let blockchain = Blockchain::new(2);
        assert!(blockchain.is_valid_chain());
    }
}
