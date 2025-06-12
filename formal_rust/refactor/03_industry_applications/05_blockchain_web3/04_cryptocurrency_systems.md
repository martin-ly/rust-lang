# 5.4 加密货币系统 (Cryptocurrency Systems)

## 概述

加密货币系统是区块链技术的核心应用，提供去中心化的数字资产和支付功能。本节将建立加密货币系统的形式化模型，并提供Rust实现。

## 形式化定义

### 5.4.1 加密货币系统定义

**定义 5.4.1** (加密货币系统)
加密货币系统是一个五元组 $CS = (T, W, M, V, P)$，其中：

- $T$ 是交易集合
- $W$ 是钱包集合
- $M$ 是挖矿机制
- $V$ 是验证机制
- $P$ 是协议规则

**定义 5.4.2** (交易)
交易是一个四元组 $tx = (from, to, amount, signature)$，其中：

- $from$ 是发送方地址
- $to$ 是接收方地址
- $amount$ 是交易金额
- $signature$ 是数字签名

**定义 5.4.3** (钱包)
钱包是一个三元组 $wallet = (address, private\_key, balance)$，其中：

- $address$ 是公钥地址
- $private\_key$ 是私钥
- $balance$ 是余额

## 核心定理

### 定理 5.4.1 (交易安全性)

**定理**: 对于任意交易 $tx$，如果签名验证通过，则交易不可篡改：

$$verify(tx.signature, tx.data) = true \Rightarrow immutable(tx)$$

### 定理 5.4.2 (余额一致性)

**定理**: 对于任意钱包集合 $W$，总余额保持不变：

$$\sum_{w \in W} w.balance = constant$$

## Rust实现

### 5.4.1 加密货币系统实现

```rust
use std::collections::HashMap;
use sha2::{Sha256, Digest};
use secp256k1::{SecretKey, PublicKey, Message, Secp256k1};
use rand::Rng;

/// 交易
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub id: String,
    pub from: String,
    pub to: String,
    pub amount: u64,
    pub fee: u64,
    pub timestamp: u64,
    pub signature: Vec<u8>,
}

impl Transaction {
    pub fn new(from: String, to: String, amount: u64, fee: u64) -> Self {
        let id = Self::generate_id(&from, &to, amount, fee);
        
        Self {
            id,
            from,
            to,
            amount,
            fee,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            signature: Vec::new(),
        }
    }
    
    pub fn sign(&mut self, private_key: &SecretKey) -> Result<(), CryptoError> {
        let secp = Secp256k1::new();
        let message = self.to_message()?;
        let signature = secp.sign_ecdsa(&message, private_key);
        
        self.signature = signature.serialize_der().to_vec();
        Ok(())
    }
    
    pub fn verify(&self, public_key: &PublicKey) -> Result<bool, CryptoError> {
        let secp = Secp256k1::new();
        let message = self.to_message()?;
        let signature = secp256k1::ecdsa::Signature::from_der(&self.signature)
            .map_err(|_| CryptoError::InvalidSignature)?;
        
        Ok(secp.verify_ecdsa(&message, &signature, public_key).is_ok())
    }
    
    fn generate_id(from: &str, to: &str, amount: u64, fee: u64) -> String {
        let mut hasher = Sha256::new();
        hasher.update(from.as_bytes());
        hasher.update(to.as_bytes());
        hasher.update(&amount.to_le_bytes());
        hasher.update(&fee.to_le_bytes());
        
        let result = hasher.finalize();
        hex::encode(result)
    }
    
    fn to_message(&self) -> Result<Message, CryptoError> {
        let data = format!("{}:{}:{}:{}:{}", 
            self.from, self.to, self.amount, self.fee, self.timestamp);
        
        let mut hasher = Sha256::new();
        hasher.update(data.as_bytes());
        let hash = hasher.finalize();
        
        Message::from_slice(&hash)
            .map_err(|_| CryptoError::InvalidMessage)
    }
}

/// 钱包
#[derive(Debug, Clone)]
pub struct Wallet {
    pub address: String,
    pub private_key: SecretKey,
    pub public_key: PublicKey,
    pub balance: u64,
    pub nonce: u64,
}

impl Wallet {
    pub fn new() -> Self {
        let secp = Secp256k1::new();
        let private_key = SecretKey::new(&mut rand::thread_rng());
        let public_key = PublicKey::from_secret_key(&secp, &private_key);
        let address = Self::generate_address(&public_key);
        
        Self {
            address,
            private_key,
            public_key,
            balance: 0,
            nonce: 0,
        }
    }
    
    pub fn from_private_key(private_key: SecretKey) -> Self {
        let secp = Secp256k1::new();
        let public_key = PublicKey::from_secret_key(&secp, &private_key);
        let address = Self::generate_address(&public_key);
        
        Self {
            address,
            private_key,
            public_key,
            balance: 0,
            nonce: 0,
        }
    }
    
    pub fn create_transaction(&mut self, to: String, amount: u64, fee: u64) -> Result<Transaction, CryptoError> {
        if amount + fee > self.balance {
            return Err(CryptoError::InsufficientBalance);
        }
        
        let mut transaction = Transaction::new(
            self.address.clone(),
            to,
            amount,
            fee,
        );
        
        transaction.sign(&self.private_key)?;
        self.nonce += 1;
        
        Ok(transaction)
    }
    
    pub fn update_balance(&mut self, amount: i64) {
        if amount > 0 {
            self.balance = self.balance.saturating_add(amount as u64);
        } else {
            self.balance = self.balance.saturating_sub((-amount) as u64);
        }
    }
    
    fn generate_address(public_key: &PublicKey) -> String {
        let mut hasher = Sha256::new();
        hasher.update(&public_key.serialize());
        let hash = hasher.finalize();
        
        // 简化的地址生成，实际应该使用RIPEMD160
        hex::encode(&hash[..20])
    }
}

/// 加密货币系统
pub struct CryptocurrencySystem {
    pub wallets: HashMap<String, Wallet>,
    pub transactions: Vec<Transaction>,
    pub mempool: Vec<Transaction>,
    pub block_reward: u64,
    pub difficulty: u32,
}

impl CryptocurrencySystem {
    pub fn new(block_reward: u64, difficulty: u32) -> Self {
        Self {
            wallets: HashMap::new(),
            transactions: Vec::new(),
            mempool: Vec::new(),
            block_reward,
            difficulty,
        }
    }
    
    pub fn create_wallet(&mut self) -> String {
        let wallet = Wallet::new();
        let address = wallet.address.clone();
        self.wallets.insert(address.clone(), wallet);
        address
    }
    
    pub fn send_transaction(&mut self, from: &str, to: &str, amount: u64, fee: u64) -> Result<String, CryptoError> {
        let wallet = self.wallets.get_mut(from)
            .ok_or(CryptoError::WalletNotFound)?;
        
        let transaction = wallet.create_transaction(to.to_string(), amount, fee)?;
        
        // 验证交易
        if !self.verify_transaction(&transaction)? {
            return Err(CryptoError::InvalidTransaction);
        }
        
        // 添加到内存池
        self.mempool.push(transaction.clone());
        
        Ok(transaction.id)
    }
    
    pub fn mine_block(&mut self, miner_address: &str) -> Result<Block, CryptoError> {
        let miner_wallet = self.wallets.get_mut(miner_address)
            .ok_or(CryptoError::WalletNotFound)?;
        
        // 创建区块
        let mut block = Block::new(
            self.transactions.len() as u64,
            self.mempool.clone(),
            miner_address.to_string(),
        );
        
        // 挖矿
        block.mine(self.difficulty)?;
        
        // 处理交易
        for transaction in &block.transactions {
            self.process_transaction(transaction)?;
        }
        
        // 奖励矿工
        miner_wallet.update_balance(self.block_reward as i64);
        
        // 清空内存池
        self.mempool.clear();
        
        Ok(block)
    }
    
    pub fn verify_transaction(&self, transaction: &Transaction) -> Result<bool, CryptoError> {
        // 验证签名
        let from_wallet = self.wallets.get(&transaction.from)
            .ok_or(CryptoError::WalletNotFound)?;
        
        if !transaction.verify(&from_wallet.public_key)? {
            return Err(CryptoError::InvalidSignature);
        }
        
        // 验证余额
        if transaction.amount + transaction.fee > from_wallet.balance {
            return Err(CryptoError::InsufficientBalance);
        }
        
        Ok(true)
    }
    
    pub fn process_transaction(&mut self, transaction: &Transaction) -> Result<(), CryptoError> {
        let from_wallet = self.wallets.get_mut(&transaction.from)
            .ok_or(CryptoError::WalletNotFound)?;
        
        let to_wallet = self.wallets.get_mut(&transaction.to)
            .ok_or(CryptoError::WalletNotFound)?;
        
        // 扣除发送方余额
        from_wallet.update_balance(-(transaction.amount + transaction.fee) as i64);
        
        // 增加接收方余额
        to_wallet.update_balance(transaction.amount as i64);
        
        // 添加到已确认交易
        self.transactions.push(transaction.clone());
        
        Ok(())
    }
    
    pub fn get_balance(&self, address: &str) -> Result<u64, CryptoError> {
        let wallet = self.wallets.get(address)
            .ok_or(CryptoError::WalletNotFound)?;
        
        Ok(wallet.balance)
    }
    
    pub fn get_transaction_history(&self, address: &str) -> Vec<&Transaction> {
        self.transactions.iter()
            .filter(|tx| tx.from == address || tx.to == address)
            .collect()
    }
}

/// 区块
#[derive(Debug, Clone)]
pub struct Block {
    pub index: u64,
    pub timestamp: u64,
    pub transactions: Vec<Transaction>,
    pub previous_hash: String,
    pub hash: String,
    pub nonce: u64,
    pub miner: String,
}

impl Block {
    pub fn new(index: u64, transactions: Vec<Transaction>, miner: String) -> Self {
        let previous_hash = if index == 0 {
            "0000000000000000000000000000000000000000000000000000000000000000".to_string()
        } else {
            "previous_hash".to_string() // 简化实现
        };
        
        Self {
            index,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            transactions,
            previous_hash,
            hash: String::new(),
            nonce: 0,
            miner,
        }
    }
    
    pub fn mine(&mut self, difficulty: u32) -> Result<(), CryptoError> {
        let target = "0".repeat(difficulty as usize);
        
        loop {
            self.hash = self.calculate_hash();
            if self.hash.starts_with(&target) {
                break;
            }
            self.nonce += 1;
        }
        
        Ok(())
    }
    
    pub fn calculate_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(&self.index.to_le_bytes());
        hasher.update(&self.timestamp.to_le_bytes());
        hasher.update(&self.previous_hash.as_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        
        // 添加交易哈希
        for transaction in &self.transactions {
            hasher.update(transaction.id.as_bytes());
        }
        
        let result = hasher.finalize();
        hex::encode(result)
    }
}
```

### 5.4.2 代币标准实现

```rust
/// ERC-20代币
pub struct ERC20Token {
    pub name: String,
    pub symbol: String,
    pub decimals: u8,
    pub total_supply: u64,
    pub balances: HashMap<String, u64>,
    pub allowances: HashMap<(String, String), u64>,
    pub owner: String,
}

impl ERC20Token {
    pub fn new(name: String, symbol: String, decimals: u8, total_supply: u64, owner: String) -> Self {
        let mut balances = HashMap::new();
        balances.insert(owner.clone(), total_supply);
        
        Self {
            name,
            symbol,
            decimals,
            total_supply,
            balances,
            allowances: HashMap::new(),
            owner,
        }
    }
    
    pub fn balance_of(&self, address: &str) -> u64 {
        *self.balances.get(address).unwrap_or(&0)
    }
    
    pub fn transfer(&mut self, from: &str, to: &str, amount: u64) -> Result<bool, CryptoError> {
        if self.balance_of(from) < amount {
            return Err(CryptoError::InsufficientBalance);
        }
        
        let from_balance = self.balances.entry(from.to_string()).or_insert(0);
        *from_balance = from_balance.saturating_sub(amount);
        
        let to_balance = self.balances.entry(to.to_string()).or_insert(0);
        *to_balance = to_balance.saturating_add(amount);
        
        Ok(true)
    }
    
    pub fn approve(&mut self, owner: &str, spender: &str, amount: u64) -> Result<bool, CryptoError> {
        self.allowances.insert((owner.to_string(), spender.to_string()), amount);
        Ok(true)
    }
    
    pub fn transfer_from(&mut self, spender: &str, from: &str, to: &str, amount: u64) -> Result<bool, CryptoError> {
        let allowance = self.allowances.get(&(from.to_string(), spender.to_string()))
            .unwrap_or(&0);
        
        if *allowance < amount {
            return Err(CryptoError::InsufficientAllowance);
        }
        
        if self.balance_of(from) < amount {
            return Err(CryptoError::InsufficientBalance);
        }
        
        // 更新余额
        let from_balance = self.balances.entry(from.to_string()).or_insert(0);
        *from_balance = from_balance.saturating_sub(amount);
        
        let to_balance = self.balances.entry(to.to_string()).or_insert(0);
        *to_balance = to_balance.saturating_add(amount);
        
        // 更新授权
        let new_allowance = allowance.saturating_sub(amount);
        self.allowances.insert((from.to_string(), spender.to_string()), new_allowance);
        
        Ok(true)
    }
    
    pub fn allowance(&self, owner: &str, spender: &str) -> u64 {
        *self.allowances.get(&(owner.to_string(), spender.to_string())).unwrap_or(&0)
    }
}

/// ERC-721代币（NFT）
pub struct ERC721Token {
    pub name: String,
    pub symbol: String,
    pub token_owners: HashMap<u64, String>,
    pub token_approvals: HashMap<u64, String>,
    pub operator_approvals: HashMap<(String, String), bool>,
    pub next_token_id: u64,
}

impl ERC721Token {
    pub fn new(name: String, symbol: String) -> Self {
        Self {
            name,
            symbol,
            token_owners: HashMap::new(),
            token_approvals: HashMap::new(),
            operator_approvals: HashMap::new(),
            next_token_id: 1,
        }
    }
    
    pub fn mint(&mut self, to: &str) -> u64 {
        let token_id = self.next_token_id;
        self.token_owners.insert(token_id, to.to_string());
        self.next_token_id += 1;
        token_id
    }
    
    pub fn owner_of(&self, token_id: u64) -> Option<&String> {
        self.token_owners.get(&token_id)
    }
    
    pub fn transfer(&mut self, from: &str, to: &str, token_id: u64) -> Result<bool, CryptoError> {
        if let Some(owner) = self.token_owners.get(&token_id) {
            if owner != from {
                return Err(CryptoError::NotTokenOwner);
            }
        } else {
            return Err(CryptoError::TokenNotFound);
        }
        
        self.token_owners.insert(token_id, to.to_string());
        self.token_approvals.remove(&token_id);
        
        Ok(true)
    }
    
    pub fn approve(&mut self, owner: &str, to: &str, token_id: u64) -> Result<bool, CryptoError> {
        if let Some(token_owner) = self.token_owners.get(&token_id) {
            if token_owner != owner {
                return Err(CryptoError::NotTokenOwner);
            }
        } else {
            return Err(CryptoError::TokenNotFound);
        }
        
        self.token_approvals.insert(token_id, to.to_string());
        Ok(true)
    }
    
    pub fn get_approved(&self, token_id: u64) -> Option<&String> {
        self.token_approvals.get(&token_id)
    }
}
```

### 5.4.3 错误处理

```rust
/// 加密货币错误
#[derive(Debug, thiserror::Error)]
pub enum CryptoError {
    #[error("Wallet not found")]
    WalletNotFound,
    
    #[error("Insufficient balance")]
    InsufficientBalance,
    
    #[error("Invalid signature")]
    InvalidSignature,
    
    #[error("Invalid transaction")]
    InvalidTransaction,
    
    #[error("Invalid message")]
    InvalidMessage,
    
    #[error("Token not found")]
    TokenNotFound,
    
    #[error("Not token owner")]
    NotTokenOwner,
    
    #[error("Insufficient allowance")]
    InsufficientAllowance,
    
    #[error("Mining failed")]
    MiningFailed,
    
    #[error("Network error: {0}")]
    NetworkError(String),
}
```

## 应用示例

### 5.4.1 简单加密货币示例

```rust
pub fn cryptocurrency_example() {
    let mut crypto_system = CryptocurrencySystem::new(50, 4); // 50奖励，难度4
    
    // 创建钱包
    let alice = crypto_system.create_wallet();
    let bob = crypto_system.create_wallet();
    let charlie = crypto_system.create_wallet();
    
    println!("Alice: {}", alice);
    println!("Bob: {}", bob);
    println!("Charlie: {}", charlie);
    
    // 挖矿获得初始余额
    let block = crypto_system.mine_block(&alice).unwrap();
    println!("Block mined: {}", block.hash);
    
    // 查看余额
    println!("Alice balance: {}", crypto_system.get_balance(&alice).unwrap());
    
    // 发送交易
    match crypto_system.send_transaction(&alice, &bob, 10, 1) {
        Ok(tx_id) => println!("Transaction sent: {}", tx_id),
        Err(e) => eprintln!("Transaction failed: {}", e),
    }
    
    // 挖矿确认交易
    let block = crypto_system.mine_block(&charlie).unwrap();
    println!("Block mined: {}", block.hash);
    
    // 查看新余额
    println!("Alice balance: {}", crypto_system.get_balance(&alice).unwrap());
    println!("Bob balance: {}", crypto_system.get_balance(&bob).unwrap());
}
```

### 5.4.2 ERC-20代币示例

```rust
pub fn erc20_example() {
    let mut token = ERC20Token::new(
        "MyToken".to_string(),
        "MTK".to_string(),
        18,
        1000000,
        "owner".to_string(),
    );
    
    // 查看余额
    println!("Owner balance: {}", token.balance_of("owner"));
    
    // 转账
    match token.transfer("owner", "alice", 100) {
        Ok(_) => println!("Transfer successful"),
        Err(e) => eprintln!("Transfer failed: {}", e),
    }
    
    println!("Owner balance: {}", token.balance_of("owner"));
    println!("Alice balance: {}", token.balance_of("alice"));
    
    // 授权
    token.approve("alice", "bob", 50).unwrap();
    println!("Allowance: {}", token.allowance("alice", "bob"));
    
    // 授权转账
    match token.transfer_from("bob", "alice", "charlie", 30) {
        Ok(_) => println!("Transfer from successful"),
        Err(e) => eprintln!("Transfer from failed: {}", e),
    }
    
    println!("Alice balance: {}", token.balance_of("alice"));
    println!("Charlie balance: {}", token.balance_of("charlie"));
    println!("Remaining allowance: {}", token.allowance("alice", "bob"));
}
```

## 性能分析

### 5.4.1 交易处理性能

**定理 5.4.3** (交易处理复杂度)

交易处理的时间复杂度为：

$$T_{process} = O(n \cdot \log n)$$

其中 $n$ 是交易数量。

### 5.4.2 挖矿性能

**定理 5.4.4** (挖矿复杂度)

挖矿的期望时间复杂度为：

$$T_{mine} = O(2^d)$$

其中 $d$ 是难度值。

## 总结

本节建立了加密货币系统的完整形式化模型，包括：

1. **形式化定义**: 加密货币系统、交易、钱包的定义
2. **核心定理**: 交易安全性、余额一致性定理
3. **Rust实现**: 完整的加密货币系统、代币标准实现
4. **应用示例**: 简单加密货币和ERC-20代币的实际应用
5. **性能分析**: 交易处理和挖矿性能分析

加密货币系统为数字资产和去中心化金融提供了基础，是区块链技术的重要应用。
