# 游戏支付系统（Game Payment System）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [游戏支付系统](#游戏支付系统game-payment-system)
  - [概述](#概述)
  - [系统架构](#系统架构)
  - [支付处理](#支付处理)
  - [虚拟货币](#虚拟货币)
  - [实践示例](#实践示例)
  - [安全考虑](#安全考虑)
  - [参考资料](#参考资料)

---

## 概述

游戏支付系统需要处理游戏内购买、虚拟货币交易、道具购买等场景。Rust 的高性能和内存安全特性使其成为构建游戏支付系统的理想选择。

## 系统架构

```text
┌─────────────┐
│  游戏客户端  │
└──────┬──────┘
       │
┌──────▼──────────┐
│  支付网关服务   │
└──────┬──────────┘
       │
┌──────▼──────────┐
│  支付处理服务   │
└──────┬──────────┘
       │
┌──────▼──────────┐
│  虚拟货币服务   │
└─────────────────┘
```

## 支付处理

### 支付请求

```rust
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaymentRequest {
    pub user_id: String,
    pub item_id: String,
    pub amount: f64,
    pub currency: String,
    pub payment_method: PaymentMethod,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaymentMethod {
    CreditCard { card_number: String },
    PayPal { email: String },
    VirtualCurrency { currency_type: String },
}

pub struct PaymentProcessor;

impl PaymentProcessor {
    pub async fn process_payment(
        &self,
        request: PaymentRequest,
    ) -> Result<PaymentResult, PaymentError> {
        // 验证请求
        self.validate_request(&request)?;

        // 处理支付
        let result = match &request.payment_method {
            PaymentMethod::CreditCard { .. } => {
                self.process_credit_card(&request).await?
            }
            PaymentMethod::PayPal { .. } => {
                self.process_paypal(&request).await?
            }
            PaymentMethod::VirtualCurrency { .. } => {
                self.process_virtual_currency(&request).await?
            }
        };

        Ok(result)
    }

    fn validate_request(&self, request: &PaymentRequest) -> Result<(), PaymentError> {
        if request.amount <= 0.0 {
            return Err(PaymentError::InvalidAmount);
        }
        if request.user_id.is_empty() {
            return Err(PaymentError::InvalidUserId);
        }
        Ok(())
    }

    async fn process_credit_card(
        &self,
        request: &PaymentRequest,
    ) -> Result<PaymentResult, PaymentError> {
        // 模拟信用卡处理
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Ok(PaymentResult {
            transaction_id: generate_transaction_id(),
            status: PaymentStatus::Completed,
            amount: request.amount,
        })
    }

    async fn process_paypal(
        &self,
        request: &PaymentRequest,
    ) -> Result<PaymentResult, PaymentError> {
        // 模拟 PayPal 处理
        tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
        Ok(PaymentResult {
            transaction_id: generate_transaction_id(),
            status: PaymentStatus::Completed,
            amount: request.amount,
        })
    }

    async fn process_virtual_currency(
        &self,
        request: &PaymentRequest,
    ) -> Result<PaymentResult, PaymentError> {
        // 处理虚拟货币支付
        // 检查用户余额等
        Ok(PaymentResult {
            transaction_id: generate_transaction_id(),
            status: PaymentStatus::Completed,
            amount: request.amount,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaymentResult {
    pub transaction_id: String,
    pub status: PaymentStatus,
    pub amount: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PaymentStatus {
    Pending,
    Completed,
    Failed,
    Refunded,
}

#[derive(Debug)]
pub enum PaymentError {
    InvalidAmount,
    InvalidUserId,
    InsufficientFunds,
    PaymentGatewayError(String),
}

fn generate_transaction_id() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    format!("TXN{:016X}", timestamp)
}
```

## 虚拟货币

### 虚拟货币管理

```rust
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct VirtualCurrencyManager {
    balances: Arc<RwLock<HashMap<String, f64>>>,
}

impl VirtualCurrencyManager {
    pub fn new() -> Self {
        VirtualCurrencyManager {
            balances: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn get_balance(&self, user_id: &str) -> f64 {
        let balances = self.balances.read().await;
        balances.get(user_id).copied().unwrap_or(0.0)
    }

    pub async fn add_currency(
        &self,
        user_id: &str,
        amount: f64,
    ) -> Result<(), String> {
        if amount <= 0.0 {
            return Err("金额必须大于零".to_string());
        }

        let mut balances = self.balances.write().await;
        let balance = balances.entry(user_id.to_string()).or_insert(0.0);
        *balance += amount;
        Ok(())
    }

    pub async fn deduct_currency(
        &self,
        user_id: &str,
        amount: f64,
    ) -> Result<(), String> {
        if amount <= 0.0 {
            return Err("金额必须大于零".to_string());
        }

        let mut balances = self.balances.write().await;
        let balance = balances.entry(user_id.to_string()).or_insert(0.0);

        if *balance < amount {
            return Err("余额不足".to_string());
        }

        *balance -= amount;
        Ok(())
    }

    pub async fn transfer(
        &self,
        from_user: &str,
        to_user: &str,
        amount: f64,
    ) -> Result<(), String> {
        if amount <= 0.0 {
            return Err("金额必须大于零".to_string());
        }

        let mut balances = self.balances.write().await;

        let from_balance = balances.get_mut(from_user)
            .ok_or_else(|| "发送方不存在".to_string())?;

        if *from_balance < amount {
            return Err("余额不足".to_string());
        }

        *from_balance -= amount;
        let to_balance = balances.entry(to_user.to_string()).or_insert(0.0);
        *to_balance += amount;

        Ok(())
    }
}
```

## 实践示例

### 示例 1：游戏内购买

```rust
pub struct InGamePurchaseService {
    payment_processor: PaymentProcessor,
    currency_manager: Arc<VirtualCurrencyManager>,
}

impl InGamePurchaseService {
    pub fn new(
        payment_processor: PaymentProcessor,
        currency_manager: Arc<VirtualCurrencyManager>,
    ) -> Self {
        InGamePurchaseService {
            payment_processor,
            currency_manager,
        }
    }

    pub async fn purchase_item(
        &self,
        user_id: &str,
        item_id: &str,
        payment_method: PaymentMethod,
    ) -> Result<PurchaseResult, PurchaseError> {
        // 获取物品价格
        let price = self.get_item_price(item_id)?;

        // 处理支付
        let payment_request = PaymentRequest {
            user_id: user_id.to_string(),
            item_id: item_id.to_string(),
            amount: price,
            currency: "USD".to_string(),
            payment_method,
            timestamp: Utc::now(),
        };

        let payment_result = self.payment_processor
            .process_payment(payment_request)
            .await
            .map_err(|e| PurchaseError::PaymentFailed(e.to_string()))?;

        if payment_result.status != PaymentStatus::Completed {
            return Err(PurchaseError::PaymentFailed("支付未完成".to_string()));
        }

        // 发放物品
        self.grant_item(user_id, item_id).await?;

        Ok(PurchaseResult {
            transaction_id: payment_result.transaction_id,
            item_id: item_id.to_string(),
        })
    }

    fn get_item_price(&self, item_id: &str) -> Result<f64, PurchaseError> {
        // 从数据库或配置获取价格
        match item_id {
            "sword_001" => Ok(9.99),
            "shield_001" => Ok(14.99),
            "potion_001" => Ok(1.99),
            _ => Err(PurchaseError::ItemNotFound),
        }
    }

    async fn grant_item(&self, user_id: &str, item_id: &str) -> Result<(), PurchaseError> {
        // 将物品添加到用户库存
        // 实际实现应该更新数据库
        Ok(())
    }
}

#[derive(Debug)]
pub struct PurchaseResult {
    pub transaction_id: String,
    pub item_id: String,
}

#[derive(Debug)]
pub enum PurchaseError {
    ItemNotFound,
    PaymentFailed(String),
    InsufficientFunds,
}
```

## 安全考虑

### 1. 请求验证

```rust
use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

pub struct PaymentSecurity {
    secret_key: String,
}

impl PaymentSecurity {
    pub fn new(secret_key: String) -> Self {
        PaymentSecurity { secret_key }
    }

    pub fn verify_signature(
        &self,
        data: &str,
        signature: &str,
    ) -> Result<(), String> {
        let mut mac = HmacSha256::new_from_slice(self.secret_key.as_bytes())
            .map_err(|e| format!("HMAC 创建失败: {}", e))?;

        mac.update(data.as_bytes());
        mac.verify_slice(signature.as_bytes())
            .map_err(|_| "签名验证失败".to_string())
    }
}
```

### 2. 防重放攻击

```rust
use std::collections::HashSet;
use tokio::sync::RwLock;

pub struct ReplayProtection {
    used_nonces: Arc<RwLock<HashSet<String>>>,
}

impl ReplayProtection {
    pub fn new() -> Self {
        ReplayProtection {
            used_nonces: Arc::new(RwLock::new(HashSet::new())),
        }
    }

    pub async fn check_nonce(&self, nonce: &str) -> Result<(), String> {
        let mut used = self.used_nonces.write().await;
        if used.contains(nonce) {
            return Err("重复的 nonce".to_string());
        }
        used.insert(nonce.to_string());
        Ok(())
    }
}
```

## 参考资料

- [游戏开发索引](./00_index.md)
- [金融科技索引](../00_index.md)
- [支付系统最佳实践](../../../../crates/c10_networks/)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回金融科技: [`../00_index.md`](../00_index.md)
