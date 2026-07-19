# 支付网关（Payment Gateway）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [支付网关（Payment Gateway）](#支付网关payment-gateway)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [支付处理流程](#支付处理流程)
    - [基本流程](#基本流程)
  - [支付接口抽象](#支付接口抽象)
    - [Trait 定义](#trait-定义)
    - [Stripe 实现](#stripe-实现)
  - [实践示例](#实践示例)
    - [示例 1：支付服务](#示例-1支付服务)
    - [示例 2：支付重试机制](#示例-2支付重试机制)
    - [示例 3：支付验证](#示例-3支付验证)
  - [安全考虑](#安全考虑)
    - [1. 敏感数据加密](#1-敏感数据加密)
    - [2. 请求签名](#2-请求签名)
  - [参考资料](#参考资料)

---

## 概述

支付网关是金融科技应用的核心组件，负责处理支付请求、与支付提供商通信以及管理支付状态。Rust 的类型安全和性能使其成为构建支付系统的理想选择。

## 支付处理流程

### 基本流程

```rust
use serde::{Deserialize, Serialize};
use std::time::SystemTime;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaymentRequest {
    pub amount: f64,
    pub currency: String,
    pub payment_method: PaymentMethod,
    pub merchant_id: String,
    pub order_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaymentMethod {
    CreditCard { card_number: String, cvv: String, expiry: String },
    BankTransfer { account_number: String, routing_number: String },
    DigitalWallet { wallet_id: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaymentResponse {
    pub transaction_id: String,
    pub status: PaymentStatus,
    pub message: String,
    pub timestamp: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaymentStatus {
    Pending,
    Processing,
    Completed,
    Failed,
    Refunded,
}
```

## 支付接口抽象

### Trait 定义

```rust
use async_trait::async_trait;

#[async_trait]
pub trait PaymentGateway {
    async fn process_payment(
        &self,
        request: &PaymentRequest,
    ) -> Result<PaymentResponse, PaymentError>;

    async fn refund_payment(
        &self,
        transaction_id: &str,
        amount: Option<f64>,
    ) -> Result<PaymentResponse, PaymentError>;

    async fn get_payment_status(
        &self,
        transaction_id: &str,
    ) -> Result<PaymentStatus, PaymentError>;
}

#[derive(Debug)]
pub enum PaymentError {
    InvalidRequest(String),
    NetworkError(String),
    PaymentDeclined(String),
    GatewayError(String),
}
```

### Stripe 实现

```rust
use reqwest::Client;
use serde_json::json;

pub struct StripeGateway {
    client: Client,
    api_key: String,
    base_url: String,
}

impl StripeGateway {
    pub fn new(api_key: String) -> Self {
        StripeGateway {
            client: Client::new(),
            api_key,
            base_url: "https://api.stripe.com/v1".to_string(),
        }
    }
}

#[async_trait]
impl PaymentGateway for StripeGateway {
    async fn process_payment(
        &self,
        request: &PaymentRequest,
    ) -> Result<PaymentResponse, PaymentError> {
        let payment_intent = json!({
            "amount": (request.amount * 100.0) as u64,
            "currency": request.currency,
            "payment_method": match &request.payment_method {
                PaymentMethod::CreditCard { .. } => "card",
                _ => return Err(PaymentError::InvalidRequest("不支持的支付方式".to_string())),
            },
        });

        let response = self
            .client
            .post(&format!("{}/payment_intents", self.base_url))
            .bearer_auth(&self.api_key)
            .json(&payment_intent)
            .send()
            .await
            .map_err(|e| PaymentError::NetworkError(e.to_string()))?;

        if response.status().is_success() {
            let data: serde_json::Value = response
                .json()
                .await
                .map_err(|e| PaymentError::NetworkError(e.to_string()))?;

            Ok(PaymentResponse {
                transaction_id: data["id"].as_str().unwrap().to_string(),
                status: PaymentStatus::Processing,
                message: "支付处理中".to_string(),
                timestamp: SystemTime::now(),
            })
        } else {
            Err(PaymentError::PaymentDeclined("支付被拒绝".to_string()))
        }
    }

    async fn refund_payment(
        &self,
        transaction_id: &str,
        amount: Option<f64>,
    ) -> Result<PaymentResponse, PaymentError> {
        // 退款实现
        Ok(PaymentResponse {
            transaction_id: transaction_id.to_string(),
            status: PaymentStatus::Refunded,
            message: "退款成功".to_string(),
            timestamp: SystemTime::now(),
        })
    }

    async fn get_payment_status(
        &self,
        transaction_id: &str,
    ) -> Result<PaymentStatus, PaymentError> {
        // 查询支付状态
        Ok(PaymentStatus::Completed)
    }
}
```

## 实践示例

### 示例 1：支付服务

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct PaymentService {
    gateway: Arc<dyn PaymentGateway + Send + Sync>,
    transactions: Arc<RwLock<std::collections::HashMap<String, PaymentTransaction>>>,
}

#[derive(Debug, Clone)]
pub struct PaymentTransaction {
    pub id: String,
    pub request: PaymentRequest,
    pub response: PaymentResponse,
    pub created_at: SystemTime,
}

impl PaymentService {
    pub fn new(gateway: Arc<dyn PaymentGateway + Send + Sync>) -> Self {
        PaymentService {
            gateway,
            transactions: Arc::new(RwLock::new(std::collections::HashMap::new())),
        }
    }

    pub async fn process_payment(
        &self,
        request: PaymentRequest,
    ) -> Result<PaymentResponse, PaymentError> {
        // 验证请求
        self.validate_request(&request)?;

        // 处理支付
        let response = self.gateway.process_payment(&request).await?;

        // 保存交易记录
        let transaction = PaymentTransaction {
            id: response.transaction_id.clone(),
            request: request.clone(),
            response: response.clone(),
            created_at: SystemTime::now(),
        };

        let mut transactions = self.transactions.write().await;
        transactions.insert(transaction.id.clone(), transaction);

        Ok(response)
    }

    pub async fn get_transaction(
        &self,
        transaction_id: &str,
    ) -> Option<PaymentTransaction> {
        let transactions = self.transactions.read().await;
        transactions.get(transaction_id).cloned()
    }

    fn validate_request(&self, request: &PaymentRequest) -> Result<(), PaymentError> {
        if request.amount <= 0.0 {
            return Err(PaymentError::InvalidRequest("金额必须大于0".to_string()));
        }

        if request.currency.is_empty() {
            return Err(PaymentError::InvalidRequest("货币不能为空".to_string()));
        }

        Ok(())
    }
}
```

### 示例 2：支付重试机制

```rust
use tokio::time::{sleep, Duration};

pub struct PaymentRetry {
    max_retries: u32,
    retry_delay: Duration,
}

impl PaymentRetry {
    pub fn new(max_retries: u32, retry_delay: Duration) -> Self {
        PaymentRetry {
            max_retries,
            retry_delay,
        }
    }

    pub async fn process_with_retry(
        &self,
        gateway: &dyn PaymentGateway,
        request: &PaymentRequest,
    ) -> Result<PaymentResponse, PaymentError> {
        let mut last_error = None;

        for attempt in 0..self.max_retries {
            match gateway.process_payment(request).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.max_retries - 1 {
                        sleep(self.retry_delay * (attempt + 1)).await;
                    }
                }
            }
        }

        Err(last_error.unwrap_or(PaymentError::GatewayError("重试失败".to_string())))
    }
}
```

### 示例 3：支付验证

```rust
pub struct PaymentValidator;

impl PaymentValidator {
    pub fn validate_card(card_number: &str) -> bool {
        // Luhn 算法验证
        let digits: Vec<u32> = card_number
            .chars()
            .filter_map(|c| c.to_digit(10))
            .collect();

        if digits.len() < 13 || digits.len() > 19 {
            return false;
        }

        let mut sum = 0;
        let mut double = false;

        for &digit in digits.iter().rev() {
            let mut value = digit;
            if double {
                value *= 2;
                if value > 9 {
                    value -= 9;
                }
            }
            sum += value;
            double = !double;
        }

        sum % 10 == 0
    }

    pub fn validate_amount(amount: f64) -> bool {
        amount > 0.0 && amount <= 1_000_000.0
    }

    pub fn validate_currency(currency: &str) -> bool {
        let valid_currencies = ["USD", "EUR", "GBP", "CNY", "JPY"];
        valid_currencies.contains(&currency)
    }
}
```

## 安全考虑

### 1. 敏感数据加密

```rust
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};

pub struct PaymentEncryption {
    cipher: Aes256Gcm,
}

impl PaymentEncryption {
    pub fn new(key: &[u8; 32]) -> Self {
        let cipher = Aes256Gcm::new_from_slice(key).unwrap();
        PaymentEncryption { cipher }
    }

    pub fn encrypt_card_number(&self, card_number: &str) -> Result<Vec<u8>, String> {
        let nonce = Nonce::from_slice(b"unique nonce");
        self.cipher
            .encrypt(nonce, card_number.as_bytes())
            .map_err(|e| e.to_string())
    }

    pub fn decrypt_card_number(&self, encrypted: &[u8]) -> Result<String, String> {
        let nonce = Nonce::from_slice(b"unique nonce");
        let decrypted = self.cipher
            .decrypt(nonce, encrypted)
            .map_err(|e| e.to_string())?;
        String::from_utf8(decrypted).map_err(|e| e.to_string())
    }
}
```

### 2. 请求签名

```rust
use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

pub fn sign_request(data: &str, secret: &str) -> String {
    let mut mac = HmacSha256::new_from_slice(secret.as_bytes()).unwrap();
    mac.update(data.as_bytes());
    let result = mac.finalize();
    hex::encode(result.into_bytes())
}

pub fn verify_signature(data: &str, signature: &str, secret: &str) -> bool {
    let expected = sign_request(data, secret);
    expected == signature
}
```

## 参考资料

- [支付处理索引](./00_index.md)
- [金融科技索引](../00_index.md)
- [Stripe API 文档](https://stripe.com/docs/api)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回金融科技: [`../00_index.md`](../00_index.md)
