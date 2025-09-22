# 安全与隐私 (Security & Privacy)

## 概述

本文件夹包含Rust 1.90版本中AI/ML应用的安全和隐私保护技术、工具和最佳实践。

## 主要安全威胁

### 1. 模型安全

- **模型投毒**: 恶意训练数据导致模型行为异常
- **对抗攻击**: 精心设计的输入欺骗模型
- **模型窃取**: 通过查询推断模型参数
- **后门攻击**: 隐藏的恶意功能
- **数据泄露**: 训练数据中的敏感信息泄露

### 2. 数据安全

- **数据泄露**: 敏感数据未授权访问
- **数据篡改**: 训练数据被恶意修改
- **隐私泄露**: 个人隐私信息暴露
- **数据完整性**: 数据在传输和存储中被破坏
- **访问控制**: 未授权的数据访问

### 3. 系统安全

- **代码注入**: 恶意代码执行
- **缓冲区溢出**: 内存安全漏洞
- **权限提升**: 未授权的系统访问
- **网络攻击**: 网络通信被截获或篡改
- **依赖漏洞**: 第三方库的安全漏洞

## 安全技术

### 1. 加密技术

- **对称加密**: AES加密算法
- **非对称加密**: RSA、椭圆曲线加密
- **哈希函数**: SHA-256、BLAKE3
- **数字签名**: 数据完整性验证
- **密钥管理**: 安全的密钥存储和分发

### 2. 隐私保护技术

- **差分隐私**: 在统计查询中保护隐私
- **同态加密**: 在加密数据上直接计算
- **安全多方计算**: 多方协作而不泄露数据
- **联邦学习**: 分布式训练保护数据隐私
- **数据脱敏**: 移除或替换敏感信息

### 3. 访问控制

- **身份认证**: 用户身份验证
- **授权管理**: 权限控制和访问策略
- **审计日志**: 操作记录和监控
- **最小权限原则**: 只授予必要权限
- **零信任架构**: 不信任任何组件

## 安全工具

### 1. 加密库

```rust
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};

// AES-GCM加密
pub struct SecureEncryption {
    cipher: Aes256Gcm,
}

impl SecureEncryption {
    pub fn new(key: &[u8]) -> Result<Self, Box<dyn std::error::Error>> {
        let key = Key::from_slice(key);
        let cipher = Aes256Gcm::new(key);
        Ok(Self { cipher })
    }
    
    pub fn encrypt(&self, data: &[u8], nonce: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let nonce = Nonce::from_slice(nonce);
        let ciphertext = self.cipher.encrypt(nonce, data)?;
        Ok(ciphertext)
    }
    
    pub fn decrypt(&self, ciphertext: &[u8], nonce: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let nonce = Nonce::from_slice(nonce);
        let plaintext = self.cipher.decrypt(nonce, ciphertext)?;
        Ok(plaintext)
    }
}
```

### 2. 差分隐私

```rust
use rand::Rng;

// 拉普拉斯机制实现差分隐私
pub struct DifferentialPrivacy {
    epsilon: f64,
}

impl DifferentialPrivacy {
    pub fn new(epsilon: f64) -> Self {
        Self { epsilon }
    }
    
    pub fn add_noise(&self, value: f64, sensitivity: f64) -> f64 {
        let scale = sensitivity / self.epsilon;
        let noise = self.laplace_noise(scale);
        value + noise
    }
    
    fn laplace_noise(&self, scale: f64) -> f64 {
        let mut rng = rand::thread_rng();
        let u: f64 = rng.gen_range(-0.5..0.5);
        -scale * u.signum() * (1.0 - 2.0 * u.abs()).ln()
    }
}
```

### 3. 安全配置

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    pub encryption_enabled: bool,
    pub encryption_key: Option<String>,
    pub access_control: AccessControlConfig,
    pub audit_logging: bool,
    pub data_retention_days: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessControlConfig {
    pub require_authentication: bool,
    pub allowed_ips: Vec<String>,
    pub rate_limiting: RateLimitConfig,
    pub permissions: HashMap<String, Vec<String>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitConfig {
    pub requests_per_minute: u32,
    pub burst_size: u32,
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            encryption_enabled: true,
            encryption_key: None,
            access_control: AccessControlConfig {
                require_authentication: true,
                allowed_ips: Vec::new(),
                rate_limiting: RateLimitConfig {
                    requests_per_minute: 100,
                    burst_size: 10,
                },
                permissions: HashMap::new(),
            },
            audit_logging: true,
            data_retention_days: 30,
        }
    }
}
```

## 隐私保护实现

### 1. 数据脱敏

```rust
use regex::Regex;

pub struct DataAnonymizer {
    email_regex: Regex,
    phone_regex: Regex,
    ssn_regex: Regex,
}

impl DataAnonymizer {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            email_regex: Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b")?,
            phone_regex: Regex::new(r"\b\d{3}-\d{3}-\d{4}\b")?,
            ssn_regex: Regex::new(r"\b\d{3}-\d{2}-\d{4}\b")?,
        })
    }
    
    pub fn anonymize_text(&self, text: &str) -> String {
        let mut result = text.to_string();
        
        // 脱敏邮箱
        result = self.email_regex.replace_all(&result, "***@***.***").to_string();
        
        // 脱敏电话
        result = self.phone_regex.replace_all(&result, "***-***-****").to_string();
        
        // 脱敏SSN
        result = self.ssn_regex.replace_all(&result, "***-**-****").to_string();
        
        result
    }
    
    pub fn anonymize_personal_data(&self, data: &str) -> String {
        // 更复杂的个人数据脱敏逻辑
        self.anonymize_text(data)
    }
}
```

### 2. 访问控制

```rust
use std::collections::HashMap;
use std::sync::RwLock;

#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub name: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
}

pub struct AccessController {
    users: RwLock<HashMap<String, User>>,
    role_permissions: HashMap<String, Vec<String>>,
}

impl AccessController {
    pub fn new() -> Self {
        let mut role_permissions = HashMap::new();
        role_permissions.insert("admin".to_string(), vec!["read".to_string(), "write".to_string(), "delete".to_string()]);
        role_permissions.insert("user".to_string(), vec!["read".to_string()]);
        role_permissions.insert("analyst".to_string(), vec!["read".to_string(), "analyze".to_string()]);
        
        Self {
            users: RwLock::new(HashMap::new()),
            role_permissions,
        }
    }
    
    pub fn add_user(&self, user: User) {
        let mut users = self.users.write().unwrap();
        users.insert(user.id.clone(), user);
    }
    
    pub fn check_permission(&self, user_id: &str, permission: &str) -> bool {
        let users = self.users.read().unwrap();
        if let Some(user) = users.get(user_id) {
            // 检查直接权限
            if user.permissions.contains(&permission.to_string()) {
                return true;
            }
            
            // 检查角色权限
            for role in &user.roles {
                if let Some(permissions) = self.role_permissions.get(role) {
                    if permissions.contains(&permission.to_string()) {
                        return true;
                    }
                }
            }
        }
        false
    }
}
```

### 3. 审计日志

```rust
use serde::{Deserialize, Serialize};
use std::time::SystemTime;
use std::sync::Mutex;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditLog {
    pub timestamp: SystemTime,
    pub user_id: String,
    pub action: String,
    pub resource: String,
    pub result: String,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
}

pub struct AuditLogger {
    logs: Mutex<Vec<AuditLog>>,
    max_logs: usize,
}

impl AuditLogger {
    pub fn new(max_logs: usize) -> Self {
        Self {
            logs: Mutex::new(Vec::new()),
            max_logs,
        }
    }
    
    pub fn log(&self, log: AuditLog) {
        let mut logs = self.logs.lock().unwrap();
        logs.push(log);
        
        // 保持日志数量在限制内
        if logs.len() > self.max_logs {
            logs.remove(0);
        }
    }
    
    pub fn get_logs(&self) -> Vec<AuditLog> {
        let logs = self.logs.lock().unwrap();
        logs.clone()
    }
    
    pub fn search_logs(&self, user_id: Option<&str>, action: Option<&str>) -> Vec<AuditLog> {
        let logs = self.logs.lock().unwrap();
        logs.iter()
            .filter(|log| {
                if let Some(uid) = user_id {
                    if log.user_id != uid {
                        return false;
                    }
                }
                if let Some(act) = action {
                    if log.action != act {
                        return false;
                    }
                }
                true
            })
            .cloned()
            .collect()
    }
}
```

## 安全最佳实践

### 1. 开发阶段

- 使用安全的依赖库
- 定期更新依赖
- 进行安全代码审查
- 使用静态分析工具
- 实施安全测试

### 2. 部署阶段

- 使用HTTPS加密通信
- 实施访问控制
- 配置防火墙
- 启用审计日志
- 定期安全扫描

### 3. 运维阶段

- 监控安全事件
- 定期安全审计
- 更新安全补丁
- 备份和恢复
- 应急响应计划

## 合规性

### 1. 数据保护法规

- **GDPR**: 欧盟通用数据保护条例
- **CCPA**: 加州消费者隐私法案
- **HIPAA**: 健康保险可携性和责任法案
- **SOX**: 萨班斯-奥克斯利法案

### 2. 行业标准

- **ISO 27001**: 信息安全管理体系
- **SOC 2**: 服务组织控制
- **PCI DSS**: 支付卡行业数据安全标准
- **NIST**: 网络安全框架

## 相关资源

- [Rust安全最佳实践](https://github.com/rust-ai/rust-security-guide)
- [AI安全研究](https://github.com/rust-ai/ai-security-research)
- [隐私保护技术](https://github.com/rust-ai/privacy-preserving-techniques)
- [安全工具集合](https://github.com/rust-ai/security-tools)
