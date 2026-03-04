# Rust网络安全工具开发指南

> 一份关于使用Rust语言开发网络安全工具的完整指南，涵盖从基础密码学到高级入侵检测系统的所有内容。

---

## 目录

- [Rust网络安全工具开发指南](#rust网络安全工具开发指南)
  - [目录](#目录)
  - [1. 安全工具概述](#1-安全工具概述)
    - [1.1 Rust在安全领域的优势](#11-rust在安全领域的优势)
    - [1.2 内存安全与漏洞预防](#12-内存安全与漏洞预防)
    - [1.3 常见安全工具类型](#13-常见安全工具类型)
  - [2. 密码学基础](#2-密码学基础)
    - [2.1 ring库](#21-ring库)
    - [2.2 rustls（TLS实现）](#22-rustlstls实现)
    - [2.3 AEAD加密](#23-aead加密)
    - [2.4 密钥派生](#24-密钥派生)
  - [3. 网络扫描](#3-网络扫描)
    - [3.1 端口扫描器](#31-端口扫描器)
    - [3.2 异步扫描优化](#32-异步扫描优化)
  - [4. 漏洞检测](#4-漏洞检测)
    - [4.1 静态分析](#41-静态分析)
  - [5. 入侵检测](#5-入侵检测)
    - [5.1 数据包捕获（libpcap）](#51-数据包捕获libpcap)
    - [5.2 规则引擎](#52-规则引擎)
  - [6. 恶意软件分析](#6-恶意软件分析)
    - [6.1 沙箱环境](#61-沙箱环境)
  - [7. 安全监控](#7-安全监控)
    - [7.1 日志收集](#71-日志收集)
    - [7.2 SIEM集成](#72-siem集成)
  - [8. 完整示例：简单IDS系统](#8-完整示例简单ids系统)
  - [9. 安全编码实践](#9-安全编码实践)
    - [9.1 输入验证](#91-输入验证)
    - [9.2 错误处理](#92-错误处理)
    - [9.3 敏感数据处理](#93-敏感数据处理)
  - [10. 合规与审计](#10-合规与审计)
    - [10.1 安全标准](#101-安全标准)
    - [10.2 审计日志](#102-审计日志)
    - [10.3 取证工具](#103-取证工具)
  - [附录：常用依赖](#附录常用依赖)
  - [总结](#总结)

---

## 1. 安全工具概述

### 1.1 Rust在安全领域的优势

Rust语言因其独特的内存安全保证和零成本抽象特性，成为开发网络安全工具的理想选择：

| 特性 | 优势 | 安全影响 |
|------|------|----------|
| 所有权系统 | 编译时内存管理 | 消除UAF、双重释放 |
| 借用检查器 | 防止数据竞争 | 线程安全 |
| 类型系统 | 编译期错误捕获 | 减少运行时漏洞 |
| 零成本抽象 | 高性能 | 实时处理能力 |
| FFI安全 | 安全的C交互 | 安全的库集成 |

```rust
// Rust的所有权系统防止内存漏洞
fn process_sensitive_data(data: Vec<u8>) {
    // 数据所有权明确，不会出现use-after-free
    let processed = encrypt_data(data); // data被移动，之后无法访问
    // data.push(0); // 编译错误！data已被移动
    store_securely(processed);
}
```

### 1.2 内存安全与漏洞预防

Rust通过编译时检查消除常见的内存安全漏洞：

```rust
// 示例：缓冲区溢出防护
fn safe_buffer_access(buffer: &[u8], index: usize) -> Option<u8> {
    // 编译器强制边界检查
    buffer.get(index).copied()
}

// 示例：防止整数溢出
fn safe_addition(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b) // 返回None而不是溢出
}

// 示例：安全的字符串处理
fn safe_parse_input(input: &str) -> Result<i32, ParseIntError> {
    // 防止缓冲区溢出和格式字符串漏洞
    input.parse::<i32>()
}
```

### 1.3 常见安全工具类型

```text
安全工具生态系统
├── 防御性工具
│   ├── 防火墙
│   ├── 入侵检测/防御系统(IDS/IPS)
│   ├── 端点保护平台(EPP)
│   └── 安全信息与事件管理(SIEM)
├── 攻击性工具
│   ├── 渗透测试框架
│   ├── 漏洞扫描器
│   └── 网络侦察工具
├── 分析性工具
│   ├── 恶意软件分析沙箱
│   ├── 取证工具
│   └── 威胁情报平台
└── 加密工具
    ├── 密钥管理
    ├── 安全通信
    └── 数据保护
```

---

## 2. 密码学基础

### 2.1 ring库

`ring`是Rust生态中最流行的密码学库之一，提供安全的底层加密原语：

```rust
use ring::{aead, rand};
use ring::rand::SecureRandom;

/// 安全的随机数生成
fn generate_secure_random(length: usize) -> Result<Vec<u8>, ring::error::Unspecified> {
    let rng = rand::SystemRandom::new();
    let mut bytes = vec![0u8; length];
    rng.fill(&mut bytes)?;
    Ok(bytes)
}

/// AES-GCM加密实现
fn encrypt_aes_gcm(
    key: &[u8],
    nonce: &[u8],
    plaintext: &[u8],
    associated_data: &[u8],
) -> Result<Vec<u8>, ring::error::Unspecified> {
    let unbound_key = aead::UnboundKey::new(&aead::AES_256_GCM, key)?;
    let nonce_sequence = aead::Nonce::try_assume_unique_for_key(nonce)?;
    let mut sealing_key = aead::SealingKey::new(unbound_key, nonce_sequence);

    let mut in_out = plaintext.to_vec();
    let tag = sealing_key.seal_in_place_separate_tag(
        aead::Aad::from(associated_data),
        &mut in_out,
    )?;

    in_out.extend_from_slice(tag.as_ref());
    Ok(in_out)
}
```

### 2.2 rustls（TLS实现）

`rustls`是一个现代、安全的TLS库，完全用Rust编写：

```rust
use rustls::{ClientConfig, Certificate};
use std::sync::Arc;

/// 配置TLS客户端
fn configure_tls_client(root_certs: Vec<Certificate>) -> Arc<ClientConfig> {
    let config = ClientConfig::builder()
        .with_safe_defaults()
        .with_root_certificates(root_certs.into())
        .with_no_client_auth();

    Arc::new(config)
}
```

### 2.3 AEAD加密

```rust
use chacha20poly1305::{
    aead::{Aead, KeyInit},
    ChaCha20Poly1305, Nonce, Key
};

/// ChaCha20-Poly1305加密（适用于移动设备）
struct ChaChaCipher {
    cipher: ChaCha20Poly1305,
}

impl ChaChaCipher {
    fn new(key: &[u8; 32]) -> Self {
        let key = Key::from_slice(key);
        Self {
            cipher: ChaCha20Poly1305::new(key),
        }
    }

    fn encrypt(
        &self,
        nonce: &[u8; 12],
        plaintext: &[u8],
    ) -> Result<Vec<u8>, chacha20poly1305::aead::Error> {
        let nonce = Nonce::from_slice(nonce);
        self.cipher.encrypt(nonce, plaintext)
    }
}
```

### 2.4 密钥派生

```rust
use argon2::{self, Config, ThreadMode, Variant, Version};

/// Argon2id密钥派生（推荐用于密码哈希）
fn derive_key_argon2id(
    password: &[u8],
    salt: &[u8],
    output_len: usize,
) -> Result<Vec<u8>, argon2::Error> {
    let config = Config {
        variant: Variant::Argon2id,
        version: Version::Version13,
        mem_cost: 65536,  // 64 MB
        time_cost: 3,
        lanes: 4,
        thread_mode: ThreadMode::Parallel,
        secret: &[],
        ad: &[],
        hash_length: output_len as u32,
    };

    argon2::hash_raw(password, salt, &config)
}
```

---

## 3. 网络扫描

### 3.1 端口扫描器

```rust
use tokio::net::TcpStream;
use tokio::time::{timeout, Duration};
use futures::stream::{self, StreamExt};

#[derive(Debug, Clone)]
struct PortScanResult {
    port: u16,
    state: PortState,
    service_hint: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
enum PortState {
    Open,
    Closed,
    Filtered,
}

struct AsyncPortScanner {
    target: String,
    timeout: Duration,
    concurrency: usize,
}

impl AsyncPortScanner {
    async fn connect_scan(&self, ports: Vec<u16>) -> Vec<PortScanResult> {
        let target = self.target.clone();

        stream::iter(ports)
            .map(|port| {
                let target = target.clone();
                let timeout = self.timeout;
                async move {
                    let addr = format!("{}:{}", target, port);
                    match timeout(timeout, TcpStream::connect(&addr)).await {
                        Ok(Ok(_)) => Some(PortScanResult {
                            port,
                            state: PortState::Open,
                            service_hint: Self::guess_service(port),
                        }),
                        Ok(Err(_)) => Some(PortScanResult {
                            port,
                            state: PortState::Closed,
                            service_hint: None,
                        }),
                        Err(_) => Some(PortScanResult {
                            port,
                            state: PortState::Filtered,
                            service_hint: None,
                        }),
                    }
                }
            })
            .buffer_unordered(self.concurrency)
            .filter_map(|result| async move { result })
            .collect()
            .await
    }

    fn guess_service(port: u16) -> Option<String> {
        match port {
            21 => Some("FTP".to_string()),
            22 => Some("SSH".to_string()),
            80 => Some("HTTP".to_string()),
            443 => Some("HTTPS".to_string()),
            3306 => Some("MySQL".to_string()),
            _ => None,
        }
    }
}
```

### 3.2 异步扫描优化

```rust
use tokio::sync::{mpsc, Semaphore};
use std::sync::Arc;

struct AsyncScanManager {
    semaphore: Arc<Semaphore>,
}

impl AsyncScanManager {
    async fn distributed_scan(
        &self,
        targets: Vec<String>,
        ports: Vec<u16>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut handles = Vec::new();

        for target in targets {
            for port in &ports {
                let _permit = self.semaphore.clone().acquire_owned().await?;
                let target = target.clone();
                let port = *port;

                let handle = tokio::spawn(async move {
                    let _ = Self::scan_single(&target, port).await;
                });

                handles.push(handle);
            }
        }

        for handle in handles {
            handle.await?;
        }

        Ok(())
    }

    async fn scan_single(target: &str, port: u16) -> ScanResult {
        let addr = format!("{}:{}", target, port);
        let start = std::time::Instant::now();

        match timeout(Duration::from_secs(5), TcpStream::connect(&addr)).await {
            Ok(Ok(_)) => ScanResult {
                target: target.to_string(),
                port,
                state: PortState::Open,
                latency: start.elapsed(),
            },
            _ => ScanResult {
                target: target.to_string(),
                port,
                state: PortState::Filtered,
                latency: Duration::from_secs(5),
            },
        }
    }
}
```

---

## 4. 漏洞检测

### 4.1 静态分析

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum Severity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

#[derive(Debug, Clone)]
struct AnalysisRule {
    id: String,
    name: String,
    severity: Severity,
    pattern: String,
}

struct SecurityAnalyzer {
    rules: Vec<AnalysisRule>,
    findings: Vec<Finding>,
}

#[derive(Debug, Clone)]
struct Finding {
    file: String,
    line: usize,
    rule: AnalysisRule,
    message: String,
}

impl SecurityAnalyzer {
    fn new() -> Self {
        let rules = vec![
            AnalysisRule {
                id: "RUST-001".to_string(),
                name: "Unsafe Block Usage".to_string(),
                severity: Severity::High,
                pattern: "unsafe".to_string(),
            },
            AnalysisRule {
                id: "RUST-002".to_string(),
                name: "Unwrap Usage".to_string(),
                severity: Severity::Medium,
                pattern: "unwrap()".to_string(),
            },
        ];

        Self {
            rules,
            findings: Vec::new(),
        }
    }

    fn analyze_file(&mut self, file_path: &str, source: &str) {
        for (line_num, line) in source.lines().enumerate() {
            for rule in &self.rules {
                if line.contains(&rule.pattern) {
                    self.findings.push(Finding {
                        file: file_path.to_string(),
                        line: line_num + 1,
                        rule: rule.clone(),
                        message: format!("Found: {}", rule.name),
                    });
                }
            }
        }
    }

    fn generate_report(&self) -> AnalysisReport {
        let mut severity_counts = HashMap::new();

        for finding in &self.findings {
            *severity_counts.entry(finding.rule.severity.clone()).or_insert(0) += 1;
        }

        AnalysisReport {
            total_findings: self.findings.len(),
            severity_counts,
        }
    }
}

#[derive(Debug)]
struct AnalysisReport {
    total_findings: usize,
    severity_counts: HashMap<Severity, usize>,
}
```

---

## 5. 入侵检测

### 5.1 数据包捕获（libpcap）

```rust
use pcap::{Capture, Device};
use std::time::SystemTime;

#[derive(Debug, Clone, Default)]
struct CapturedPacket {
    timestamp: u64,
    length: u32,
    data: Vec<u8>,
}

struct PacketCaptureEngine {
    device: String,
}

impl PacketCaptureEngine {
    fn new(device: String) -> Self {
        Self { device }
    }

    fn start_capture<F>(&self, mut handler: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(&CapturedPacket),
    {
        let mut cap = Capture::from_device(self.device.as_str())?
            .promisc(true)
            .snaplen(65535)
            .open()?;

        loop {
            match cap.next_packet() {
                Ok(packet) => {
                    let captured = CapturedPacket {
                        timestamp: SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)?
                            .as_secs(),
                        length: packet.header.len,
                        data: packet.data.to_vec(),
                    };
                    handler(&captured);
                }
                Err(pcap::Error::TimeoutExpired) => continue,
                Err(e) => {
                    eprintln!("Capture error: {}", e);
                    break;
                }
            }
        }

        Ok(())
    }
}
```

### 5.2 规则引擎

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct IdsRule {
    id: String,
    name: String,
    description: String,
    severity: Severity,
    enabled: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum RuleAction {
    Alert,
    Log,
    Drop,
}

struct RuleEngine {
    rules: Vec<IdsRule>,
}

impl RuleEngine {
    fn new() -> Self {
        Self { rules: Vec::new() }
    }

    fn load_rules(&mut self, rules: Vec<IdsRule>) {
        self.rules = rules;
    }

    fn evaluate(&self, packet: &CapturedPacket) -> Vec<RuleMatch> {
        let mut matches = Vec::new();

        for rule in &self.rules {
            if !rule.enabled {
                continue;
            }

            // 规则匹配逻辑
            if self.match_rule(packet, rule) {
                matches.push(RuleMatch {
                    rule_id: rule.id.clone(),
                    rule_name: rule.name.clone(),
                    severity: rule.severity.clone(),
                });
            }
        }

        matches
    }

    fn match_rule(&self, _packet: &CapturedPacket, _rule: &IdsRule) -> bool {
        // 实际匹配逻辑
        false
    }
}

#[derive(Debug)]
struct RuleMatch {
    rule_id: String,
    rule_name: String,
    severity: Severity,
}
```

---

## 6. 恶意软件分析

### 6.1 沙箱环境

```rust
use std::process::Command;
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
struct SandboxConfig {
    timeout: Duration,
    memory_limit: usize,
    network_isolation: bool,
}

struct Sandbox {
    config: SandboxConfig,
    container_id: Option<String>,
}

impl Sandbox {
    fn new(config: SandboxConfig) -> Self {
        Self {
            config,
            container_id: None,
        }
    }

    fn initialize(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let container_name = format!("sandbox-{}", uuid::Uuid::new_v4());

        let output = Command::new("docker")
            .args(&[
                "run", "-d", "--rm",
                "--name", &container_name,
                "--memory", &format!("{}m", self.config.memory_limit),
            ])
            .arg("sandbox-image:latest")
            .arg("sleep")
            .arg("3600")
            .output()?;

        if output.status.success() {
            self.container_id = Some(
                String::from_utf8_lossy(&output.stdout).trim().to_string()
            );
            Ok(())
        } else {
            Err("Failed to create container".into())
        }
    }
}

#[derive(Debug)]
struct SandboxExecutionResult {
    exit_code: Option<i32>,
    execution_time: Duration,
}
```

---

## 7. 安全监控

### 7.1 日志收集

```rust
use serde::{Serialize, Deserialize};
use std::time::SystemTime;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SecurityEvent {
    #[serde(rename = "@timestamp")]
    timestamp: String,
    #[serde(rename = "event.kind")]
    event_kind: String,
    #[serde(rename = "event.severity")]
    event_severity: i32,
    message: String,
}

impl SecurityEvent {
    fn new(kind: &str, severity: i32, message: &str) -> Self {
        Self {
            timestamp: format!("{:?}", SystemTime::now()),
            event_kind: kind.to_string(),
            event_severity: severity,
            message: message.to_string(),
        }
    }
}

struct LogCollector {
    events: Vec<SecurityEvent>,
}

impl LogCollector {
    fn new() -> Self {
        Self { events: Vec::new() }
    }

    fn collect(&mut self, event: SecurityEvent) {
        self.events.push(event);
    }
}
```

### 7.2 SIEM集成

```rust
use reqwest::Client;

struct ElasticsearchConnector {
    endpoint: String,
    index: String,
    buffer: Vec<SecurityEvent>,
}

impl ElasticsearchConnector {
    fn new(endpoint: String, index: String) -> Self {
        Self {
            endpoint,
            index,
            buffer: Vec::new(),
        }
    }

    async fn send_event(&mut self, event: SecurityEvent) -> Result<(), Box<dyn std::error::Error>> {
        self.buffer.push(event);

        if self.buffer.len() >= 100 {
            self.flush().await?;
        }

        Ok(())
    }

    async fn flush(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let client = Client::new();
        let url = format!("{}/{}/_bulk", self.endpoint, self.index);

        // 构建批量请求
        let mut bulk_body = String::new();
        for event in &self.buffer {
            let action = serde_json::json!({
                "index": { "_index": self.index }
            });
            bulk_body.push_str(&action.to_string());
            bulk_body.push('\n');
            bulk_body.push_str(&serde_json::to_string(event)?);
            bulk_body.push('\n');
        }

        client.post(&url)
            .header("Content-Type", "application/x-ndjson")
            .body(bulk_body)
            .send()
            .await?;

        self.buffer.clear();
        Ok(())
    }
}
```

---

## 8. 完整示例：简单IDS系统

```rust
use tokio::sync::{mpsc, broadcast};

struct SimpleIDS {
    rules: Vec<IdsRule>,
    alert_tx: broadcast::Sender<Alert>,
}

#[derive(Debug, Clone)]
struct Alert {
    id: String,
    rule_id: String,
    rule_name: String,
    severity: Severity,
    description: String,
}

impl SimpleIDS {
    fn new() -> Self {
        let (alert_tx, _) = broadcast::channel(1000);

        Self {
            rules: Vec::new(),
            alert_tx,
        }
    }

    async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let (packet_tx, mut packet_rx) = mpsc::channel(10000);

        // 启动数据包捕获
        let capture_handle = tokio::spawn(self.start_capture(packet_tx));

        // 处理数据包
        let alert_tx = self.alert_tx.clone();
        let rules = self.rules.clone();

        let engine_handle = tokio::spawn(async move {
            let mut engine = RuleEngine::new();
            engine.load_rules(rules);

            while let Some(packet) = packet_rx.recv().await {
                let matches = engine.evaluate(&packet);
                for m in matches {
                    let alert = Alert {
                        id: format!("ALT-{}", uuid::Uuid::new_v4()),
                        rule_id: m.rule_id,
                        rule_name: m.rule_name,
                        severity: m.severity,
                        description: format!("Match on rule {}", m.rule_name),
                    };
                    let _ = alert_tx.send(alert);
                }
            }
        });

        tokio::try_join!(capture_handle, engine_handle)?;
        Ok(())
    }

    async fn start_capture(&self, packet_tx: mpsc::Sender<CapturedPacket>) {
        let engine = PacketCaptureEngine::new("eth0".to_string());
        engine.start_capture(move |packet| {
            let _ = packet_tx.try_send(packet.clone());
        }).ok();
    }
}
```

---

## 9. 安全编码实践

### 9.1 输入验证

```rust
pub mod input_validation {
    use regex::Regex;

    pub fn validate_ip(ip: &str) -> Result<(), String> {
        let parts: Vec<&str> = ip.split('.').collect();

        if parts.len() != 4 {
            return Err("Invalid IP format".to_string());
        }

        for part in parts {
            match part.parse::<u8>() {
                Ok(_) => continue,
                Err(_) => return Err(format!("Invalid IP octet: {}", part)),
            }
        }

        Ok(())
    }

    pub fn validate_path(path: &str) -> Result<(), String> {
        if path.contains("..") {
            return Err("Path traversal detected".to_string());
        }
        Ok(())
    }
}
```

### 9.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SecurityError {
    #[error("Invalid input: {0}")]
    InvalidInput(String),

    #[error("Authentication failed")]
    AuthenticationFailed,

    #[error("Authorization denied")]
    AuthorizationDenied,
}
```

### 9.3 敏感数据处理

```rust
use zeroize::{Zeroize, Zeroizing};

pub struct SecureKey {
    data: Zeroizing<Vec<u8>>,
}

impl SecureKey {
    pub fn new(data: Vec<u8>) -> Self {
        Self {
            data: Zeroizing::new(data),
        }
    }
}

impl Drop for SecureKey {
    fn drop(&mut self) {
        // 内存自动清零
    }
}
```

---

## 10. 合规与审计

### 10.1 安全标准

```rust
pub mod compliance {
    use std::collections::HashMap;

    #[derive(Debug)]
    pub struct ComplianceCheck {
        standard: String,
        requirements: Vec<Requirement>,
    }

    #[derive(Debug)]
    pub struct Requirement {
        id: String,
        description: String,
        check_fn: fn() -> bool,
    }

    pub struct ComplianceChecker;

    impl ComplianceChecker {
        pub fn check_pci_dss() -> ComplianceReport {
            let checks = vec![
                ("Req 4.1", "Use strong cryptography", true),
                ("Req 8.2", "Strong authentication", true),
            ];

            ComplianceReport {
                standard: "PCI DSS".to_string(),
                checks,
                passed: checks.iter().all(|(_, _, p)| *p),
            }
        }
    }

    #[derive(Debug)]
    pub struct ComplianceReport {
        standard: String,
        checks: Vec<(&'static str, &'static str, bool)>,
        passed: bool,
    }
}
```

### 10.2 审计日志

```rust
pub struct AuditLogger {
    log_file: std::fs::File,
}

impl AuditLogger {
    pub fn new(path: &str) -> Result<Self, std::io::Error> {
        let log_file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)?;

        Ok(Self { log_file })
    }

    pub fn log(&mut self, event: &AuditEvent) -> Result<(), std::io::Error> {
        let entry = format!("{}\n", serde_json::to_string(event).unwrap());
        std::io::Write::write_all(&mut self.log_file, entry.as_bytes())?;
        Ok(())
    }
}

#[derive(Debug, serde::Serialize)]
pub struct AuditEvent {
    timestamp: String,
    user: String,
    action: String,
    resource: String,
    result: String,
}
```

### 10.3 取证工具

```rust
pub mod forensics {
    use std::fs;
    use std::path::Path;

    /// 文件哈希计算
    pub fn compute_hash(path: &Path) -> Result<String, std::io::Error> {
        use sha2::{Sha256, Digest};

        let data = fs::read(path)?;
        let hash = Sha256::digest(&data);
        Ok(format!("{:x}", hash))
    }

    /// 文件元数据提取
    pub fn extract_metadata(path: &Path) -> Result<FileMetadata, std::io::Error> {
        let metadata = fs::metadata(path)?;

        Ok(FileMetadata {
            size: metadata.len(),
            created: format!("{:?}", metadata.created()),
            modified: format!("{:?}", metadata.modified()),
            accessed: format!("{:?}", metadata.accessed()),
        })
    }

    #[derive(Debug)]
    pub struct FileMetadata {
        size: u64,
        created: String,
        modified: String,
        accessed: String,
    }
}
```

---

## 附录：常用依赖

```toml
[dependencies]
# 密码学
ring = "0.16"
rustls = "0.21"
chacha20poly1305 = "0.10"
argon2 = "0.5"
pbkdf2 = "0.12"

# 网络
pcap = "1.0"
tokio = { version = "1.0", features = ["full"] }
reqwest = { version = "0.11", features = ["json"] }

# 数据处理
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde_yaml = "0.9"

# 模式匹配
regex = "1.0"

# 安全编码
zeroize = "1.6"
thiserror = "1.0"

# 日志
log = "0.4"
env_logger = "0.10"

# 测试
proptest = "1.0"
```

---

## 总结

本指南涵盖了使用Rust开发网络安全工具的完整知识体系，从基础的密码学到复杂的入侵检测系统。Rust的内存安全保证和零成本抽象使其成为安全工具开发的理想选择。

主要要点：

1. **利用Rust的安全特性**：所有权系统和借用检查器可消除常见的内存漏洞
2. **使用成熟的加密库**：如ring和rustls，避免自行实现加密算法
3. **异步编程**：利用tokio实现高性能网络工具
4. **全面的测试**：包括单元测试、集成测试和模糊测试
5. **安全编码实践**：输入验证、错误处理和敏感数据保护

---

*文档版本：1.0*
*最后更新：2026年3月*
*作者：Rust安全工具开发团队*
