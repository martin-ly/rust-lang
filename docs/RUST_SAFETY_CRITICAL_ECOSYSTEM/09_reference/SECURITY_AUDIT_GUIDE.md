# 安全审计指南

## 概述

本文档提供Rust安全关键系统的安全审计流程、检查清单和最佳实践，确保系统符合安全要求。

---

## 1. 审计框架

### 1.1 审计类型

```
安全审计类型:

代码审计:
├── 静态代码分析
├── 依赖审计
├── 配置审计
└── 文档审计

运行时审计:
├── 行为监控
├── 性能分析
├── 资源使用
└── 异常检测

供应链审计:
├── 依赖来源
├── 许可证合规
├── 漏洞扫描
└── SBOM验证
```

### 1.2 审计生命周期

```
开发阶段审计:
├── 每日: 自动扫描
├── 每周: 依赖检查
├── 每月: 深度审计
└── 发布前: 全面审计

运营阶段审计:
├── 持续: 行为监控
├── 定期: 漏洞评估
├── 事件: 应急响应
└── 年度: 全面审查
```

---

## 2. 静态代码审计

### 2.1 审计工具链

```bash
# 1. Clippy全面检查
cargo clippy --all-targets --all-features -- -W clippy::all -W clippy::pedantic

# 2. 安全审计
cargo audit

# 3. 许可证检查
cargo deny check licenses

# 4. 漏洞扫描
cargo audit --json

# 5. 代码重复检测
cargo install cargo-bloat
cargo bloat --release
```

### 2.2 unsafe代码审计

```rust
/// unsafe代码审计检查表
///
/// 审计要点:
/// 1. SAFETY注释完整性
/// 2. 前置条件验证
/// 3. 不变量维护
/// 4. 边界检查
/// 5. 对齐要求

/// ✅ 良好示例
///
/// # Safety
///
/// 调用者必须确保:
/// - `ptr` 是非空的有效指针
/// - `ptr` 已正确对齐
/// - `ptr` 指向已初始化的内存
pub unsafe fn read_value<T>(ptr: *const T) -> T {
    // SAFETY: 调用者已确保前提条件
    ptr.read()
}

/// ❌ 不良示例 (缺少文档)
pub unsafe fn bad_read<T>(ptr: *const T) -> T {
    ptr.read()  // 缺少SAFETY注释
}

/// 审计脚本
#[cfg(test)]
mod audit {
    use std::process::Command;

    #[test]
    fn audit_unsafe_usage() {
        // 检查unsafe代码比例
        let output = Command::new("cargo")
            .args(&["geiger", "--output-format", "json"])
            .output()
            .expect("Failed to run cargo-geiger");

        // 解析输出，确保unsafe比例<1%
        let report: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap();

        let unsafe_ratio = report["ratio"].as_f64().unwrap();
        assert!(unsafe_ratio < 0.01, "Too much unsafe code: {}", unsafe_ratio);
    }
}
```

---

## 3. 依赖安全审计

### 3.1 依赖评估矩阵

| 评估项 | 权重 | 检查方法 |
|--------|------|----------|
| **维护状态** | 30% | 最近更新时间 |
| **社区活跃度** | 20% | GitHub stars/forks |
| **安全历史** | 25% | 漏洞数据库查询 |
| **许可证兼容** | 15% | 许可证扫描 |
| **代码质量** | 10% | 静态分析 |

### 3.2 依赖审计配置

```toml
# deny.toml
[graph]
targets = [
    { triple = "x86_64-unknown-linux-gnu" },
    { triple = "thumbv7em-none-eabihf" },
]

[advisories]
db-path = "~/.cargo/advisory-dbs"
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"
yanked = "deny"
severity-threshold = "medium"

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
    "ISC",
]
deny = [
    "GPL-2.0",
    "GPL-3.0",
    "AGPL-3.0",
]
copyleft = "deny"

[bans]
multiple-versions = "warn"
wildcards = "deny"
highlight = "all"

# 禁止特定crate
deny = [
    { name = "crate-with-vulnerabilities" },
    { name = "unmaintained-crate" },
]

[sources]
unknown-registry = "deny"
unknown-git = "deny"
allow-registry = [
    "https://github.com/rust-lang/crates.io-index",
]
```

### 3.3 SBOM生成与验证

```bash
# 生成SBOM
cargo install cargo-sbom
cargo sbom > sbom.json

# 验证SBOM
cargo sbom --validate

# 导入依赖图
cargo tree --edges normal --prefix none | sort | uniq
```

---

## 4. 运行时安全监控

### 4.1 安全事件检测

```rust
/// 运行时安全监控
use std::sync::atomic::{AtomicU64, Ordering};

pub struct SecurityMonitor {
    anomaly_count: AtomicU64,
    last_check: AtomicU64,
}

impl SecurityMonitor {
    pub fn new() -> Self {
        Self {
            anomaly_count: AtomicU64::new(0),
            last_check: AtomicU64::new(0),
        }
    }

    /// 检测异常行为
    pub fn check_behavior(&self, event: SecurityEvent) -> SecurityAction {
        match event {
            SecurityEvent::InvalidMemoryAccess => {
                self.anomaly_count.fetch_add(1, Ordering::Relaxed);
                SecurityAction::Alert
            }
            SecurityEvent::TimingAnomaly { expected, actual } => {
                if actual > expected * 2 {
                    self.anomaly_count.fetch_add(1, Ordering::Relaxed);
                    SecurityAction::Investigate
                } else {
                    SecurityAction::Allow
                }
            }
            SecurityEvent::ResourceExhaustion { resource, usage } => {
                if usage > 0.9 {
                    SecurityAction::Throttle
                } else {
                    SecurityAction::Allow
                }
            }
        }
    }

    /// 获取安全评分
    pub fn security_score(&self) -> u8 {
        let anomalies = self.anomaly_count.load(Ordering::Relaxed);
        match anomalies {
            0 => 100,
            1..=5 => 80,
            6..=10 => 60,
            11..=20 => 40,
            _ => 20,
        }
    }
}

pub enum SecurityEvent {
    InvalidMemoryAccess,
    TimingAnomaly { expected: u64, actual: u64 },
    ResourceExhaustion { resource: String, usage: f32 },
}

pub enum SecurityAction {
    Allow,
    Alert,
    Investigate,
    Throttle,
    Block,
}
```

### 4.2 入侵检测

```rust
/// 简单的入侵检测系统
pub struct IntrusionDetector {
    pattern_db: Vec<AttackPattern>,
    event_log: RingBuffer<SecurityEvent, 1000>,
}

struct AttackPattern {
    name: &'static str,
    signature: Vec<EventSignature>,
    severity: Severity,
}

impl IntrusionDetector {
    pub fn analyze(&mut self, event: SecurityEvent) -> Vec<Alert> {
        self.event_log.push(event);

        let mut alerts = Vec::new();

        for pattern in &self.pattern_db {
            if self.matches_pattern(pattern) {
                alerts.push(Alert {
                    name: pattern.name,
                    severity: pattern.severity,
                    timestamp: current_time(),
                });
            }
        }

        alerts
    }

    fn matches_pattern(&self, pattern: &AttackPattern) -> bool {
        // 模式匹配逻辑
        true
    }
}
```

---

## 5. 审计报告模板

### 5.1 执行摘要

```markdown
# 安全审计报告

## 执行摘要

| 项目 | 结果 |
|------|------|
| **审计日期** | 2026-03-18 |
| **审计范围** | 全系统 |
| **总体评级** | 🟢 通过 |
| **关键发现** | 0 |
| **高风险** | 2 |
| **中风险** | 5 |
| **低风险** | 12 |

## 关键发现

### 发现1: 依赖过时
- **严重性**: 中
- **描述**: crate X 版本过旧，存在已知漏洞
- **修复**: 升级到 v2.0.0

### 发现2: unsafe代码缺少文档
- **严重性**: 中
- **描述**: src/ffi.rs:45 缺少SAFETY注释
- **修复**: 添加完整文档

## 建议

1. 建立定期依赖更新机制
2. 加强代码审查
3. 增加自动化安全测试
```

### 5.2 详细审计清单

```
代码审计:
□ unsafe代码审查
□ 边界检查验证
□ 错误处理审查
□ 并发安全分析
□ 资源泄漏检查

依赖审计:
□ 漏洞扫描
□ 许可证检查
□ 维护状态评估
□ 供应链风险分析
□ SBOM完整性

配置审计:
□ 编译标志检查
□ 功能标志审查
□ 环境变量安全
□ 密钥管理审查
□ 日志配置审查
```

---

## 6. 持续安全监控

### 6.1 CI集成

```yaml
# .github/workflows/security.yml
name: Security Audit

on:
  schedule:
    - cron: '0 0 * * 0'  # 每周日
  push:
    branches: [main]

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run cargo audit
        uses: actions-rust-lang/audit@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}

      - name: Check licenses
        run: cargo deny check

      - name: Scan for secrets
        uses: trufflesecurity/trufflehog@main
        with:
          path: ./
          base: main
          head: HEAD

      - name: Generate SBOM
        run: |
          cargo install cargo-sbom
          cargo sbom > sbom.json

      - name: Upload SBOM
        uses: actions/upload-artifact@v3
        with:
          name: sbom
          path: sbom.json
```

### 6.2 安全指标仪表板

```rust
/// 安全指标收集
pub struct SecurityMetrics {
    pub vulnerability_count: AtomicU64,
    pub dependency_age: AtomicU64,
    pub code_coverage: AtomicU64,
    pub unsafe_ratio: AtomicU64,
}

impl SecurityMetrics {
    pub fn generate_report(&self) -> SecurityReport {
        SecurityReport {
            vulnerability_count: self.vulnerability_count.load(Ordering::Relaxed),
            avg_dependency_age_days: self.dependency_age.load(Ordering::Relaxed),
            code_coverage_percent: self.code_coverage.load(Ordering::Relaxed),
            unsafe_code_ratio: self.unsafe_ratio.load(Ordering::Relaxed) as f64 / 10000.0,
            timestamp: current_time(),
        }
    }
}
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*安全是持续的过程，不是一次性的活动。*
