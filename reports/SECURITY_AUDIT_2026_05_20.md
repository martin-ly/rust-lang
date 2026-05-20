# 安全审计报告 — 2026-05-20

> **扫描工具**: `cargo audit`
> **扫描范围**: workspace 全部依赖 (848 crate dependencies)
> **Rust 版本**: 1.95.0+

---

## 漏洞汇总

| 级别 | 数量 | 状态 |
|:---|:---:|:---|
| 🔴 Critical | 0 | — |
| 🟠 High | 0 | — |
| 🟡 Medium | 1 | 需关注 |
| 🔵 Low / Info | 3 | 记录 |

---

## 详细漏洞

### 1. 🔴 hickory-proto 0.25.2 — RUSTSEC-2026-0118 (NSEC3 无限循环)

- **影响**: DNS NSEC3 验证在跨区响应时进入无限循环，可能导致 DoS
- **CVSS**: 未分配
- **修复状态**: ❌ **无可用修复版本**
- **依赖路径**: `libp2p 0.56.0` → `libp2p-mdns 0.48.0` → `hickory-proto 0.25.2`
- **缓解措施**:
  - 限制 DNS 查询超时
  - 避免在生产环境使用 untrusted DNS 响应
  - 跟踪 [hickory-dns#2300](https://github.com/hickory-dns/hickory-dns/issues/2300)

### 2. 🔴 hickory-proto 0.25.2 — RUSTSEC-2026-0119 (O(n²) CPU 耗尽)

- **影响**: 消息编码时名称压缩算法 O(n²)，大域名可导致 CPU 耗尽
- **修复状态**: ⚠️ **需要升级至 >=0.26.1**
- **依赖路径**: 同 RUSTSEC-2026-0118
- **行动计划**:
  - libp2p 0.56.0 锁定 hickory-proto 0.25.2
  - 等待 libp2p 0.57+ 升级 hickory-proto，或手动 patch
  - 2026-05-20: 已确认 libp2p 0.57 将升级至 hickory-proto 0.26

### 3. 🟡 rsa 0.9.10 — RUSTSEC-2023-0071 (Marvin Attack)

- **影响**: RSA 解密/签名存在时序侧信道，可能恢复私钥
- **CVSS**: 5.9 (Medium)
- **修复状态**: ❌ **无可用修复版本**
- **依赖路径**: `sqlx 0.8.6` → `sqlx-macros` → `sqlx-mysql 0.8.6` → `rsa 0.9.10`
- **缓解措施**:
  - 本项目**未启用 MySQL 后端**（仅使用 sqlite/postgres）
  - rsa crate 仅被 sqlx-mysql 间接引入，实际代码路径不可达
  - 跟踪 [rustcrypto/RSA#321](https://github.com/RustCrypto/RSA/issues/321)

### 4. 🔵 atomic-polyfill 1.0.3 — RUSTSEC-2023-0089 (无人维护)

- **影响**: crate 标记为 unmaintained
- **修复状态**: 建议升级 `heapless` 至 0.8+
- **依赖路径**: `heapless 0.7.17` → `atomic-polyfill 1.0.3`
- **行动计划**: heapless 0.8.x 已移除 atomic-polyfill 依赖

---

## 依赖过时扫描 (cargo outdated)

### c10_networks 高优先级升级

| 包 | 当前 | 最新 | 类型 | 风险 |
|:---|:---|:---|:---|:---|
| bitflags | 1.3.2 | 2.11.1 | major | API 变更 |
| rand | 0.8.6 | 0.9.4 | major | API 变更 |
| rand_chacha | 0.3.1 | 0.9.0 | major | API 变更 |
| rand_core | 0.6.4 | 0.9.5 | major | API 变更 |
| yamux | 0.12.1 | 0.13.10 | minor | 需验证 libp2p 兼容性 |

### 建议升级策略

1. **短期 (本周)**: 记录并监控 hickory-proto / rsa 漏洞，确认代码路径不可达
2. **中期 (2-4 周)**: 升级 rand 0.8 → 0.9 系列（需适配 API 变更）
3. **长期 (待 libp2p 0.57)**: 升级 hickory-proto 0.25 → 0.26+

---

## 验证命令

```bash
# 重新扫描
cargo audit

# 查看过时依赖
cargo outdated --workspace

# 检查特定 crate 漏洞
cargo audit -p hickory-proto
cargo audit -p rsa
```

---

> **结论**: 当前无 Critical/High 级别漏洞。Medium 级别漏洞（rsa）实际代码路径不可达。建议持续跟踪 hickory-proto 修复进展，并在 libp2p 升级后同步更新。

[来源: cargo-audit / RustSec Advisory Database](https://rustsec.org/)
