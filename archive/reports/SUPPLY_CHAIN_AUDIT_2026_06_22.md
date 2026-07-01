# 供应链安全审计报告

> **生成时间**: 2026-06-22T15:31:13.473411
> **工具**: scripts/supply_chain_audit.py（cargo-vet 替代方案）
> **Rust 版本**: 1.96.0 (Edition 2024)

## 依赖概览

| 类别 | 数量 |
|:---|:---:|
| 唯一包名 | 899 |
| 总包实例（含多版本） | 1016 |
| crates.io 注册表 | 999 |
| 本地路径依赖 | 17 |
| Git 依赖 | 0 |

## 版本落后检查（采样）

| 包名 | 当前版本 | 最新版本 | 建议 |
|:---|:---|:---|:---|
| accesskit_atspi_common | 0.18.1 | 0.19.0 | 考虑升级 |
| accesskit_consumer | 0.35.0 | 0.37.0 | 考虑升级 |
| accesskit_consumer | 0.36.0 | 0.37.0 | 考虑升级 |
| accesskit_unix | 0.21.1 | 0.22.0 | 考虑升级 |
| accesskit_windows | 0.32.1 | 0.33.1 | 考虑升级 |
| accesskit_winit | 0.32.2 | 0.33.1 | 考虑升级 |
| addr2line | 0.25.1 | 0.26.1 | 考虑升级 |
| aead | 0.5.2 | 0.6.1 | 考虑升级 |
| aes | 0.8.4 | 0.9.1 | 考虑升级 |
| aes-gcm | 0.10.3 | 0.11.0-rc.4 | 考虑升级 |
| ahash | 0.7.8 | 0.8.12 | 考虑升级 |
| allocator-api2 | 0.2.21 | 0.4.0 | 考虑升级 |
| anes | 0.1.6 | 0.2.1 | 考虑升级 |

## 已知安全公告

✅ 未发现已知安全漏洞。

## 后续建议

1. **定期运行 `cargo audit`**：安装 `cargo-audit` 后定期扫描依赖安全公告。
2. **关注版本更新**：对核心依赖（tokio、serde 等）设置 Dependabot 或 Renovate。
3. **cargo-vet 待修复**：Windows 上 cargo-vet 编译失败（LockFileEx API），已报告上游。
4. **本地 crate 审计**：本工作区 17 个本地 crate 无外部安全风险。
