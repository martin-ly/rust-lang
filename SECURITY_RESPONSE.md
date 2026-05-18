# 供应链安全响应流程

> **维护者**: rust-lang 知识体系项目组
> **生效日期**: 2026-05-18
> **策略文件**: [`deny.toml`](./deny.toml)
> **CI 检查**: [`.github/workflows/security-audit.yml`](./.github/workflows/security-audit.yml)

---

## 一、安全事件分级 (Severity Levels)

| 级别 | 标准 | 响应时间 | 行动 |
|:---|:---|:---:|:---|
| **P0 — Critical** | RUSTSEC `severity = critical`; 可导致 RCE/UAF/沙箱逃逸 | 24h | 立即隔离/降级依赖，发布修复，通知所有下游 |
| **P1 — High** | RUSTSEC `severity = high`; 可导致 DoS/信息泄露/权限提升 | 72h | 优先升级依赖或应用补丁，更新 deny.toml |
| **P2 — Medium/Low** | RUSTSEC `severity = medium/low`; 有限影响 | 1 周 | 纳入常规 `cargo update` 周期处理 |
| **P3 — Unmaintained** | crate 标记为 unmaintained/deprecated | 1 个月 | 评估替代方案，制定迁移计划 |
| **P4 — Informational** | yanked / 通知类通告 | 下次发布前 | 在 `cargo update` 时一并处理 |

---

## 二、响应工作流 (Response Workflow)

```
检测 → 分级 → 评估 → 修复 → 验证 → 文档 → 复盘
  ↑___________________________________________↓
```

### Step 1: 检测 (Detection)

**自动化检测**（每日/每次 CI）：

- `cargo audit` — 扫描 Cargo.lock 中的已知漏洞
- `cargo deny check advisories` — 基于策略文件的漏洞检查
- `cargo outdated` — 检测过期依赖

**人工检测**（每周）：

- 浏览 <https://rustsec.org/advisories/>
- 关注直接依赖 crate 的 GitHub Security Advisories

### Step 2: 分级 (Triage)

根据上表分级，创建跟踪 issue（如适用）：

```markdown
## RUSTSEC-XXXX-XXXX 跟踪
- **等级**: P0/P1/P2/P3
- **影响 crate**: xxx
- **引入路径**: workspace 直接声明 / 通过 xxx 传递引入
- **修复方案**: 升级至 x.y.z / 替换为 xxx / 暂时忽略（带理由）
- **负责人**: @xxx
- **截止日期**: YYYY-MM-DD
```

### Step 3: 评估 (Assessment)

判断修复可行性：

1. **可直接升级**？→ 修改 `Cargo.toml` workspace 版本 → `cargo check` → `cargo test`
2. **需代码适配**？→ 评估工作量，纳入 Sprint 计划
3. **传递依赖无法控制**？→ 更新 `deny.toml` 的 `ignore` 列表（带 `ignore-until` 到期日）
4. **无修复版本**？→ 评估替代 crate 或功能降级

### Step 4: 修复 (Fix)

**直接依赖修复**：

```bash
# 1. 修改 Cargo.toml 中的 workspace 版本
# 2. 运行 cargo update -p <crate>
cargo update -p hickory-proto
# 3. 编译验证
cargo check --workspace
# 4. 测试验证
cargo test --workspace
```

**传递依赖修复**（通过 `[patch]` 或升级直接依赖）：

```toml
# 在 Cargo.toml 中临时 patch
tokio-console = { git = "https://github.com/tokio-rs/console", branch = "main" }
```

### Step 5: 验证 (Verification)

```bash
# 重新运行安全审计
cargo audit
cargo deny check advisories
# 确保无新增漏洞
```

### Step 6: 文档 (Documentation)

- 更新 `CHANGELOG.md` 的 Security 章节
- 更新 `deny.toml` 的 ignore 列表（如适用）
- 关闭跟踪 issue

### Step 7: 复盘 (Retrospective)

每月回顾：

- 本月新增漏洞数量及分级分布
- 平均修复时间 (MTTR)
- 重复出现的漏洞模式（如某 crate 频繁引入安全问题）
- 改进措施

---

## 三、当前已知风险登记册 (Risk Register)

> 最后更新: 2026-05-18

| RUSTSEC | 等级 | 影响 Crate | 引入路径 | 状态 | 计划修复日期 |
|:---|:---:|:---|:---|:---:|:---:|
| RUSTSEC-2026-0118 | P1 | hickory-proto 0.25.2 | workspace 直接声明 | 跟踪中 | 2026-06-15 |
| RUSTSEC-2026-0119 | P1 | hickory-proto 0.24.4/0.25.2 | workspace 直接 + libp2p 传递 | 跟踪中 | 2026-06-15 |
| RUSTSEC-2025-0009 | P1 | ring 0.16.20 | libp2p-tls 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2026-0098 | P1 | rustls-webpki 0.101.7 | libp2p-tls 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2026-0099 | P1 | rustls-webpki 0.101.7 | libp2p-tls 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2026-0104 | P1 | rustls-webpki 0.101.7 | libp2p-tls 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2022-0041 | P2 | crossbeam-utils 0.7.2 | bastion-executor 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2026-0002 | P2 | lru 0.12.5 | libp2p-swarm / tokio-console 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2025-0141 | P3 | bincode 2.0.1 | workspace 直接声明 (bench-only) | 计划中 | 2026-05-25 |
| RUSTSEC-2025-0134 | P3 | rustls-pemfile 2.2.0 | workspace 直接声明 | 计划中 | 2026-05-25 |
| RUSTSEC-2026-0110 | P3 | bare-metal 0.2.5 | cortex-m 传递 (embedded) | 跟踪中 | 2026-06-30 |
| RUSTSEC-2025-0057 | P3 | fxhash 0.2.1 | bastion 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2024-0384 | P3 | instant 0.1.13 | bastion/glommio 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2024-0436 | P3 | paste 1.0.15 | tokio-console / netlink 传递 | 跟踪中 | 2026-06-30 |
| RUSTSEC-2025-0010 | P3 | ring 0.16.20 | libp2p-tls 传递 | 跟踪中 | 2026-06-30 |

---

## 四、关键依赖维护策略

### libp2p 生态 (c10_networks)

- **当前版本**: 0.54.1（可选依赖，通过 `libp2p` feature 启用）
- **风险**: 传递引入 ring 0.16.20、rustls-webpki 0.101.7、hickory-proto 0.24.4
- **计划**: 升级至 0.56+（需同步升级 hickory-resolver 到 0.26+，API 变更大）
- **责任人**: c10_networks 维护者

### bastion 生态 (c06_async)

- **当前版本**: 0.4.5（可选依赖，通过 `bastion` feature 启用）
- **风险**: 传递引入 fxhash、instant、crossbeam-utils 0.7.2（unsound）
- **计划**: 评估替换为 actix/axum 原生容错方案，或推动 bastion 上游修复
- **责任人**: c06_async 维护者

### hickory-dns (c10_networks)

- **当前版本**: 0.25.2（workspace 直接声明）
- **风险**: RUSTSEC-2026-0118（无修复版本）、RUSTSEC-2026-0119
- **计划**: 升级至 0.26.1+，适配 c10_networks DNS 模块 API 变化
- **责任人**: c10_networks 维护者

---

## 五、工具链速查

```bash
# 运行完整安全审计
cargo audit

# 运行 deny 策略检查
cargo deny check

# 检查过期依赖
cargo outdated

# 更新指定依赖
cargo update -p <crate-name>

# 查看依赖树
cargo tree -p <crate-name>

# 查看重复依赖
cargo tree -d
```

---

## 六、参考链接

- [RustSec Advisory Database](https://rustsec.org/advisories/)
- [cargo-deny 文档](https://embarkstudios.github.io/cargo-deny/)
- [cargo-audit 文档](https://github.com/RustSec/rustsec/tree/main/cargo-audit)
- [Rust Project Security Policy](https://www.rust-lang.org/policies/security)
