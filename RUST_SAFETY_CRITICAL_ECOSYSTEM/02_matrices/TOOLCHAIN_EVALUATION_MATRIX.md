# 工具链评估矩阵

## 概述

本文档提供Rust安全关键开发工具链的全面评估，帮助团队选择合适的工具组合。

---

## 1. 编译器评估

### 1.1 功能对比

| 特性 | rustc (稳定) | Ferrocene | AdaCore GNAT Pro | 嵌入式专用 |
|------|-------------|-----------|------------------|-----------|
| **语言版本** | 最新稳定 | 固定版本 | 固定版本 | 定制 |
| **目标平台** | 通用 | 认证平台 | 认证平台 | 特定 |
| **TÜV认证** | ❌ | ✅ | ✅ | 部分 |
| **ISO 26262** | ❌ | ✅ ASIL D | ✅ ASIL D | 部分 |
| **DO-178C** | ❌ | 计划中 | 计划中 | ❌ |
| **定价** | 免费 | $$$ | $$$ | $$ |
| **支持** | 社区 | 商业 | 商业 | 混合 |

### 1.2 性能对比

```
编译速度 (相对值, 越小越好):

rustc + LTO: 100 (基准)
Ferrocene:   105 (含验证)
GNAT Pro:    120 (Ada兼容层)
GCC-Rust:    150 (实验性)

生成代码质量:

rustc LLVM:  ⭐⭐⭐⭐⭐
Ferrocene:   ⭐⭐⭐⭐⭐ (相同后端)
GNAT Pro:    ⭐⭐⭐⭐ (LLVM)
GCC-Rust:    ⭐⭐⭐ (GCC后端)
```

---

## 2. 静态分析工具评估

### 2.1 功能矩阵

| 工具 | 类型检查 | 内存安全 | 并发安全 | 编码标准 | 复杂度 | CI集成 |
|------|---------|---------|---------|---------|--------|--------|
| **rustc** | ✅ 核心 | ✅ 借用 | ✅ Send/Sync | ❌ | ⚠️ | ✅ |
| **Clippy** | ✅ 扩展 | ⚠️ 部分 | ⚠️ 部分 | ✅ | ✅ | ✅ |
| **Miri** | ❌ | ✅ UB检测 | ✅ 数据竞争 | ❌ | ❌ | ⚠️ |
| **cargo-deny** | ❌ | ❌ | ❌ | ❌ | ❌ | ✅ |
| **Semgrep** | ⚠️ | ⚠️ | ⚠️ | ✅ | ⚠️ | ✅ |

### 2.2 推荐配置

```rust
// clippy.toml 推荐配置

# 安全关键级别
deny = [
    "unsafe_code",              # ASIL D要求
]

warn = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::restriction",
    "clippy::nursery",
]

allow = [
    "clippy::module_name_repetitions",
    "clippy::similar_names",
]

# 复杂度限制
cyclomatic-complexity-threshold = 10
cognitive-complexity-threshold = 15
too-many-lines-threshold = 50
```

---

## 3. 形式化验证工具评估

### 3.1 能力对比

| 工具 | 自动化 | 覆盖率 | 学习曲线 | 性能 | 成熟度 | 应用场景 |
|------|--------|--------|----------|------|--------|----------|
| **Miri** | ⭐⭐⭐⭐⭐ | UB检测 | 低 | 慢 | 高 | 开发时 |
| **Kani** | ⭐⭐⭐⭐⭐ | 属性验证 | 中 | 中 | 中 | CI集成 |
| **Verus** | ⭐⭐⭐ | 功能正确 | 高 | 快* | 中 | 核心算法 |
| **Creusot** | ⭐⭐⭐ | 复杂不变量 | 高 | 快* | 低 | 研究 |
| **Prusti** | ⭐⭐⭐⭐ | 契约检查 | 中 | 中 | 中 | IDE集成 |

*验证后无运行时开销

### 3.2 选择决策树

```
需要验证什么？
    │
    ├── 无未定义行为 ──► Miri
    │   ├── 内存操作
    │   ├── 原始指针
    │   └── 并发访问
    │
    ├── 安全属性 ──► Kani
    │   ├── 数组边界
    │   ├── 整数溢出
    │   └── 自定义属性
    │
    ├── 功能正确性 ──► Verus/Creusot
    │   ├── 复杂算法
    │   ├── 数据结构
    │   └── 系统不变量
    │
    └── 运行时契约 ──► Prusti
        ├── 前置条件
        ├── 后置条件
        └── 循环不变量
```

---

## 4. 测试框架评估

### 4.1 功能对比

| 框架 | 单元测试 | 集成测试 | 属性测试 | Mock | 覆盖率 | no_std |
|------|---------|---------|---------|------|--------|--------|
| **built-in** | ✅ | ✅ | ❌ | ❌ | ❌ | ✅ |
| **proptest** | ✅ | ✅ | ✅ | ❌ | ❌ | ⚠️ |
| **mockall** | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ |
| **double** | ✅ | ❌ | ❌ | ✅ | ❌ | ✅ |
| **embedded-test** | ✅ | ⚠️ | ❌ | ❌ | ❌ | ✅ |

### 4.2 覆盖率工具

```
覆盖率工具对比:

cargo-tarpaulin:
├── 类型: 行/分支/MC/DC
├── 速度: 中等
├── 精度: 高
├── CI: 优秀
└── 推荐: ⭐⭐⭐⭐⭐

cargo-llvm-cov:
├── 类型: 全功能
├── 速度: 快
├── 精度: 非常高
├── CI: 优秀
└── 推荐: ⭐⭐⭐⭐⭐

grcov:
├── 类型: 多格式
├── 速度: 中等
├── 精度: 高
├── CI: 良好
└── 推荐: ⭐⭐⭐⭐
```

---

## 5. IDE和编辑器评估

### 5.1 功能矩阵

| IDE | 代码补全 | 重构 | 调试 | 验证集成 | 价格 |
|-----|---------|------|------|---------|------|
| **VS Code** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 免费 |
| **CLion** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | $$$
| **neovim** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | 免费 |
| **Helix** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ | 免费 |

### 5.2 rust-analyzer配置

```json
{
    "rust-analyzer.cargo.features": "all",
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.checkOnSave.allTargets": true,
    "rust-analyzer.cargo.unsetTest": ["core"],
    "rust-analyzer.lens.enable": true,
    "rust-analyzer.hover.documentation.enable": true,
    "rust-analyzer.inlayHints.enable": true,
    "rust-analyzer.procMacro.enable": true,
    "[rust]": {
        "editor.formatOnSave": true,
        "editor.defaultFormatter": "rust-lang.rust-analyzer"
    }
}
```

---

## 6. CI/CD工具评估

### 6.1 平台对比

| 平台 | Rust支持 | 并行构建 | 缓存 | 自托管 | 成本 |
|------|---------|---------|------|--------|------|
| **GitHub Actions** | ⭐⭐⭐⭐⭐ | ✅ | ✅ | ✅ | 免费/$$ |
| **GitLab CI** | ⭐⭐⭐⭐⭐ | ✅ | ✅ | ✅ | 免费/$$ |
| **Azure DevOps** | ⭐⭐⭐⭐ | ✅ | ✅ | ✅ | $$ |
| **Jenkins** | ⭐⭐⭐ | ⚠️ | ⚠️ | ✅ | 免费(自管) |
| **Drone** | ⭐⭐⭐⭐ | ✅ | ✅ | ✅ | 免费 |

### 6.2 GitHub Actions完整配置

```yaml
name: Safety Critical CI

on: [push, pull_request]

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy, miri, llvm-tools-preview

      - name: Format
        run: cargo fmt --all -- --check

      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Test
        run: cargo test --all-features

      - name: Miri
        run: cargo miri test
        env:
          MIRIFLAGS: -Zmiri-strict-provenance

      - name: Coverage
        uses: taiki-e/install-action@cargo-llvm-cov
      - run: cargo llvm-cov --all-features --lcov --output-path lcov.info

      - name: Kani
        run: |
          cargo install --locked kani-verifier
          kani-setup
          cargo kani --workspace
```

---

## 7. 包和依赖管理

### 7.1 审计工具

| 工具 | 漏洞扫描 | 许可证检查 | 过期检测 | 大小分析 | SBOM |
|------|---------|-----------|---------|---------|------|
| **cargo-audit** | ✅ | ❌ | ⚠️ | ❌ | ❌ |
| **cargo-deny** | ✅ | ✅ | ✅ | ✅ | ✅ |
| **cargo-outdated** | ❌ | ❌ | ✅ | ❌ | ❌ |
| **cargo-bloat** | ❌ | ❌ | ❌ | ✅ | ❌ |
| **cargo-sbom** | ❌ | ❌ | ❌ | ❌ | ✅ |

### 7.2 推荐deny.toml

```toml
[advisories]
vulnerability = "deny"
yanked = "deny"

[licenses]
allow = ["MIT", "Apache-2.0", "BSD-3-Clause"]
deny = ["GPL-2.0", "GPL-3.0"]

[bans]
multiple-versions = "warn"
wildcards = "deny"
```

---

## 8. 嵌入式特定工具

### 8.1 调试和烧录

| 工具 | JTAG/SWD | RTT | 追踪 | GDB | 价格 |
|------|---------|-----|------|-----|------|
| **probe-rs** | ✅ | ✅ | ⚠️ | ✅ | 免费 |
| **OpenOCD** | ✅ | ❌ | ✅ | ✅ | 免费 |
| **J-Link** | ✅ | ✅ | ✅ | ✅ | $-$$$ |
| **ST-Link** | ✅ | ❌ | ❌ | ⚠️ | $ |

### 8.2 日志和跟踪

```rust
// defmt 推荐配置
use defmt::*;

#[entry]
fn main() -> ! {
    defmt::info!("System starting...");

    loop {
        let sensor_value = read_sensor();
        defmt::debug!("Sensor: {}", sensor_value);

        if sensor_value > THRESHOLD {
            defmt::warn!("Threshold exceeded: {}", sensor_value);
        }
    }
}
```

---

## 9. 工具链推荐组合

### 9.1 ASIL D级项目

```
编译器: Ferrocene
├── TÜV认证
├── 固定版本
└── 商业支持

静态分析:
├── rustc (借用检查)
├── Clippy (编码标准)
└── Miri (UB检测)

形式化验证:
├── Kani (属性验证)
└── Verus (关键算法)

测试:
├── cargo test (单元测试)
├── cargo-llvm-cov (覆盖率)
└── proptest (属性测试)

CI/CD:
├── GitHub Actions
├── 可重现构建
└── SBOM生成

IDE:
├── VS Code + rust-analyzer
└── 或 CLion (商业)
```

### 9.2 SIL 2级项目

```
编译器: rustc (固定版本)
├── 成本优化
├── 充分验证
└── 社区支持

静态分析:
├── rustc
├── Clippy
└── 可选Miri

测试:
├── cargo test
├── cargo-tarpaulin
└── 手动代码审查

成本: 降低60%
风险: 可控
适用: 非最高安全等级
```

---

## 10. 工具选择检查表

### 编译器选择

- [ ] 目标安全等级确定
- [ ] 认证要求评估
- [ ] 预算考虑
- [ ] 时间线考虑
- [ ] 团队熟悉度

### 验证工具选择

- [ ] 验证目标明确
- [ ] 自动化程度需求
- [ ] 团队技能评估
- [ ] CI集成需求
- [ ] 维护成本

### CI/CD选择

- [ ] 现有基础设施
- [ ] 并行需求
- [ ] 自托管需求
- [ ] 安全要求
- [ ] 成本预算

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**评估日期**: 2026年Q1

---

*工具链选择是项目成功的基础，建议充分评估后再做决定。*
