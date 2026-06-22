# Rust安全关键系统 - 检查清单与模板

> **Bloom 层级**: 理解
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

## 代码审查检查清单
>
> **[来源: Rust Official Docs]**

### Unsafe代码审查清单
>
> **[来源: Rust Official Docs]**

```markdown
## Unsafe代码审查
> **[来源: Rust Official Docs]**

### 基本信息
> **[来源: Rust Official Docs]**
- [ ] 审查日期: ___________
- [ ] 审查人: ___________
- [ ] 作者: ___________
- [ ] 模块/函数: ___________

### 安全清单
> **[来源: Rust Official Docs]**

#### 文档化
- [ ] 有 `# Safety` 文档注释
- [ ] 文档说明了前置条件
- [ ] 文档说明了不变量
- [ ] 文档说明了调用者责任

#### 范围控制
- [ ] unsafe块尽可能小
- [ ] 每个unsafe块有明确目的
- [ ] 不超过10行（特殊情况需说明）

#### 输入验证
- [ ] 所有指针参数检查非空
- [ ] 长度参数验证合理
- [ ] 索引参数检查边界
- [ ] 枚举值检查有效

#### 内存安全
- [ ] 无use-after-free风险
- [ ] 无双重释放风险
- [ ] 无缓冲区溢出风险
- [ ] 指针正确对齐

#### 测试
- [ ] Miri测试通过
- [ ] 有单元测试
- [ ] 边界条件测试
- [ ] 错误路径测试

#### 替代方案
- [ ] 考虑了safe Rust替代方案
- [ ] 文档说明了为何必须使用unsafe

### 审查结论
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 通过
- [ ] 有条件通过（需修改: ________）
- [ ] 不通过（原因: ________）

### 备注
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
_________________________________
```

---

### 模块安全等级检查清单
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```markdown
## 模块安全等级评估
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 模块信息
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] 模块名称: ___________
- [ ] 目标ASIL/SIL等级: ___________

### QM (低安全等级)
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 使用Safe Rust
- [ ] 通过clippy检查
- [ ] 有基本测试

### ASIL A/B
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- [ ] 使用Safe Rust
- [ ] 无unsafe代码
- [ ] cargo audit通过
- [ ] 测试覆盖率>80%
- [ ] Miri测试通过

### ASIL C
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- [ ] 大多数代码Safe Rust
- [ ] unsafe代码<5%
- [ ] unsafe代码已审查
- [ ] 测试覆盖率>90%
- [ ] Kani验证关键函数
- [ ] 形式化文档

### ASIL D
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
- [ ] 仅必要时使用unsafe
- [ ] unsafe代码<1%
- [ ] 经过多轮审查
- [ ] 测试覆盖率>95%
- [ ] MC/DC覆盖
- [ ] 形式化验证
- [ ] 认证工具链

### 评估结果
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] 符合目标等级
- [ ] 需要改进（见备注）

备注: _________________________________
```

---

## 认证准备检查清单
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### ISO 26262准备清单
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```markdown
## ISO 26262认证准备
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 项目信息
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
- [ ] 项目名称: ___________
- [ ] 目标ASIL等级: ___________
- [ ] 预计认证日期: ___________

### 安全管理 (Part 2)
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] 安全计划制定
- [ ] 安全经理任命
- [ ] 安全文化建立

### 概念阶段 (Part 3)
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 项目定义
- [ ] 安全生命周期定义
- [ ] 危害分析和风险评估 (HARA)
- [ ] 功能安全概念

### 产品开发: 系统 (Part 4)
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- [ ] 技术安全需求规格
- [ ] 系统设计
- [ ] 项目集成和测试
- [ ] 安全验证

### 产品开发: 软件 (Part 6)
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- [ ] 软件安全需求规格
- [ ] 软件架构设计
- [ ] 软件单元设计和实现
- [ ] 软件单元测试
- [ ] 软件集成和测试
- [ ] 软件安全验证

### 工具鉴定 (Part 8)
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
- [ ] 工具分类 (TCL)
- [ ] 工具鉴定方法选择
- [ ] 工具鉴定报告

### 生产 (Part 7)
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] 生产计划
- [ ] 生产过程验证

### 证据包
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 所有文档完成
- [ ] 追溯性矩阵
- [ ] 测试报告
- [ ] 审查记录
- [ ] 工具鉴定报告

### 准备就绪
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- [ ] 内部审计完成
- [ ] 管理层审查
- [ ] 认证机构预约

状态: [ ] 准备就绪  [ ] 需要改进
```

---

## 发布前检查清单
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```markdown
## 发布前最终检查
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 代码质量
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] 所有代码审查完成
- [ ] clippy无警告
- [ ] cargo fmt格式化
- [ ] 无TODO/FIXME遗留

### 测试
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 所有单元测试通过
- [ ] 集成测试通过
- [ ] 覆盖率达标 (>90%)
- [ ] Miri测试通过 (unsafe代码)
- [ ] Kani验证通过 (关键函数)

### 安全
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- [ ] cargo audit无高危漏洞
- [ ] 依赖项已审查
- [ ] 安全文档更新

### 文档
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- [ ] API文档完整
- [ ] README更新
- [ ] CHANGELOG更新
- [ ] 版本号更新

### 认证 (如适用)
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
- [ ] 认证证据包完整
- [ ] 追溯性验证
- [ ] 安全分析更新

### 构建
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- [ ] Release构建成功
- [ ] 目标平台测试
- [ ] 安装包测试

### 批准
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 技术经理签字: ______
- [ ] 项目经理签字: ______
- [ ] 质量经理签字: ______

发布版本: ___________
发布日期: ___________
```

---

## 文档模板
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 安全需求规格模板
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```markdown
# 软件安全需求规格 (SSRS)

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [Rustonomicon](https://doc.rust-lang.org/nomicon/), [Ferrocene](https://ferrous-systems.com/ferrocene/), [Rust Safety Critical WG](https://github.com/rust-safety-critical/wg)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 安全关键生态系统来源标注 [来源: Authority Source Sprint Batch 8]

## 文档信息
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
- 文档编号: SSRS-XXX
- 版本: 1.0
- 日期: YYYY-MM-DD
- 作者: ________

## 1. 引言
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 1.1 目的
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
本文档描述XXX模块的软件安全需求。

### 1.2 范围
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
适用于ASIL X等级的软件开发。

### 1.3 参考文档
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- 系统安全需求规格: SSSS-XXX
- 技术安全概念: TSC-XXX

## 2. 安全需求
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### SR-001: [需求标题]
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
**需求描述**: ...
**ASIL等级**: X
**追溯**: [系统需求编号]
**验证方法**: 测试/分析/审查
**验收标准**: ...

### SR-002: ...
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
...

## 3. 安全机制
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 3.1 硬件诊断接口
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
...

### 3.2 软件自检
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
...

## 4. 安全分析
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 4.1 FMEA
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
| 功能 | 故障模式 | 影响 | ASIL | 安全措施 |
|------|----------|------|------|----------|
| ... | ... | ... | ... | ... |

### 4.2 FTA
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
[故障树图]

## 5. 追溯性矩阵
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 系统需求 | 软件需求 | 设计 | 代码 | 测试 |
|----------|----------|------|------|------|
| SRS-001 | SR-001 | D-001 | M-001 | T-001 |
| ... | ... | ... | ... | ... |

## 6. 附录
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 6.1 术语表
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
...

### 6.2 变更历史
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
| 版本 | 日期 | 变更描述 | 作者 |
|------|------|----------|------|
| 1.0 | ... | 初始版本 | ... |
```

### 设计文档模板
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```markdown
# 软件架构设计文档 (SADD)

## 文档信息
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- 文档编号: SADD-XXX
- 版本: 1.0

## 1. 架构概述
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 1.1 高层架构
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
[架构图]

### 1.2 组件列表
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
| 组件 | 功能 | ASIL | 语言 |
|------|------|------|------|
| ... | ... | ... | ... |

## 2. 详细设计
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 组件A
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
#### 职责
...

#### 接口
```rust,ignore
pub fn function_name(arg: Type) -> Result<Output, Error>;
```

#### 安全机制

- 输入验证: ...
- 错误处理: ...
- 自检: ...

## 3. 数据流
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 3.1 正常操作
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

[数据流图]

### 3.2 错误处理
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

[错误处理流]

## 4. 资源使用
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 4.1 内存
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- 栈使用: X bytes
- 堆使用: Y bytes (如适用)

### 4.2 时间
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- 最坏情况执行时间: X μs

## 5. 安全分析
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 5.1 假设
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

...

### 5.2 依赖
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

...

### 5.3 风险
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

...

```

### 测试报告模板
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```markdown
# 软件测试报告

## 测试信息
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
- 模块: ________
- 版本: ________
- 测试日期: ________
- 测试人员: ________

## 测试范围
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 单元测试
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- 测试数量: X
- 通过: Y
- 失败: Z
- 覆盖率: X%

### 集成测试
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- 测试数量: X
- 通过: Y
- 失败: Z

### 系统测试
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
...

## 覆盖分析
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 语句覆盖
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- 目标: >90%
- 实际: X%
- 状态: [ ]通过 [ ]未通过

### 分支覆盖
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
...

### MC/DC (ASIL D)
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
...

## 缺陷统计
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 严重级别 | 数量 | 已修复 | 剩余 |
|----------|------|--------|------|
| 严重 | X | Y | Z |
| 高 | X | Y | Z |
| 中 | X | Y | Z |
| 低 | X | Y | Z |

## 结论
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [ ] 测试通过，可以发布
- [ ] 测试未通过，需要修复

## 批准
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- 测试经理: ________
- 日期: ________
```

---

## 工具配置模板
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Clippy配置 (.clippy.toml)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```toml
# 安全关键Rust项目Clippy配置

# MSRV (Minimum Supported Rust Version)
msrv = "1.70.0"

# 认知复杂度阈值
cognitive-complexity-threshold = 15

# 循环复杂度阈值
cyclomatic-complexity-threshold = 15

# 函数参数数量上限
too-many-arguments-threshold = 7

# 函数行数上限
function-threshold = 50

# 结构体字段上限
struct-field-threshold = 10

# 枚举变体上限
enum-variant-threshold = 10

# 避免破坏导出API
avoid-breaking-exported-api = false

# 允许的诊断级别
allow = [
    # 根据项目需要
]

# 警告的诊断级别
warn = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::cargo",
]

# 拒绝的诊断级别 (错误)
deny = [
    "clippy::correctness",
    "unsafe_code",  # 可选：完全禁止unsafe
]
```

### CI配置 (.github/workflows/ci.yml)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```yaml
name: Safety-Critical CI

on:
  push:
    branches: [main]
  pull_request:

env:
  CARGO_TERM_COLOR: always

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-action@stable
        with:
          components: rustfmt, clippy, llvm-tools-preview

      - name: Format check
        run: cargo fmt --check

      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Build
        run: cargo build --release

      - name: Test
        run: cargo test --all-features

      - name: Coverage
        uses: taiki-e/install-action@cargo-tarpaulin
        run: cargo tarpaulin --fail-under 90

      - name: Security audit
        uses: actions-rust-lang/audit@v1

      - name: Miri (if unsafe)
        run: |
          rustup component add miri
          cargo miri test
        if: ${{ hashFiles('**/unsafe**') != '' }}
```

### Cargo.toml模板
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```toml
[package]
name = "safety-critical-module"
version = "1.0.0"
edition = "2021"
rust-version = "1.70"  # MSRV
license = "MIT OR Apache-2.0"
authors = ["Your Name <you@example.com>"]
description = "Safety-critical Rust module"
repository = "https://github.com/yourorg/yourrepo"

[features]
default = ["std"]
std = []
unsafe = []  # 可选unsafe特性

[dependencies]
# 仅使用已审计的依赖
heapless = "0.8"  # 无堆集合
serde = { version = "1.0", default-features = false }

[dev-dependencies]
proptest = "1.0"  # 属性测试
kani-verifier = "0.40"  # 模型检查

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
strip = true

[profile.release-with-debug]
inherits = "release"
strip = false
debug = true
```

---

## 使用说明
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **选择合适的检查清单**根据当前阶段和任务
2. **打印或数字化**使用这些清单
3. **定期审查**并更新模板
4. **收集反馈**改进清单

---

**模板版本**: 1.0
**最后更新**: 2026-03-18
**维护者**: Rust安全关键系统工作组
---

**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [Rust 安全关键系统生态系统主索引](../README.md)

- [API设计指南](01_api_design_guidelines.md)
- [社区参与与贡献指南](03_community_and_contributing.md)

---

## 权威来源索引

> **[来源: [ISO 26262](https://www.iso.org/standard/68383.html)]**
>
> **[来源: [IEC 61508](https://www.iec.ch/functionalsafety)]**
>
> **[来源: [MISRA Rust Guidelines](https://misra.org.uk/)]**
>
> **[来源: [Ferrocene](https://ferrocene.dev/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

## 📚 模块 8: 国际化对齐

> 本节按项目模板要求补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [Rust Project Goals — Safety-Critical Rust](https://rust-lang.github.io/rust-project-goals/2026/) | 权威来源 | 安全关键目标 |
| [Ferrocene](https://ferrocene.dev/) | 权威来源 | Ferrocene 认证 Rust |

### 8.2 学术来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 权威来源 | 语义基础 |
| [RefinedRust — OOPSLA 2024](https://dl.acm.org/doi/10.1145/3689738) | 权威来源 | 形式化验证 |

### 8.3 社区权威

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [Rust Safety-Critical Consortium](https://rust-safety-critical.com/) | 权威来源 | 安全关键联盟 |
| [High Integrity Systems Blog](https://www.highintegritysystems.com/) | 权威来源 | 工业实践 |
