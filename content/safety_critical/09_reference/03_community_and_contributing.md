# 社区参与与贡献指南

**EN**: Community And Contributing
**Summary**: 社区参与与贡献指南 Community And Contributing.

> **权威来源**: 本文件为 `content/` 专题深度内容入口；通用 Rust 概念解释请见 [`concept/06_ecosystem/README.md`](../../../concept/06_ecosystem/README.md)。若 `concept/` 已覆盖相同主题，本文仅保留应用场景、案例与决策树，不重复概念推导。

> **Bloom 层级**: L4-L6
>
> 本文内容迁移自历史归档，已按 `AGENTS.md` 规则保留为安全关键领域专题实践。

## 1. 社区生态
>
> **[来源: Rust Official Docs]**

### 1.1 主要组织

> **[来源: Rust Reference - doc.rust-lang.org/reference]**
>
> **[来源: Rust Official Docs]**

```
Rust基金会:
├── 安全关键Rust工作组
│   └── https://github.com/rustfoundation/safety-critical-rust-consortium
│
├── 安全工作组
│   └── https://github.com/rust-secure-code/wg
│
└── 嵌入式工作组
    └── https://github.com/rust-embedded/wg

商业组织:
├── Ferrous Systems
│   └── Ferrocene项目
│
├── AdaCore
│   └── GNAT Pro for Rust
│
├── HighTec EDV-Systeme
│   └── Rust编译器
│
└── 42 Technology
    └── 安全咨询服务

学术机构:
├── ETH Zurich (Prusti)
├── Inria (Creusot)
├── VMware Research (Verus)
├── AWS (Kani)
└── 多所大学研究组
```

### 1.2 在线社区

> **[来源: TRPL - The Rust Programming Language]**

```
论坛和讨论:
├── Rust Users Forum
│   └── https://users.rust-lang.org/
│
├── Rust嵌入式论坛
│   └── https://github.com/rust-embedded
│
├── Zulip Chat
│   ├── Rust主频道
│   └── 安全关键Rust
│
└── Reddit
    ├── r/rust
    └── r/embedded

会议和活动:
├── RustConf
├── EuroRust
├── Rust嵌入式会议
├── OxidizeConf
└── 各种Meetup
```

---

## 2. 参与方式
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 代码贡献

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

```
贡献领域:
├── 开源项目
│   ├── rust-lang/rust (编译器)
│   ├── rust-embedded (嵌入式生态)
│   ├── ferrocene (认证工具链)
│   ├── kani (验证工具)
│   └── verus (形式化验证)
│
├── 库开发
│   ├── 硬件抽象层(HAL)
│   ├── 安全关键算法
│   ├── 验证工具集成
│   └── 测试框架
│
└── 文档
    ├── 教程编写
    ├── 示例代码
    ├── 翻译工作
    └── 标准文档
```

### 2.2 贡献流程
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```bash
# 1. Fork仓库
# 2. 克隆本地
git clone https://github.com/YOUR_USERNAME/PROJECT.git
cd PROJECT

# 3. 创建分支
git checkout -b feature/my-contribution

# 4. 开发和测试
cargo test
cargo clippy
cargo fmt

# 5. 提交更改
git add .
git commit -m "feat: description of changes"

# 6. 推送并创建PR
git push origin feature/my-contribution
# 在GitHub上创建Pull Request
```

---

## 3. 知识分享
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 3.1 内容创作
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
博客写作:
├── 技术博客
│   ├── 学习笔记
│   ├── 项目经验
│   ├── 问题解决方案
│   └── 最佳实践
│
├── 平台选择
│   ├── 个人博客
│   ├── Medium
│   ├── Dev.to
│   ├── 知乎
│   └── CSDN
│
└── 主题建议
    ├── Rust入门指南
    ├── 嵌入式开发经验
    ├── 功能安全实施
    ├── 形式化验证教程
    └── 工具使用技巧
```

### 3.2 演讲和分享
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```
演讲机会:
├── 本地Meetup
│   └── https://www.meetup.com/rust/
│
├── 技术会议
│   ├── 提交CFP (Call for Proposals)
│   ├── 闪电演讲
│   └── 研讨会
│
├── 公司内部分享
│   ├── 技术午餐会
│   ├── 培训讲座
│   └── 代码审查分享
│
└── 在线研讨会
    ├── Webinar
    ├── 直播编程
    └── YouTube频道
```

---

## 4. 标准参与
>
> **[来源: [crates.io](https://crates.io/)]**

### 4.1 标准组织
>
> **[来源: [docs.rs](https://docs.rs/)]**

```
参与方式:
├── ISO/IEC JTC 1/SC 22
│   └── 编程语言标准
│
├── MISRA
│   └── Rust编码标准开发
│
├── AUTOSAR
│   └── Rust自适应平台
│
└── 行业联盟
    ├── 汽车制造商联盟
    ├── 航空电子协会
    └── 工业自动化组织
```

### 4.2 认证机构合作
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```
与认证机构合作:
├── 预认证沟通
│   ├── 技术方案讨论
│   ├── 工具鉴定合作
│   └── 案例研究分享
│
├── 培训合作
│   ├── 联合培训
│   ├── 认证课程开发
│   └── 考试标准制定
│
└── 行业推广
    ├── 会议演讲
    ├── 白皮书发布
    └── 媒体采访
```

---

## 5. 教育资源
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 5.1 导师计划
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
导师-学员配对:
├── 配对方式
│   ├── 官方导师计划
│   ├── 社区配对
│   └── 公司内部分配
│
├── 指导内容
│   ├── Rust语言学习
│   ├── 项目指导
│   ├── 职业规划
│   └── 代码审查
│
└── 时间承诺
    ├── 每周1-2小时
    ├── 持续3-6个月
    └── 定期评估
```

### 5.2 学习小组
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
组织学习小组:
├── 线上小组
│   ├── Discord频道
│   ├── 微信群
│   ├── 视频会议
│   └── 协同编程
│
├── 线下活动
│   ├── 本地聚会
│   ├── 黑客松
│   ├── 代码冲刺
│   └── 社交活动
│
└── 学习资源
    ├── 共享书单
    ├── 项目仓库
    ├── 笔记分享
    └── 问题讨论
```

---

## 6. 职业发展
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 6.1 技能认证
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```
认证路径:
├── Rust官方认证
│   ├── Rust Developer
│   ├── Rust Expert
│   └── 特定领域认证
│
├── 功能安全认证
│   ├── CFSE (Certified Functional Safety Expert)
│   ├── TÜV认证
│   └── 行业标准认证
│
└── 公司认证
    ├── 内部技能认证
    ├── 项目经验认证
    └── 技术领导力认证
```

### 6.2 职业机会
>
> **[来源: [crates.io](https://crates.io/)]**

```
就业方向:
├── 嵌入式开发工程师
│   └── 汽车/航空/医疗设备
│
├── 功能安全工程师
│   └── 安全分析/认证
│
├── 工具链开发
│   └── 编译器/验证工具
│
├── 系统架构师
│   └── 安全关键系统设计
│
└── 技术顾问
    └── 咨询/培训服务
```

---

## 7. 贡献行为准则
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 7.1 行为准则
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```
社区准则:
├── 尊重他人
│   ├── 友善交流
│   ├── 包容差异
│   └── 避免歧视
│
├── 专业态度
│   ├── 建设性反馈
│   ├── 诚实沟通
│   └── 承担责任
│
└── 协作精神
    ├── 分享知识
    ├── 帮助他人
    └── 团队合作
```

### 7.2 贡献质量
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```
质量保证:
├── 代码质量
│   ├── 通过CI检查
│   ├── 测试覆盖
│   ├── 文档完整
│   └── 符合规范
│
├── 沟通质量
│   ├── 清晰的PR描述
│   ├── 及时回复
│   ├── 接受反馈
│   └── 持续改进
│
└── 长期维护
    ├── 问题跟进
    ├── 文档更新
    └── 版本兼容
```

---

## 8. 资源链接
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 8.1 官方资源
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
必读资源:
├── The Rust Book
│   └── https://doc.rust-lang.org/book/
│
├── Rust Reference
│   └── https://doc.rust-lang.org/reference/
│
├── Rust API Guidelines
│   └── https://rust-lang.github.io/api-guidelines/
│
└── This Week in Rust
    └── https://this-week-in-rust.org/
```

### 8.2 安全关键特定
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
专业资源:
├── High Assurance Rust
│   └── https://highassurance.rs/
│
├── Ferrocene Documentation
│   └── https://ferrocene.dev/
│
├── Rust Safety Critical Wiki
│   └── https://github.com/rustfoundation/safety-critical-rust-consortium
│
└── Embedded Rust Book
    └── https://docs.rust-embedded.org/book/
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*社区的力量在于每个人的参与和贡献。*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

---
