# 名校区块链课程对标大纲（2024 年更新版）

## 目标

- 建立与 MIT、Stanford、UC Berkeley、Princeton 等课程周次对齐的教学大纲
- 将每周主题映射到本仓 `11_blockchain.md` 与 `docs/*` 小节
- 为每周提供：关键知识点、实验任务（Rust/ink!/Substrate）、推荐阅读
- 结合 Rust 1.89 特性，提供现代化的实践方案

---

## MIT 15.S12 - 区块链与加密货币

### 第 1 周：引言与系统模型

- **映射章节**：1.1, 7.1
- **关键知识点**：
  - 区块链基础概念与历史发展
  - 分布式系统模型与挑战
  - 去中心化 vs 中心化系统
- **实验任务**：
  - 使用 Substrate 构建最小区块链节点
  - 实现基础的区块创建和验证
- **Rust 1.89 特性应用**：

  ```rust
  // 使用生命周期语法检查优化区块链节点
  struct BlockchainNode<'a> {
      peers: Vec<&'a Peer>,
      blockchain: &'a mut Blockchain,
  }
  ```

- **推荐阅读**：
  - Bitcoin Whitepaper (Satoshi Nakamoto)
  - Ethereum Whitepaper (Vitalik Buterin)
  - Substrate Documentation

### 第 2 周：密码学基础

- **映射章节**：3.1, 3.2
- **关键知识点**：
  - 哈希函数（SHA-256, Blake3）
  - 数字签名（Ed25519, secp256k1）
  - Merkle 树构建与验证
- **实验任务**：
  - Rust 实现 SHA-256 哈希函数
  - 实现 Ed25519 数字签名
  - 构建 Merkle 树数据结构
- **Rust 1.89 特性应用**：

  ```rust
  // 使用常量泛型推断优化哈希计算
  struct BlockHash<const N: usize = 32> {
      data: [u8; N],
  }
  ```

- **推荐阅读**：
  - Applied Cryptography (Bruce Schneier)
  - Cryptography Engineering (Ferguson, Schneier, Kohno)

### 第 3 周：一致性与 PoW

- **映射章节**：1.2, 6.1
- **关键知识点**：
  - 共识算法基础
  - 工作量证明机制
  - 分叉处理与最长链规则
- **实验任务**：
  - 实现简化版 PoW 算法
  - 模拟分叉场景处理
- **推荐阅读**：
  - Bitcoin Mining
  - Consensus Algorithms

### 第 4 周：激励与经济学

- **映射章节**：6.1 扩展
- **关键知识点**：
  - 博弈论在区块链中的应用
  - 激励机制设计
  - 经济安全模型
- **实验任务**：
  - 分析不同激励模型
  - 实现简单的经济模型
- **推荐阅读**：
  - Game Theory in Blockchain
  - Cryptocurrency Economics

### 第 5 周：脚本与智能合约

- **映射章节**：2.1, 2.2
- **关键知识点**：
  - 智能合约基础概念
  - 合约执行环境
  - 安全性与可验证性
- **实验任务**：
  - 使用 ink! 开发简单智能合约
  - 合约安全审计实践
- **Rust 1.89 特性应用**：

  ```rust
  // 使用 Result::flatten 简化错误处理
  #[ink::contract]
  mod my_contract {
      impl MyContract {
          pub fn transfer(&mut self, to: AccountId, amount: u128) -> Result<(), Error> {
              self.validate_transfer(amount)
                  .and_then(|_| self.execute_transfer(to, amount))
                  .flatten() // 新稳定的 API
          }
      }
  }
  ```

- **推荐阅读**：
  - Smart Contract Security
  - Formal Verification

### 第 6 周：隐私与匿名性

- **映射章节**：3.3, 7.2
- **关键知识点**：
  - 隐私保护技术
  - 匿名协议（CoinJoin, RingCT）
  - 零知识证明基础
- **实验任务**：
  - 实现简单的隐私保护机制
  - 零知识证明原型
- **推荐阅读**：
  - Privacy in Blockchain
  - Zero-Knowledge Proofs

### 第 7 周：PoS 与 BFT

- **映射章节**：1.2, 6.1
- **关键知识点**：
  - 权益证明机制
  - 拜占庭容错算法
  - 最终性 vs 概率最终性
- **实验任务**：
  - 实现 PoS 共识算法
  - BFT 协议模拟
- **推荐阅读**：
  - Proof of Stake
  - Byzantine Fault Tolerance

### 第 8 周：可扩展性与 L2

- **映射章节**：6.4, 7.2
- **关键知识点**：
  - 扩容挑战与解决方案
  - Layer 2 技术（状态通道、Rollup）
  - 分片技术
- **实验任务**：
  - 实现简单的状态通道
  - Rollup 原型开发
- **推荐阅读**：
  - Layer 2 Solutions
  - Scaling Blockchain

### 第 9 周：跨链与互操作

- **映射章节**：6.4
- **关键知识点**：
  - 跨链通信协议
  - 桥接技术
  - 互操作性标准
- **实验任务**：
  - 实现跨链消息传递
  - 桥接协议开发
- **推荐阅读**：
  - Cross-Chain Protocols
  - Blockchain Interoperability

### 第 10 周：治理与监管

- **映射章节**：2.3, 4.3
- **关键知识点**：
  - 链上治理机制
  - 监管框架
  - 合规要求
- **实验任务**：
  - 实现治理投票系统
  - 合规检查工具
- **推荐阅读**：
  - Blockchain Governance
  - Regulatory Framework

### 第 11 周：应用案例

- **映射章节**：4.*
- **关键知识点**：
  - DeFi 应用
  - NFT 与数字资产
  - 供应链管理
- **实验任务**：
  - 开发 DeFi 应用
  - NFT 合约实现
- **推荐阅读**：
  - DeFi Applications
  - NFT Standards

### 第 12 周：项目展示

- **映射章节**：综合
- **项目要求**：
  - 完整的区块链应用
  - 技术文档
  - 演示视频
- **评估标准**：
  - 技术实现质量
  - 创新性
  - 文档完整性

---

## Stanford CS251 - 区块链技术

### 第 1 周：基础组件

- **映射章节**：1, 3
- **关键知识点**：
  - 区块结构设计
  - 哈希函数应用
  - 数字签名机制
- **实验任务**：
  - 构建区块链数据结构
  - 实现基础验证逻辑
- **推荐阅读**：
  - Blockchain Basics
  - Cryptographic Primitives

### 第 2 周：共识族谱

- **映射章节**：1.2, 6.1
- **关键知识点**：
  - PoW, PoS, BFT 对比
  - 混合共识机制
  - 共识算法性能分析
- **实验任务**：
  - 比较不同共识算法性能
  - 实现混合共识原型
- **推荐阅读**：
  - Consensus in Blockchain Systems
  - Algorithm Analysis

### 第 3 周：合约与安全

- **映射章节**：2.2, 7.2
- **关键知识点**：
  - 智能合约安全漏洞
  - 形式化验证方法
  - 安全最佳实践
- **实验任务**：
  - 使用 ink! 开发安全合约
  - 合约漏洞检测工具
- **推荐阅读**：
  - Smart Contract Security
  - Formal Verification

### 第 4 周：隐私技术

- **映射章节**：3.3
- **关键知识点**：
  - 隐私保护协议
  - 匿名技术
  - 隐私计算
- **实验任务**：
  - 实现隐私保护机制
  - 匿名交易协议
- **推荐阅读**：
  - Privacy Technologies
  - Anonymous Protocols

### 第 5 周：扩容与性能

- **映射章节**：6.4, 7.2
- **关键知识点**：
  - 性能瓶颈分析
  - 扩容技术对比
  - 优化策略
- **实验任务**：
  - 性能测试与优化
  - 扩容方案实现
- **推荐阅读**：
  - Performance Optimization
  - Scaling Solutions

### 第 6 周：DeFi/NFT/MEV

- **映射章节**：4.* 扩展
- **关键知识点**：
  - 去中心化金融
  - 非同质化代币
  - 最大可提取价值
- **实验任务**：
  - DeFi 协议开发
  - NFT 市场实现
- **推荐阅读**：
  - DeFi Protocols
  - NFT Standards

### 第 7 周：生态与研究前沿

- **映射章节**：7.*
- **关键知识点**：
  - 最新技术发展
  - 研究方向
  - 未来趋势
- **实验任务**：
  - 前沿技术调研
  - 创新方案设计
- **推荐阅读**：
  - Research Papers
  - Technical Trends

### 第 8 周：期末项目

- **映射章节**：综合
- **项目要求**：
  - 创新性区块链应用
  - 完整技术实现
  - 学术论文
- **评估标准**：
  - 技术创新性
  - 实现质量
  - 学术价值

---

## UC Berkeley - 区块链课程系列

### 第 1 周：比特币/以太坊基础

- **映射章节**：1, 6
- **关键知识点**：
  - UTXO 模型 vs 账户模型
  - 交易处理机制
  - 状态转换函数
- **实验任务**：
  - 解析比特币交易
  - 以太坊状态转换
- **推荐阅读**：
  - Mastering Bitcoin
  - Mastering Ethereum

### 第 2 周：Substrate/Polkadot 实作

- **映射章节**：4.1, 4.3
- **关键知识点**：
  - 模块化区块链架构
  - 跨链通信协议
  - 平行链技术
- **实验任务**：
  - 开发 Substrate pallet
  - 跨链消息实现
- **推荐阅读**：
  - Substrate Documentation
  - Polkadot Whitepaper

### 第 3 周：合约审计

- **映射章节**：2.2, 7.2
- **关键知识点**：
  - 安全审计方法
  - 漏洞检测技术
  - 最佳实践指南
- **实验任务**：
  - 审计 ink! 合约
  - 自动化检测工具
- **推荐阅读**：
  - Smart Contract Auditing
  - Security Best Practices

### 第 4 周：ZK 与现代密码学

- **映射章节**：3.2, 7.2
- **关键知识点**：
  - 零知识证明系统
  - 现代密码学应用
  - 隐私保护技术
- **实验任务**：
  - ZK 证明实现
  - 隐私计算协议
- **推荐阅读**：
  - Zero-Knowledge Proofs
  - Modern Cryptography

### 第 5 周：L2 与数据可用性

- **映射章节**：6.4, 7.2
- **关键知识点**：
  - Layer 2 解决方案
  - 数据可用性问题
  - 状态通道技术
- **实验任务**：
  - L2 协议实现
  - 数据可用性验证
- **推荐阅读**：
  - Layer 2 Solutions
  - Data Availability

### 第 6 周：系统化工程

- **映射章节**：5, 自动化推进
- **关键知识点**：
  - 工程最佳实践
  - 自动化工具链
  - 持续集成部署
- **实验任务**：
  - 构建完整工具链
  - 自动化测试部署
- **推荐阅读**：
  - Software Engineering
  - DevOps Practices

---

## Princeton - 比特币与加密货币

### 第 1 周：协议与攻击模型

- **映射章节**：6.2
- **关键知识点**：
  - 攻击向量分析
  - 安全模型设计
  - 威胁建模
- **实验任务**：
  - 模拟攻击场景
  - 防护机制实现
- **推荐阅读**：
  - Bitcoin Security
  - Attack Vectors

### 第 2 周：激励与博弈

- **映射章节**：6.1 扩展
- **关键知识点**：
  - 博弈论应用
  - 激励机制设计
  - 经济安全分析
- **实验任务**：
  - 激励模型分析
  - 博弈论模拟
- **推荐阅读**：
  - Game Theory in Blockchain
  - Cryptocurrency Economics

### 第 3 周：隐私与合规

- **映射章节**：3.3, 7.1
- **关键知识点**：
  - 隐私保护技术
  - 合规要求
  - 监管框架
- **实验任务**：
  - 隐私保护实现
  - 合规检查工具
- **推荐阅读**：
  - Privacy Technologies
  - Regulatory Compliance

### 第 4 周：扩展与未来

- **映射章节**：6.4, 7.*
- **关键知识点**：
  - 扩容技术发展
  - 未来趋势分析
  - 技术挑战
- **实验任务**：
  - 扩容方案设计
  - 未来技术调研
- **推荐阅读**：
  - Scaling Solutions
  - Future Trends

---

## 任务模板（每周）

### 标准任务结构

- **目标**：明确学习目标和技术要求
- **知识点**：核心概念和理论基础
- **实验**：实践任务和代码实现
- **代码参考**：相关代码示例和库
- **阅读**：推荐阅读材料
- **评测**：评估标准和检查点

### Rust 1.89 特性集成

- **生命周期语法检查**：在区块链节点和交易处理中应用
- **常量泛型推断**：优化哈希计算和密码学操作
- **FFI 改进**：与 C 语言区块链库的互操作
- **API 稳定性**：使用稳定的 API 提高代码可靠性
- **跨平台测试**：支持多平台区块链应用测试

### 质量保证

- **代码可运行性**：所有示例代码必须可编译运行
- **技术准确性**：概念和实现必须准确无误
- **更新及时性**：跟踪最新技术发展
- **参考权威性**：引用权威来源和标准文档
