# 01.1 全局知识图谱（中/英）

> 完成状态：已完成（100%）。本页锚点与图谱校验通过。
> 来源：`docs/KNOWLEDGE_GRAPH.md`, `docs/KNOWLEDGE_GRAPH_EN.md`

## 中文版本

```mermaid
graph TD
  A["算法与数据结构"]
  B["设计模式"]
  C["网络协议"]
  D["框架与微服务"]
  E["区块链"]
  F["WebAssembly"]
  G["IoT"]
  H["机器学习"]
  I["系统建模"]

  A -- 并发/分布式优化 --> C
  A -- 结构复用/组合 --> B
  B -- 架构复用/插件化 --> D
  C -- 协议一致性/分布式通信 --> D
  D -- 服务治理/自动化运维 --> E
  E -- 共识/安全/合约 --> C
  E -- 数据上链/可信计算 --> G
  F -- 跨平台/安全沙箱 --> D
  F -- AI推理/链上执行 --> H
  G -- 边缘智能/实时性 --> H
  G -- 设备数据/安全认证 --> C
  H -- 大数据/云原生 --> D
  H -- 模型验证/可解释性 --> I
  I -- 形式化建模/验证 --> A
  I -- 智能分析/系统仿真 --> H
  I -- 多模型协同/安全性 --> G
  F -- WASM建模/安全验证 --> I
  D -- 监控/可观测性 --> I
  C -- 网络安全/自动化测试 --> I
  B -- 自动化检测/重构 --> I
  E -- 智能合约/自动验证 --> I
  G -- 远程运维/自动化测试 --> I
  H -- 自动化训练/模型安全 --> I
```

> 本图谱自动生成，展现 Rust 形式化工程体系各主题间的理论与工程交叉关系。

## English Version

```mermaid
graph TD
  A["Algorithms & Data Structures"]
  B["Design Patterns"]
  C["Network Protocols"]
  D["Frameworks & Microservices"]
  E["Blockchain"]
  F["WebAssembly"]
  G["IoT"]
  H["Machine Learning"]
  I["System Modeling"]

  A -- Concurrency/Distributed Optimization --> C
  A -- Structural Reuse/Composition --> B
  B -- Architectural Reuse/Pluginization --> D
  C -- Protocol Consistency/Distributed Communication --> D
  D -- Service Governance/Automated Ops --> E
  E -- Consensus/Security/Contracts --> C
  E -- Data On-chain/Trusted Computing --> G
  F -- Cross-platform/Sandbox Security --> D
  F -- AI Inference/On-chain Execution --> H
  G -- Edge Intelligence/Real-time --> H
  G -- Device Data/Security Auth --> C
  H -- Big Data/Cloud Native --> D
  H -- Model Verification/Explainability --> I
  I -- Formal Modeling/Verification --> A
  I -- Intelligent Analysis/Simulation --> H
  I -- Multi-model Collaboration/Security --> G
  F -- WASM Modeling/Security Verification --> I
  D -- Monitoring/Observability --> I
  C -- Network Security/Automated Testing --> I
  B -- Automated Detection/Refactoring --> I
  E -- Smart Contract/Automated Verification --> I
  G -- Remote Ops/Automated Testing --> I
  H -- Automated Training/Model Security --> I
```

> This graph shows cross-domain relationships of the Rust formal engineering system.

## Cross-links

- 核心理论: `../01_core_theory/00_core_theory_index.md`
- 应用领域: `../04_application_domains/00_index.md`
- 形式化验证: `../08_formal_verification/00_index.md`

## 节点链接索引（双向导航）

- 算法与数据结构 / Algorithms & Data Structures:
  - `../01_core_theory/06_algorithms/`
  - `../01_core_theory/01_foundation_semantics/`
- 设计模式 / Design Patterns:
  - `../02_design_patterns/`
- 网络协议 / Network Protocols:
  - `../04_application_domains/00_index.md`
- 框架与微服务 / Frameworks & Microservices:
  - `../04_application_domains/00_index.md`
  - `../07_software_engineering/00_index.md`
- 区块链 / Blockchain:
  - `../04_application_domains/00_index.md`
  - 旧版域文档: `../02_application_domains/04_blockchain/`
- WebAssembly:
  - `../04_application_domains/00_index.md`
- IoT:
  - `../04_application_domains/00_index.md`
- 机器学习 / Machine Learning:
  - `../04_application_domains/00_index.md`
- 系统建模 / System Modeling:
  - `../08_formal_verification/00_index.md`
  - `../01_core_theory/00_core_theory_index.md`

## 系统编程专题深链索引

- 操作系统开发（总览）→ `../02_application_domains/01_system_programming/01_operating_system_development.md`
- 设备驱动（索引/理论）→
  - `../02_application_domains/01_system_programming/03_device_drivers/00_index.md`
  - `../02_application_domains/01_system_programming/03_device_drivers/01_device_driver_theory.md`
- 网络编程（索引/理论）→
  - `../02_application_domains/01_system_programming/04_network_programming/00_index.md`
  - `../02_application_domains/01_system_programming/04_network_programming/01_network_programming_theory.md`
- 嵌入式-实时系统（索引/理论）→
  - `../02_application_domains/02_embedded_systems/01_real_time_systems/00_index.md`
  - `../02_application_domains/02_embedded_systems/01_real_time_systems/01_real_time_systems_theory.md`
