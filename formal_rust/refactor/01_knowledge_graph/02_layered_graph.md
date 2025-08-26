# 01.2 分层知识图谱（中文）

> 来源：`docs/KNOWLEDGE_GRAPH_LAYERED.md`

```mermaid
graph TD
  subgraph 基础理论层
    A1["算法与数据结构"]
    A2["类型系统与安全性"]
    A3["并发与分布式理论"]
    A4["设计模式"]
  end

  subgraph 工程实现层
    B1["网络协议"]
    B2["框架与微服务"]
    B3["区块链"]
    B4["WebAssembly"]
    B5["IoT"]
    B6["机器学习"]
    B7["系统建模"]
  end

  subgraph 自动化与工具链层
    C1["自动化测试"]
    C2["性能基准"]
    C3["形式化验证"]
    C4["CI/CD"]
    C5["安全审计"]
    C6["可观测性"]
    C7["文档/国际化"]
  end

  subgraph 交叉专题层
    D1["分布式一致性与共识"]
    D2["边缘智能与数据上链"]
    D3["AI+区块链+IoT 融合"]
    D4["自动化运维与远程升级"]
    D5["模型验证与智能分析"]
  end

  A1 -- 结构复用/组合 --> A4
  A1 -- 类型安全/泛型 --> A2
  A3 -- 并发/一致性理论 --> B1
  A3 -- 分布式优化 --> B2
  A4 -- 架构复用/插件化 --> B2
  B1 -- 协议一致性/分布式通信 --> B2
  B2 -- 服务治理/自动化运维 --> C4
  B3 -- 共识/安全/合约 --> D1
  B3 -- 数据上链/可信计算 --> D2
  B4 -- 跨平台/安全沙箱 --> B2
  B4 -- AI推理/链上执行 --> B6
  B5 -- 边缘智能/实时性 --> D2
  B5 -- 设备数据/安全认证 --> C5
  B6 -- 大数据/云原生 --> B2
  B6 -- 模型验证/可解释性 --> D5
  B7 -- 形式化建模/验证 --> C3
  B7 -- 智能分析/系统仿真 --> D5
  C1 -- 自动化测试/属性测试 --> B1
  C2 -- 性能基准/分析 --> B2
  C3 -- 形式化验证/不变式 --> B7
  C4 -- 持续集成/部署 --> B2
  C5 -- 安全审计/合约分析 --> B3
  C6 -- 监控/可观测性 --> B2
  C7 -- 文档/国际化 --> B2
  D1 -- 共识安全/分布式一致性 --> B3
  D2 -- 边缘智能/数据上链 --> B5
  D3 -- AI+区块链+IoT 融合 --> B6
  D4 -- 自动化运维与远程升级 --> B5
  D5 -- 智能分析/模型验证 --> B7
```

## Cross-links

- 并发语义: `../09_concurrency_semantics/00_index.md`
- 形式化验证: `../08_formal_verification/00_index.md`
- 软件工程: `../07_software_engineering/00_index.md`

## 节点链接索引（分层映射）

- A2 类型系统与安全性 → `../01_core_theory/02_type_system/`
- A3 并发与分布式理论 → `../09_concurrency_semantics/00_index.md`
- B1 网络协议 → `../04_application_domains/01_system_programming/04_network_programming/00_index.md`
- B2 框架与微服务 → `../07_software_engineering/00_index.md`
- B3 区块链 → `../04_application_domains/00_index.md`
- C2 性能基准 → `../05_performance_optimization/00_index.md`
- C3 形式化验证 → `../08_formal_verification/00_index.md`
- C4 CI/CD → `../07_software_engineering/00_index.md`
- C5 安全审计 → `../06_security_verification/00_index.md`
