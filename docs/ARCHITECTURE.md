# Rust 学习项目架构文档

> **版本**: Rust 1.96.0  
> **Edition**: 2024  
> **最后更新**: 2026-04-10

---

## 目录

- [项目概述](#项目概述)
- [架构总览](#架构总览)
- [Crate 关系图](#crate-关系图)
- [模块依赖图](#模块依赖图)
- [数据流图](#数据流图)

---

## 项目概述

本项目是一个全面的 Rust 语言系统化学习资源，采用 Workspace 架构组织，包含 12 个核心学习 crate 和 1 个共享库 crate。

### 设计原则

1. **渐进式学习**: 从基础到高级，每个 crate 对应一个学习阶段
2. **独立可运行**: 每个 crate 都可以独立编译和运行
3. **共享抽象**: 通过 `common` crate 提供共享工具
4. **生产就绪**: 完整的测试、基准测试和文档

---

## 架构总览

```mermaid
graph TB
    subgraph "Rust 学习项目 Workspace"
        direction TB
        
        subgraph "基础层 Tier 1"
            C01["📦 c01_ownership_borrow_scope<br/>所有权与借用"]
            C02["📦 c02_type_system<br/>类型系统"]
            C03["📦 c03_control_fn<br/>控制流与函数"]
        end
        
        subgraph "进阶层 Tier 2"
            C04["📦 c04_generic<br/>泛型与 Trait"]
            C05["📦 c05_threads<br/>线程与并发"]
            C06["📦 c06_async<br/>异步编程"]
        end
        
        subgraph "系统层 Tier 3"
            C07["📦 c07_process<br/>进程管理"]
            C08["📦 c08_algorithms<br/>算法与数据结构"]
        end
        
        subgraph "应用层 Tier 4"
            C09["📦 c09_design_pattern<br/>设计模式"]
            C10["📦 c10_networks<br/>网络编程"]
            C11["📦 c11_macro_system<br/>宏系统"]
            C12["📦 c12_wasm<br/>WebAssembly"]
        end
        
        subgraph "共享层"
            COMMON["📦 common<br/>共享库"]
        end
    end
    
    %% 依赖关系
    C02 --> C01
    C03 --> C02
    C04 --> C02
    C05 --> C01
    C06 --> C05
    C07 --> C06
    C08 --> C04
    C09 --> C04
    C10 --> C06
    C10 --> C07
    C11 --> C04
    C12 --> C06
    
    %% 共享库依赖
    C01 --> COMMON
    C02 --> COMMON
    C03 --> COMMON
    C04 --> COMMON
    C05 --> COMMON
    C06 --> COMMON
    C07 --> COMMON
    C08 --> COMMON
    C09 --> COMMON
    C10 --> COMMON
    C11 --> COMMON
    C12 --> COMMON
```

---

## Crate 关系图

### 详细依赖关系

```mermaid
flowchart LR
    subgraph "外部依赖"
        TOKIO["⚡ Tokio"]
        SERDE["📄 Serde"]
        TRACING["🔍 Tracing"]
        RAYON["🔄 Rayon"]
        CROSSBEAM["📡 Crossbeam"]
    end
    
    subgraph "核心 Crate"
        direction TB
        C01["C01: 所有权"]
        C02["C02: 类型系统"]
        C03["C03: 控制流"]
        C04["C04: 泛型"]
        C05["C05: 线程"]
        C06["C06: 异步"]
        C07["C07: 进程"]
        C08["C08: 算法"]
        C09["C09: 设计模式"]
        C10["C10: 网络"]
        C11["C11: 宏系统"]
        C12["C12: WASM"]
    end
    
    %% 外部依赖连接
    C06 --> TOKIO
    C05 --> RAYON
    C05 --> CROSSBEAM
    C10 --> TOKIO
    C01 --> SERDE
    C06 --> TRACING
```

### Crate 特性矩阵

| Crate | 核心概念 | 外部依赖 | 特性标志 | 示例数量 |
|-------|----------|----------|----------|----------|
| c01_ownership | 所有权、借用、生命周期 | tokio, serde | - | 15+ |
| c02_type_system | 类型系统、泛型 | serde, tokio, futures | - | 20+ |
| c03_control_fn | 控制流、函数、异步 | tokio, tracing | async, std | 12+ |
| c04_generic | 泛型、Trait、GAT | rayon, itertools | - | 18+ |
| c05_threads | 并发、同步、锁 | crossbeam, rayon | std, tokio | 25+ |
| c06_async | 异步运行时、Future | tokio, actix-web, axum | full | 30+ |
| c07_process | 进程、IPC、信号 | nix, memmap2 | async, unix | 15+ |
| c08_algorithms | 算法、数据结构 | rayon, petgraph | bench | 40+ |
| c09_design_pattern | 设计模式 | tokio, rayon | obs-tracing | 20+ |
| c10_networks | 网络协议、WebSocket | tokio, tonic, rustls | tls, sniff | 25+ |
| c11_macro_system | 宏规则、过程宏 | syn, quote | serde_support | 10+ |
| c12_wasm | WebAssembly、WASI | wasm-bindgen, js-sys | ecosystem | 8+ |

---

## 模块依赖图

### 内部模块结构

```mermaid
graph TB
    subgraph "C01: 所有权系统"
        C01_Lib["lib.rs"]
        C01_Ownership["ownership/"]
        C01_Borrow["borrow/"]
        C01_Lifetime["lifetime/"]
        C01_SmartPtr["smart_pointers/"]
    end
    
    subgraph "C02: 类型系统"
        C02_Lib["lib.rs"]
        C02_Basic["basic_types/"]
        C02_Adv["advanced_types/"]
        C02_Coll["collections/"]
        C02_Trait["traits/"]
    end
    
    subgraph "C05: 线程并发"
        C05_Lib["lib.rs"]
        C05_Basic["basic_threads/"]
        C05_Sync["synchronization/"]
        C05_Lockfree["lock_free/"]
        C05_Parallel["parallel/"]
    end
    
    subgraph "C06: 异步编程"
        C06_Lib["lib.rs"]
        C06_Basic["async_basics/"]
        C06_Runtime["runtime/"]
        C06_Stream["streams/"]
        C06_Web["web_frameworks/"]
    end
    
    subgraph "C08: 算法"
        C08_Lib["lib.rs"]
        C08_Sort["sorting/"]
        C08_Graph["graph/"]
        C08_Tree["tree/"]
        C08_ML["machine_learning/"]
    end
    
    subgraph "C10: 网络"
        C10_Lib["lib.rs"]
        C10_TCP["tcp/"]
        C10_UDP["udp/"]
        C10_HTTP["http/"]
        C10_WS["websocket/"]
        C10_GRPC["grpc/"]
    end
    
    %% 模块间依赖
    C01_Lib --> C01_Ownership
    C01_Lib --> C01_Borrow
    C01_Lib --> C01_Lifetime
    C01_Lib --> C01_SmartPtr
    
    C02_Lib --> C02_Basic
    C02_Lib --> C02_Adv
    C02_Lib --> C02_Coll
    C02_Lib --> C02_Trait
    
    C05_Lib --> C05_Basic
    C05_Lib --> C05_Sync
    C05_Lib --> C05_Lockfree
    C05_Lib --> C05_Parallel
    
    C06_Lib --> C06_Basic
    C06_Lib --> C06_Runtime
    C06_Lib --> C06_Stream
    C06_Lib --> C06_Web
    
    C08_Lib --> C08_Sort
    C08_Lib --> C08_Graph
    C08_Lib --> C08_Tree
    C08_Lib --> C08_ML
    
    C10_Lib --> C10_TCP
    C10_Lib --> C10_UDP
    C10_Lib --> C10_HTTP
    C10_Lib --> C10_WS
    C10_Lib --> C10_GRPC
```

---

## 数据流图

### 学习路径数据流

```mermaid
flowchart LR
    subgraph "输入"
        A["源代码"]
        B["配置"]
        C["测试数据"]
    end
    
    subgraph "处理层"
        D["编译检查"]
        E[" Miri 验证"]
        F["测试执行"]
        G["基准测试"]
    end
    
    subgraph "输出"
        H["二进制/库"]
        I["测试报告"]
        J["覆盖率"]
        K["性能指标"]
    end
    
    A --> D
    B --> D
    D --> E
    D --> F
    D --> G
    E --> H
    F --> I
    F --> J
    G --> K
```

### 运行时数据流（以异步模块为例）

```mermaid
sequenceDiagram
    participant Main as 主函数
    participant RT as Tokio Runtime
    participant Task as 异步任务
    participant IO as I/O 操作
    participant Res as 结果处理
    
    Main->>RT: 初始化运行时
    RT->>Task: 生成任务
    Task->>IO: 发起异步 I/O
    IO-->>Task: 返回 Future
    Task->>RT: yield 等待
    IO-->>RT: I/O 完成通知
    RT->>Task: 恢复执行
    Task->>Res: 处理结果
    Res-->>Main: 返回最终结果
```

---

## 架构决策记录

### ADR-001: Workspace 结构

**状态**: 已接受

**决策**: 使用 Cargo Workspace 组织多个学习 crate。

**原因**:
- 允许独立版本控制
- 支持跨 crate 依赖
- 统一依赖管理
- 并行编译优化

### ADR-002: Common Crate

**状态**: 已接受

**决策**: 创建独立的 `common` crate 提供共享功能。

**原因**:
- 避免代码重复
- 统一错误处理
- 共享测试工具
- 可配置特性标志

### ADR-003: 渐进式特性

**状态**: 已接受

**决策**: 使用 Cargo features 控制高级功能。

**原因**:
- 减少编译时间
- 可选依赖管理
- 平台特定支持
- 灵活的功能组合

---

## 技术栈

### 核心运行时
- **Tokio**: 异步运行时 (v1.51+)
- **Rayon**: 数据并行 (v1.11+)
- **Crossbeam**: 并发原语 (v0.8+)

### 序列化
- **Serde**: 通用序列化 (v1.0+)
- **Serde JSON**: JSON 支持 (v1.0+)

### 网络
- **Hyper**: HTTP 底层 (v1.9+)
- **Tonic**: gRPC 框架 (v0.14+)
- **Tungstenite**: WebSocket (v0.29+)

### 日志与追踪
- **Tracing**: 结构化日志 (v0.1+)
- **Prometheus**: 指标收集 (v0.14+)

---

## 参考资料

- [Cargo Workspace 文档](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Rust 模块系统](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)
- [Tokio 运行时](https://tokio.rs/)
