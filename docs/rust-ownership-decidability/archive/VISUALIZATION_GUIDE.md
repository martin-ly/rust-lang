# Rust所有权与可判定性 - 可视化指南

本指南提供多种思维表征方式，帮助理解整个论证体系。

---

## 一、所有权系统演化时间线

```mermaid
timeline
    title Rust所有权系统演化
    1970s : 线性逻辑诞生
          : Girard提出资源敏感逻辑
    1980s : 仿射类型发展
          : 弱化规则引入
    1990s : 分离逻辑
          : O'Hearn/Reynolds堆推理
    2006s : Rust项目启动
          : Graydon Hoare设计所有权
    2010s : RustBelt项目
          : 形式化语义验证
    2015s : Rust 1.0发布
          : 所有权系统稳定
    2018s : NLL引入
          : 非词法生命周期
    2020s : 形式化工具成熟
          : Creusot/Prusti/Kani
    2024s : 常量泛型
          : 类型级计算能力
```

---

## 二、概念层次结构图

```mermaid
graph TB
    subgraph 理论基础
    L1[线性逻辑] --> L2[资源 = 类型]
    A1[仿射类型] --> A2[使用 ≤ 1次]
    S1[分离逻辑] --> S2[*P 堆断言]
    end

    subgraph 核心抽象
    O1[所有权] --> O2[独占访问]
    O1 --> O3[RAII]
    B1[借用] --> B2[&T 共享]
    B1 --> B3[&mut T 独占]
    end

    subgraph 实现机制
    R1[区域系统] --> R2[生命周期]
    C1[约束求解] --> C2[NLL算法]
    end

    subgraph 工程应用
    P1[模式匹配] --> P2[解构赋值]
    G1[泛型] --> G2[trait系统]
    F1[FFI] --> F2[unsafe边界]
    end

    L2 --> O1
    A2 --> O1
    S2 --> O1
    O2 --> B1
    O3 --> R1
    B2 --> C1
    B3 --> C1
    R2 --> P1
    C2 --> G1
    G2 --> F1
```

---

## 三、安全保证层次金字塔

```text
                    ▲
                   /│\
                  / │ \
                 /  │  \        Level 4: 形式化验证
                /   │   \       (RustBelt定理证明)
               /────┼────\
              /     │      \     Level 3: 工具验证
             /      │       \    (Creusot/Kani)
            /───────┼────────\
           /        │         \  Level 2: 类型系统
          /         │          \ (编译器检查)
         /──────────┼───────────\
        /           │            \ Level 1: 运行时
       /            │             \ (panic/UB检测)
      /─────────────┼──────────────\
     /              │               \ Level 0: 硬件
    /               │                \ (内存保护)
   ───────────────────────────────────
```

### 各层说明

| 层级 | 机制 | 保证 | 失败模式 |
|:-----|:-----|:-----|:---------|
| L4 | 定理证明 | 数学正确性 | 证明错误 |
| L3 | 模型检测 | 属性满足 | 状态爆炸 |
| L2 | 类型检查 | 内存安全 | 编译错误 |
| L1 | 运行时检查 | 越界检测 | panic/崩溃 |
| L0 | MMU/保护 | 物理隔离 | 硬件故障 |

---

## 四、借用检查流程图

```mermaid
flowchart TD
    A[开始: 函数/代码块] --> B[收集借用]
    B --> C{存在 &mut T?}

    C -->|是| D{存在 &T?}
    C -->|否| E[所有 &T 有效]

    D -->|是| F[编译错误!]
    D -->|否| G[检查生命周期]

    E --> G
    G --> H{约束可满足?}

    H -->|是| I[生成MIR]
    H -->|否| J[生命周期错误!]

    I --> K[优化]
    K --> L[生成机器码]
    L --> M[结束: 安全代码]

    F --> N[修复: 调整借用]
    J --> O[修复: 添加标注]

    N --> B
    O --> B

    style F fill:#f99,stroke:#333
    style J fill:#f99,stroke:#333
    style M fill:#9f9,stroke:#333
```

---

## 五、类型状态转换图

```mermaid
stateDiagram-v2
    [*] --> Owned: let x = value

    Owned --> Moved: let y = x
    Owned --> Borrowed: let r = &x
    Owned --> MutBorrowed: let r = &mut x
    Owned --> Dropped: 作用域结束

    Moved --> [*]: x 不可再用

    Borrowed --> Owned: 借用结束
    Borrowed --> Borrowed: 重借 &*&x

    MutBorrowed --> Owned: 借用结束
    MutBorrowed --> MutBorrowed: 重借 &mut *r

    Dropped --> [*]: 内存释放

    note right of Owned
        唯一所有者
        可读可写
    end note

    note right of Moved
        所有权转移
        原变量无效
    end note

    note right of Borrowed
        共享引用
        只读访问
    end note

    note right of MutBorrowed
        独占引用
        唯一写者
    end note
```

---

## 六、生命周期包含关系图

```mermaid
graph BT
    subgraph 长生命周期
    L1['static]
    L2[函数生命周期]
    L3[块生命周期]
    end

    subgraph 引用关系
    R1[返回值 &'a T]
    R2[参数 &'b T]
    R3[局部 &T]
    end

    L1 --> L2
    L2 --> L3

    L1 -.->|包含| R1
    L2 -.->|包含| R2
    L3 -.->|包含| R3

    R2 --> R1
    note["'b: 'a 约束"]
```

---

## 七、验证工具能力矩阵雷达图

```text
                    表达能力
                       5
                       │
                       │
        自动化 4 ─────┼───── 4 自动化
                    ╱ │ ╲
                 ╱   │   ╲
              ╱      │      ╲
     可用性 3 ────────┼──────── 3 可用性
              ╲      │      ╱
                 ╲   │   ╱
                    ╲ │ ╱
        性能 2 ─────┼───── 2 性能
                       │
                       │
                       1
                    覆盖范围

    RustBelt  ████████████████████  (4,2,3,4,4) 高表达,低自动
    Creusot   ████████████████     (4,3,3,3,4) 平衡
    Prusti    ██████████████       (3,4,4,3,3) 高自动
    Kani      ████████████         (3,4,4,2,3) 模型检测
    Miri      ██████████           (2,5,5,2,2) 运行时
    rustc     ████████████████     (3,5,5,3,3) 类型系统
```

---

## 八、案例研究分类树

```text
案例研究/
├── 嵌入式生态 (15个)
│   ├── 异步运行时
│   │   ├── embassy (静态任务)
│   │   └── rtic (实时调度)
│   ├── 网络协议
│   │   └── smoltcp (零拷贝TCP/IP)
│   ├── 存储
│   │   ├── embedded-storage
│   │   └── littlefs2 (断电安全)
│   ├── 硬件抽象
│   │   ├── nrf-hal
│   │   ├── stm32f4xx-hal
│   │   └── embedded-hal
│   └── 工具
│       ├── defmt
│       ├── panic-probe
│       └── probe-rs
│
└── 应用级生态 (24个)
    ├── Web/网络 (7个)
    │   ├── axum (类型安全路由)
    │   ├── actix-web (Actor模型)
    │   ├── tokio (异步运行时)
    │   ├── tower (服务组合)
    │   ├── hyper (HTTP实现)
    │   ├── reqwest (HTTP客户端)
    │   └── tonic (gRPC)
    ├── 数据库 (3个)
    │   ├── diesel (编译时SQL)
    │   ├── sqlx (宏验证)
    │   └── sea-orm (类型安全)
    ├── 并发原语 (5个)
    │   ├── rayon (数据并行)
    │   ├── crossbeam (无锁)
    │   ├── dashmap (分片锁)
    │   ├── parking_lot (紧凑锁)
    │   └── tokio-stream (流处理)
    ├── 异步基础设施 (4个)
    │   ├── async-trait
    │   ├── pin-project
    │   └── bytes
    ├── 序列化/CLI (2个)
    │   ├── serde
    │   └── clap
    ├── 错误处理/日志 (2个)
    │   ├── thiserror/anyhow
    │   └── tracing
    └── FFI/工具 (1个)
        ├── wasm-bindgen
        ├── pyo3
        └── chrono
```

---

## 九、学习路径图

```mermaid
graph LR
    subgraph 入门阶段
    A[理解所有权] --> B[借用检查器]
    B --> C[生命周期]
    end

    subgraph 进阶阶段
    C --> D[内部可变性]
    D --> E[智能指针]
    E --> F[生命周期省略]
    end

    subgraph 高级阶段
    F --> G[Pin/Unpin]
    G --> H[异步Rust]
    H --> I[FFI边界]
    end

    subgraph 专家阶段
    I --> J[unsafe代码]
    J --> K[形式化验证]
    K --> L[定理证明]
    end

    style A fill:#bbf,stroke:#333
    style G fill:#bfb,stroke:#333
    style L fill:#f9f,stroke:#333
```

---

## 十、核心定理汇总表

| 定理名称 | 领域 | 陈述 | 意义 |
|:---------|:-----|:-----|:-----|
| **所有权唯一性** | 核心 | ∀x: T. owner(x) = 1 | 内存安全基础 |
| **借用互斥** | 借用 | &mut T ⟹ ¬&T | 防止数据竞争 |
| **生命周期包含** | 区域 | 'a: 'b ⟹ 'a ≥ 'b | 引用有效性 |
| **NLL可判定性** | 算法 | 借用检查 ∈ P | 编译可行性 |
| **RustBelt安全性** | 形式化 | Rust ⊨ memory safety | 数学保证 |
| **零成本抽象** | 性能 | 静态检查 → 0运行时开销 | 效率保证 |

---

## 十一、反模式检测决策树

```text
                    ┌─────────────────────────┐
                    │     编译错误？           │
                    └───────────┬─────────────┘
                                │
              ┌─────────────────┼─────────────────┐
              │borrow checker    │lifetime           │其他
              ▼                  ▼                  ▼
    ┌──────────────────┐ ┌──────────────┐ ┌─────────────────┐
    │ 同时持有&和&mut？ │ │ 'a vs 'static │ │ 类型不匹配      │
    └────────┬─────────┘ └──────┬───────┘ └────────┬────────┘
             │                  │                  │
    ┌────────┴────────┐  ┌──────┴──────┐  ┌────────┴────────┐
    │是                │否 │需要更长生长期 │ │ 检查trait实现   │
    ▼                  ▼  ▼             │否 ▼                 │
┌──────────┐    ┌──────────┐  ┌────────┴────────┐  ┌─────────┴───┐
│ 重构访问  │    │ 检查     │  │ 显式标注        │  │ 添加derive  │
│ 模式      │    │ 借用     │  │ 生命周期        │  │ 或impl      │
│ 分离读写  │    │ 顺序     │  │                 │  │             │
└──────────┘    └──────────┘  └─────────────────┘  └─────────────┘
```

---

## 十二、资源与进一步阅读

| 主题 | 推荐资源 |
|:-----|:---------|
| 理论基础 | TAPL (Types and Programming Languages) |
| 线性逻辑 | Girard's "Linear Logic" |
| 分离逻辑 | O'Hearn's papers on Separation Logic |
| RustBelt | POPL 2018 paper |
| 实践指南 | The Rust Programming Language (Book) |
| 高级主题 | Rust for Rustaceans |
| 形式化工具 | Creusot tutorial, Prusti user guide |
