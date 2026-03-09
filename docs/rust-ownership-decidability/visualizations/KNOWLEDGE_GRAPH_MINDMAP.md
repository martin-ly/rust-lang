# Rust 所有权系统 - 知识图谱思维导图

> 完整的知识体系可视化导航

---

## 1. 核心概念思维导图

```mermaid
mindmap
  root((Rust 所有权系统))
    所有权 Ownership
      三原则
        唯一所有者
        作用域绑定
        可转移性
      移动语义
        Copy trait
        Move trait
        Drop trait
      实现机制
        栈分配
        堆分配
        智能指针
    借用 Borrowing
      不可变借用 &T
        多个引用
        读取权限
        并发安全
      可变借用 &mut T
        排他性
        写入权限
        内部可变性
      借用规则
        XOR规则
        生命周期有效性
        作用域不重叠
    生命周期 Lifetimes
      显式生命周期
        'a, 'b, 'static
        生命周期注解
        省略规则
      子类型关系
        协变 Covariant
        逆变 Contravariant
        不变 Invariant
      高级话题
        Higher-Rank Trait Bounds
        生命周期捕获
        匿名生命周期
    类型系统
      泛型 Generics
        类型参数
        约束 Bounds
        关联类型
      Trait 系统
        泛型trait
        关联类型
        trait对象
      类型安全
        编译期检查
        零成本抽象
        内存安全保证
```

---

## 2. 定理依赖网络图

```mermaid
graph TB
    subgraph 数学基础
        M1[归纳原理]
        M2[良基关系]
    end

    subgraph 理论基础
        L1[Linearizable条件]
        L2[类型秩 ty_rank]
    end

    subgraph 语义基础
        S1[大步语义 eval]
        S2[小步语义 step]
    end

    subgraph 核心定理
        T1[终止性 Termination]
        T2[保持性 Preservation]
        T3[进展性 Progress]
        T4[类型安全 Type Safety]
        T5[可判定性 Decidability]
    end

    subgraph 应用定理
        A1[内存安全 Memory Safety]
        A2[程序正确性 Program Correctness]
    end

    M1 --> L1
    M2 --> L2
    M1 --> S1
    M1 --> S2

    L1 --> T1
    L2 --> T1

    S1 --> T2
    S2 --> T3

    T2 --> T4
    T3 --> T4
    T1 --> T5
    T4 --> T5

    T4 --> A1
    T4 --> A2

    style T1 fill:#f9f,stroke:#333,stroke-width:2px
    style T2 fill:#f9f,stroke:#333,stroke-width:2px
    style T3 fill:#f9f,stroke:#333,stroke-width:2px
    style T4 fill:#f9f,stroke:#333,stroke-width:3px
    style T5 fill:#f9f,stroke:#333,stroke-width:2px
```

---

## 3. 学习路径决策树

```mermaid
graph TD
    Start([开始学习 Rust 所有权]) --> Q1{你的背景?}

    Q1 -->|编程新手| B1[路径A: 快速入门]
    Q1 -->|有经验开发者| B2[路径B: 系统掌握]
    Q1 -->|研究者/形式化方法| B3[路径C: 形式化专家]

    B1 --> C1[概念卡片 15min]
    B1 --> C2[基础练习 45min]
    B1 --> C3[交互式指南 2h]

    C1 --> D1[所有权概念]
    C1 --> D2[借用概念]
    C1 --> D3[生命周期概念]

    C2 --> D4[所有权练习]
    C2 --> D5[借用练习]
    C2 --> D6[生命周期练习]

    B2 --> E1[详细概念 6h]
    B2 --> E2[设计模式 8h]
    B2 --> E3[并发模式 10h]
    B2 --> E4[案例研究 6h]

    E1 --> F1[所有权深入]
    E1 --> F2[借用深入]
    E1 --> F3[生命周期深入]
    E1 --> F4[内部可变性]

    E2 --> G1[创建型模式]
    E2 --> G2[结构型模式]
    E2 --> G3[行为型模式]
    E2 --> G4[Rust特有模式]

    B3 --> H1[数学基础 8h]
    B3 --> H2[Coq基础 10h]
    B3 --> H3[元理论 12h]
    B3 --> H4[可判定性 10h]

    H1 --> I1[线性逻辑]
    H1 --> I2[分离逻辑]
    H1 --> I3[类型论]

    H2 --> J1[Syntax]
    H2 --> J2[Semantics]
    H2 --> J3[Typing]

    D1 --> K[完成! 🎉]
    D4 --> K
    G1 --> K
    I1 --> K
```

---

## 4. 并发模式选择矩阵

```mermaid
graph LR
    subgraph 场景
        S1[共享数据]
        S2[消息传递]
        S3[并行计算]
        S4[异步IO]
    end

    subgraph 模式
        P1[Mutex/RwLock]
        P2[Channel]
        P3[Rayon]
        P4[Async/Await]
        P5[Actor]
    end

    subgraph 特性
        F1[简单]
        F2[高性能]
        F3[可扩展]
        F4[容错]
    end

    S1 --> P1
    S1 --> P5
    S2 --> P2
    S2 --> P5
    S3 --> P3
    S4 --> P4

    P1 --> F1
    P3 --> F2
    P4 --> F3
    P5 --> F4
```

---

## 5. 所有权转换状态机

```mermaid
stateDiagram-v2
    [*] --> Owned: let x = T::new()

    Owned --> Moved: let y = x
    Owned --> Borrowed: &x
    Owned --> MutBorrowed: &mut x
    Owned --> Dropped: 作用域结束

    Moved --> [*]: 值转移

    Borrowed --> Owned: 借用结束
    Borrowed --> Borrowed: 多个 &x

    MutBorrowed --> Owned: 借用结束
    MutBorrowed --> [*]: 修改后drop

    Dropped --> [*]: 释放资源
```

---

## 6. 验证工具选择决策树

```mermaid
graph TD
    Start([需要验证Rust代码]) --> Q1{验证目标?}

    Q1 -->|检测UB| A1[Miri]
    Q1 -->|并发测试| A2[Loom]
    Q1 -->|属性验证| A3{自动化程度?}

    A3 -->|全自动| A4[Kani]
    A3 -->|半自动| A5{验证深度?}

    A5 -->|功能正确| A6[Creusot]
    A5 -->|合约检查| A7[Prusti]
    A5 -->|系统验证| A8[Verus]

    A1 --> B1[运行时检查]
    A2 --> B2[状态空间探索]
    A4 --> B3[模型检测]
    A6 --> B4[定理证明]
    A7 --> B5[合约验证]
    A8 --> B6[系统验证]

    B1 --> End1[✅ 发现UB]
    B2 --> End2[✅ 发现竞态]
    B3 --> End3[✅ 属性验证]
    B4 --> End4[✅ 功能证明]
    B5 --> End5[✅ 合约满足]
    B6 --> End6[✅ 系统正确]
```

---

## 7. 模块依赖图

```mermaid
graph TB
    subgraph Core
        C1[所有权]
        C2[借用]
        C3[生命周期]
    end

    subgraph Advanced
        A1[内部可变性]
        A2[Pin/Unpin]
        A3[Send/Sync]
    end

    subgraph Concurrency
        Co1[线程安全]
        Co2[消息传递]
        Co3[锁-free]
    end

    subgraph Async
        As1[Future]
        As2[Pin]
        As3[运行时]
    end

    subgraph Formal
        F1[线性逻辑]
        F2[分离逻辑]
        F3[Coq证明]
    end

    C1 --> A1
    C2 --> A1
    C3 --> A2

    A1 --> Co1
    A3 --> Co1

    C1 --> As2
    C2 --> As2

    C1 --> F1
    C2 --> F2
    C3 --> F3
```

---

## 8. Rust 1.94 特性映射

```mermaid
mindmap
  root((Rust 1.94))
    类型系统增强
      Reborrow Trait
        隐式重借用
        生命周期调整
        Coq形式化
      CoerceShared Trait
        共享引用转换
        类型推导
        Coq形式化
      Const Generics
        常量泛型默认值
        类型级计算
        Coq形式化
      Precise Capturing
        精确生命周期捕获
        impl Trait
        Coq形式化
    语义增强
      Edition 2024
        新保留字
        语法调整
        迁移指南
      Async改进
        原生async trait
        性能优化
        Coq形式化
    工具链
      新Lint
         unsafe_code
        deprecated
      编译器优化
        借用检查器
        代码生成
```

---

## 9. 案例研究分类图

```mermaid
graph TB
    subgraph 异步
        A1[Tokio]
        A2[async-std]
        A3[smol]
    end

    subgraph Web框架
        W1[Actix-web]
        W2[Axum]
        W3[Rocket]
    end

    subgraph 数据库
        D1[Diesel]
        D2[SQLx]
        D3[SeaORM]
    end

    subgraph 并发
        C1[Crossbeam]
        C2[Rayon]
        C3[parking_lot]
    end

    subgraph 序列化
        S1[Serde]
        S2[rkyv]
        S3[postcard]
    end

    subgraph 嵌入式
        E1[Embassy]
        E2[RTIC]
        E3[cortex-m]
    end

    Core[核心概念] --> A1
    Core --> W1
    Core --> D1
    Core --> C1
    Core --> S1
    Core --> E1
```

---

## 10. 完整知识图谱

```mermaid
graph TB
    subgraph 理论层
        T1[线性逻辑]
        T2[分离逻辑]
        T3[类型论]
        T4[操作语义]
    end

    subgraph 核心层
        C1[所有权]
        C2[借用]
        C3[生命周期]
        C4[类型系统]
    end

    subgraph 模式层
        P1[设计模式]
        P2[并发模式]
        P3[架构模式]
    end

    subgraph 工具层
        V1[验证工具]
        V2[调试工具]
        V3[分析工具]
    end

    subgraph 应用层
        A1[案例研究]
        A2[最佳实践]
        A3[性能优化]
    end

    T1 --> C1
    T2 --> C2
    T3 --> C4
    T4 --> C3

    C1 --> P1
    C2 --> P2
    C3 --> P2
    C4 --> P3

    C1 --> V1
    C2 --> V2
    C3 --> V3

    P1 --> A1
    P2 --> A2
    P3 --> A3

    V1 --> A2
```

---

## 使用指南

### 如何选择图表

| 目的 | 推荐图表 |
|:-----|:---------|
| 了解整体结构 | 完整知识图谱、核心概念思维导图 |
| 规划学习路径 | 学习路径决策树 |
| 理解定理关系 | 定理依赖网络图 |
| 选择并发模式 | 并发模式选择矩阵、模式选择决策树 |
| 验证代码 | 验证工具选择决策树 |
| 查看所有权状态 | 所有权转换状态机 |

---

*这些图表使用 Mermaid 语法，可在支持 Mermaid 的 Markdown 查看器中渲染*
