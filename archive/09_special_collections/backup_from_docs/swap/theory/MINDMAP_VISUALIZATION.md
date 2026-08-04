# C01 所有权系统 思维导图与可视化

> **文档定位**: Rust 1.90 所有权系统可视化学习  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **文档类型**: 思维导图 + 流程图 + 架构图

---

## 📊 目录

- [C01 所有权系统 思维导图与可视化](#c01-所有权系统-思维导图与可视化)
  - [📊 目录](#-目录)
  - [1. 所有权系统全景思维导图](#1-所有权系统全景思维导图)
    - [核心概念体系](#核心概念体系)
  - [2. 所有权转移流程图](#2-所有权转移流程图)
    - [Move语义流程](#move语义流程)
    - [所有权转移决策树](#所有权转移决策树)
  - [3. 借用系统架构图](#3-借用系统架构图)
    - [借用检查器架构](#借用检查器架构)
    - [借用冲突检测流程](#借用冲突检测流程)
  - [4. 生命周期系统](#4-生命周期系统)
    - [生命周期标注流程](#生命周期标注流程)
    - [生命周期省略规则](#生命周期省略规则)
  - [5. 智能指针架构](#5-智能指针架构)
    - [智能指针类型关系](#智能指针类型关系)
    - [引用计数流程](#引用计数流程)
  - [6. 内存布局可视化](#6-内存布局可视化)
    - [栈与堆内存布局](#栈与堆内存布局)
    - [内存分配流程](#内存分配流程)
  - [7. 并发所有权模型](#7-并发所有权模型)
    - [Send与Sync架构](#send与sync架构)
    - [线程安全决策流程](#线程安全决策流程)
  - [相关文档](#相关文档)
  - [返回导航](#返回导航)

---

## 1. 所有权系统全景思维导图

### 核心概念体系

```mermaid
mindmap
  root((所有权系统))
    所有权规则
      每个值有唯一所有者
      所有者离开作用域值被drop
      值可以转移所有权
      移动语义
        Move
        所有权转移
        原变量失效
      复制语义
        Copy trait
        栈上复制
        原变量保留
    借用系统
      不可变借用 &T
        多个同时存在
        只读访问
        无数据竞争
      可变借用 &mut T
        唯一存在
        独占访问
        修改数据
      借用规则
        不可同时存在
        借用期间所有者不可变
        作用域限制
    生命周期
      生命周期参数 'a
        泛型参数
        约束关系
        省略规则
      生命周期边界
        函数签名
        结构体定义
        trait约束
      生命周期省略
        输入生命周期
        输出生命周期
        self规则
    智能指针
      Box<T>
        堆分配
        独占所有权
        实现Deref
      Rc<T>
        引用计数
        共享所有权
        Clone增加计数
      Arc<T>
        原子引用计数
        线程安全
        跨线程共享
      RefCell<T>
        内部可变性
        运行时检查
        单线程使用
      Mutex<T>
        线程安全
        互斥锁
        独占访问
    内存管理
      栈分配
        快速
        固定大小
        自动回收
      堆分配
        灵活大小
        手动管理
        通过所有权
      Drop trait
        析构函数
        资源释放
        RAII模式
```

---

## 2. 所有权转移流程图

### Move语义流程

```mermaid
flowchart TD
    Start[创建值] --> Assign[赋值给变量]
    Assign --> Check{实现Copy?}
    
    Check -->|是| Copy[复制值]
    Check -->|否| Move[移动所有权]
    
    Copy --> Origin1[原变量有效]
    Copy --> New1[新变量有效]
    
    Move --> Origin2[原变量失效]
    Move --> New2[新变量获得所有权]
    
    Origin1 --> Use1{继续使用?}
    New1 --> Use2{继续使用?}
    Origin2 --> Error[编译错误]
    New2 --> Use3{继续使用?}
    
    Use1 -->|是| Valid1[合法使用]
    Use2 -->|是| Valid2[合法使用]
    Use3 -->|是| Valid3[合法使用]
    
    Valid1 --> End[结束]
    Valid2 --> End
    Valid3 --> End
    Error --> End
    
    style Start fill:#e3f2fd
    style Copy fill:#c8e6c9
    style Move fill:#fff3e0
    style Error fill:#ffcdd2
    style End fill:#e8f5e9
```

### 所有权转移决策树

```mermaid
flowchart TD
    Start[需要传递值] --> Size{值大小?}
    
    Size -->|小<64B| Stack{栈上类型?}
    Size -->|大>64B| Heap[使用Box/引用]
    
    Stack -->|是| CopyCheck{实现Copy?}
    Stack -->|否| Heap
    
    CopyCheck -->|是| UseCopy[直接复制]
    CopyCheck -->|否| Borrow{需要所有权?}
    
    Borrow -->|否| UseRef[使用引用 &T]
    Borrow -->|是| Move[移动所有权]
    
    Heap --> Multi{多个所有者?}
    Multi -->|否| UseBox[Box<T>]
    Multi -->|是| Thread{跨线程?}
    
    Thread -->|否| UseRc[Rc<T>]
    Thread -->|是| UseArc[Arc<T>]
    
    UseCopy --> End[完成]
    UseRef --> End
    Move --> End
    UseBox --> End
    UseRc --> End
    UseArc --> End
    
    style Start fill:#e3f2fd
    style UseCopy fill:#c8e6c9
    style UseRef fill:#bbdefb
    style End fill:#e8f5e9
```

---

## 3. 借用系统架构图

### 借用检查器架构

```mermaid
graph TB
    subgraph Source [源代码]
        Code[Rust源码]
    end
    
    subgraph Parser [语法分析]
        AST[抽象语法树]
        HIR[高级中间表示]
    end
    
    subgraph BorrowChecker [借用检查器]
        NLL[非词法生命周期]
        LivenessAnalysis[活性分析]
        BorrowAnalysis[借用分析]
        
        subgraph Rules [借用规则]
            Rule1[规则1: &T多个]
            Rule2[规则2: &mut T唯一]
            Rule3[规则3: 不可同时]
        end
        
        ConflictDetection[冲突检测]
    end
    
    subgraph MIR [中级中间表示]
        MIRGen[MIR生成]
        MIROptim[MIR优化]
    end
    
    subgraph Output [输出]
        Success[编译通过]
        Error[借用错误]
    end
    
    Code --> AST
    AST --> HIR
    HIR --> NLL
    
    NLL --> LivenessAnalysis
    LivenessAnalysis --> BorrowAnalysis
    BorrowAnalysis --> Rules
    
    Rules --> ConflictDetection
    
    ConflictDetection -->|无冲突| MIRGen
    ConflictDetection -->|有冲突| Error
    
    MIRGen --> MIROptim
    MIROptim --> Success
    
    style BorrowChecker fill:#fff3e0
    style Rules fill:#f3e5f5
    style Success fill:#c8e6c9
    style Error fill:#ffcdd2
```

### 借用冲突检测流程

```mermaid
sequenceDiagram
    participant Code as 源代码
    participant Checker as 借用检查器
    participant Analyzer as 活性分析器
    participant Rules as 规则引擎
    participant Reporter as 错误报告
    
    Code->>Checker: 提交代码块
    activate Checker
    
    Checker->>Analyzer: 分析变量生命周期
    activate Analyzer
    Analyzer->>Analyzer: 构建生命周期图
    Analyzer-->>Checker: 返回生命周期信息
    deactivate Analyzer
    
    Checker->>Rules: 检查借用规则
    activate Rules
    
    Rules->>Rules: 检查规则1<br/>多个&T?
    Rules->>Rules: 检查规则2<br/>唯一&mut T?
    Rules->>Rules: 检查规则3<br/>&T与&mut T冲突?
    
    alt 无冲突
        Rules-->>Checker: 通过
        Checker-->>Code: 编译通过
    else 有冲突
        Rules->>Reporter: 报告冲突
        Reporter-->>Code: 借用错误<br/>E0502/E0503
    end
    
    deactivate Rules
    deactivate Checker
```

---

## 4. 生命周期系统

### 生命周期标注流程

```mermaid
flowchart TD
    Start[编写函数] --> HasRef{有引用参数?}
    
    HasRef -->|否| NoLifetime[无需生命周期]
    HasRef -->|是| Multi{多个引用?}
    
    Multi -->|否| Elision{省略规则适用?}
    Multi -->|是| Explicit[显式标注]
    
    Elision -->|是| Auto[自动推导]
    Elision -->|否| Explicit
    
    Explicit --> Input[标注输入生命周期]
    Input --> Output[标注输出生命周期]
    Output --> Constraint[添加约束关系]
    
    Constraint --> Verify{编译器验证}
    
    Verify -->|通过| Success[编译通过]
    Verify -->|失败| Error[生命周期错误]
    
    NoLifetime --> Success
    Auto --> Success
    
    Error --> Fix{修复?}
    Fix -->|是| Explicit
    Fix -->|否| End[编译失败]
    
    Success --> End
    
    style Start fill:#e3f2fd
    style Success fill:#c8e6c9
    style Error fill:#ffcdd2
    style End fill:#e8f5e9
```

### 生命周期省略规则

```mermaid
stateDiagram-v2
    [*] --> 分析函数签名
    
    分析函数签名 --> 规则1: 单个输入引用
    分析函数签名 --> 规则2: 多个输入引用
    分析函数签名 --> 规则3: &self或&mut self
    
    规则1 --> 省略1: 输入生命周期赋给输出
    规则2 --> 不省略: 需要显式标注
    规则3 --> 省略3: self生命周期赋给输出
    
    省略1 --> [*]: 自动推导
    不省略 --> [*]: 手动标注
    省略3 --> [*]: 自动推导
    
    note right of 规则1
        fn foo<'a>(x: &'a i32) -> &'a i32
        可省略为
        fn foo(x: &i32) -> &i32
    end note
    
    note right of 规则3
        fn foo<'a>(&'a self) -> &'a str
        可省略为
        fn foo(&self) -> &str
    end note
```

---

## 5. 智能指针架构

### 智能指针类型关系

```mermaid
graph TB
    subgraph Ownership [所有权模型]
        Unique[独占所有权]
        Shared[共享所有权]
        Interior[内部可变性]
    end
    
    subgraph SingleThread [单线程]
        Box[Box&lt;T&gt;<br/>独占+堆分配]
        Rc[Rc&lt;T&gt;<br/>共享+引用计数]
        RefCell[RefCell&lt;T&gt;<br/>运行时借用]
        Cell[Cell&lt;T&gt;<br/>Copy类型]
    end
    
    subgraph MultiThread [多线程]
        Arc[Arc&lt;T&gt;<br/>原子引用计数]
        Mutex[Mutex&lt;T&gt;<br/>互斥锁]
        RwLock[RwLock&lt;T&gt;<br/>读写锁]
        Atomic[Atomic*<br/>原子类型]
    end
    
    Unique --> Box
    Shared --> Rc
    Shared --> Arc
    Interior --> RefCell
    Interior --> Cell
    Interior --> Mutex
    Interior --> RwLock
    
    Rc -.->|线程安全版本| Arc
    RefCell -.->|线程安全版本| Mutex
    Mutex -.->|读写分离| RwLock
    Cell -.->|原子版本| Atomic
    
    style Ownership fill:#e3f2fd
    style SingleThread fill:#fff3e0
    style MultiThread fill:#f3e5f5
```

### 引用计数流程

```mermaid
sequenceDiagram
    participant V as 值
    participant RC1 as Rc1
    participant RC2 as Rc2
    participant RC3 as Rc3
    participant Heap as 堆内存
    
    Note over V,Heap: 创建Rc
    V->>Heap: 分配内存
    Heap->>RC1: 创建Rc<br/>count=1
    
    Note over V,Heap: 克隆Rc
    RC1->>RC2: clone()
    RC2->>Heap: 增加引用计数<br/>count=2
    
    RC1->>RC3: clone()
    RC3->>Heap: 增加引用计数<br/>count=3
    
    Note over V,Heap: 离开作用域
    RC1->>Heap: drop<br/>count=2
    RC2->>Heap: drop<br/>count=1
    
    Note over V,Heap: 最后一个Rc离开
    RC3->>Heap: drop<br/>count=0
    Heap->>Heap: 释放内存
```

---

## 6. 内存布局可视化

### 栈与堆内存布局

```mermaid
graph TB
    subgraph Stack [栈内存]
        direction TB
        SF1[栈帧1: main]
        SF2[栈帧2: foo]
        SF3[栈帧3: bar]
        
        subgraph SF1_Detail [main栈帧]
            V1[x: i32 = 10]
            V2[y: &i32 = &x]
            V3[s: String<br/>ptr,len,cap]
        end
        
        subgraph SF2_Detail [foo栈帧]
            V4[a: i32 = 20]
            V5[b: Box&lt;i32&gt;<br/>pointer]
        end
    end
    
    subgraph Heap [堆内存]
        direction TB
        H1[String数据:<br/>'hello']
        H2[Box数据:<br/>i32 = 30]
        H3[Vec数据:<br/>[1,2,3,4]]
    end
    
    V3 -->|ptr| H1
    V5 -->|ptr| H2
    
    style Stack fill:#e3f2fd
    style Heap fill:#fff3e0
    style V3 fill:#bbdefb
    style V5 fill:#bbdefb
```

### 内存分配流程

```mermaid
flowchart TD
    Start[需要内存] --> Type{类型检查}
    
    Type -->|固定大小| StackCheck{栈空间足够?}
    Type -->|动态大小| Heap
    
    StackCheck -->|是| StackAlloc[栈分配]
    StackCheck -->|否| StackOverflow[栈溢出]
    
    StackAlloc --> Fast[快速分配<br/>移动栈指针]
    Fast --> AutoFree[作用域结束<br/>自动释放]
    
    Heap --> Allocator[调用分配器]
    Allocator --> Search[搜索空闲块]
    Search --> Found{找到?}
    
    Found -->|是| HeapAlloc[堆分配]
    Found -->|否| OOM[内存不足]
    
    HeapAlloc --> Manual[手动管理<br/>通过所有权]
    Manual --> Drop[Drop trait<br/>释放内存]
    
    AutoFree --> End[完成]
    Drop --> End
    StackOverflow --> Error[错误]
    OOM --> Error
    
    style Fast fill:#c8e6c9
    style AutoFree fill:#c8e6c9
    style Error fill:#ffcdd2
```

---

## 7. 并发所有权模型

### Send与Sync架构

```mermaid
graph TB
    subgraph Traits [标记trait]
        Send[Send trait<br/>可跨线程转移所有权]
        Sync[Sync trait<br/>可跨线程共享引用]
    end
    
    subgraph SendTypes [实现Send的类型]
        ST1[原始类型<br/>i32, f64等]
        ST2[String, Vec等]
        ST3[Box&lt;T: Send&gt;]
        ST4[Arc&lt;T: Send + Sync&gt;]
        ST5[Mutex&lt;T: Send&gt;]
    end
    
    subgraph SyncTypes [实现Sync的类型]
        SYT1[&T where T: Sync]
        SYT2[Arc&lt;T: Sync&gt;]
        SYT3[Mutex&lt;T&gt;]
        SYT4[RwLock&lt;T&gt;]
        SYT5[原子类型]
    end
    
    subgraph NonSend [不实现Send]
        NST1[Rc&lt;T&gt;<br/>非原子引用计数]
        NST2[原始指针<br/>*const T, *mut T]
        NST3[Cell&lt;T&gt;]
        NST4[RefCell&lt;T&gt;]
    end
    
    Send --> SendTypes
    Sync --> SyncTypes
    
    Send -.->|排除| NonSend
    
    style Traits fill:#e3f2fd
    style SendTypes fill:#c8e6c9
    style SyncTypes fill:#bbdefb
    style NonSend fill:#ffcdd2
```

### 线程安全决策流程

```mermaid
flowchart TD
    Start[需要跨线程] --> Own{转移所有权?}
    
    Own -->|是| SendCheck{实现Send?}
    Own -->|否| Share{共享数据?}
    
    SendCheck -->|是| Move[直接move到线程]
    SendCheck -->|否| Clone[克隆数据<br/>如果可以]
    
    Share -->|是| Multi{多个所有者?}
    Share -->|否| Borrow[使用引用<br/>需要生命周期]
    
    Multi -->|是| Mutable{需要修改?}
    Multi -->|否| ArcImmut[Arc&lt;T&gt;<br/>只读共享]
    
    Mutable -->|是| Lock{锁类型?}
    Mutable -->|否| ArcImmut
    
    Lock -->|互斥| ArcMutex[Arc&lt;Mutex&lt;T&gt;&gt;<br/>独占访问]
    Lock -->|读写分离| ArcRwLock[Arc&lt;RwLock&lt;T&gt;&gt;<br/>多读单写]
    Lock -->|无锁| Atomic[Atomic*<br/>原子操作]
    
    Move --> End[完成]
    Clone --> End
    Borrow --> End
    ArcImmut --> End
    ArcMutex --> End
    ArcRwLock --> End
    Atomic --> End
    
    style Start fill:#e3f2fd
    style ArcImmut fill:#c8e6c9
    style ArcMutex fill:#fff3e0
    style ArcRwLock fill:#bbdefb
    style Atomic fill:#f3e5f5
```

---

## 相关文档

- [知识图谱](./KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)
- [多维矩阵](./MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)
- [所有权理论](../01_theory/)
- [核心概念](../02_core/)
- [FAQ](../FAQ.md)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust-lang项目组

---

## 返回导航

- [返回主索引](../00_MASTER_INDEX.md)
- [返回README](../README.md)
- [查看实践指南](../05_practice/)
