# C08 算法 思维导图与可视化

> **文档定位**: Rust 1.90 算法与数据结构可视化学习  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **文档类型**: 思维导图 + 流程图 + 算法可视化

---

## 📊 目录

- [C08 算法 思维导图与可视化](#c08-算法-思维导图与可视化)
  - [📊 目录](#-目录)
  - [1. 算法全景思维导图](#1-算法全景思维导图)
    - [算法分类总览](#算法分类总览)
  - [2. 排序算法可视化](#2-排序算法可视化)
    - [快速排序流程](#快速排序流程)
    - [归并排序过程](#归并排序过程)
  - [3. 搜索算法可视化](#3-搜索算法可视化)
    - [二分搜索流程](#二分搜索流程)
    - [深度优先搜索](#深度优先搜索)
  - [4. 图算法可视化](#4-图算法可视化)
    - [Dijkstra最短路径](#dijkstra最短路径)
    - [最小生成树](#最小生成树)
  - [5. 动态规划可视化](#5-动态规划可视化)
    - [背包问题决策树](#背包问题决策树)
    - [最长公共子序列](#最长公共子序列)
  - [6. 数据结构演化](#6-数据结构演化)
    - [树结构演化](#树结构演化)
  - [7. 复杂度分析可视化](#7-复杂度分析可视化)
    - [时间复杂度对比](#时间复杂度对比)
  - [相关文档](#相关文档)
  - [返回导航](#返回导航)

---

## 1. 算法全景思维导图

### 算法分类总览

```mermaid
mindmap
  root((算法与数据结构))
    排序算法
      比较排序
        快速排序 O(n log n)
        归并排序 O(n log n)
        堆排序 O(n log n)
      非比较排序
        计数排序 O(n+k)
        桶排序 O(n+k)
        基数排序 O(d(n+k))
    搜索算法
      线性搜索
        顺序查找 O(n)
        哨兵查找
      二分搜索
        标准二分 O(log n)
        插值查找
        指数查找
      树搜索
        BST O(log n)
        AVL O(log n)
        红黑树 O(log n)
    图算法
      最短路径
        Dijkstra 单源
        Bellman-Ford 负权
        Floyd-Warshall 全源
      最小生成树
        Kruskal 边排序
        Prim 顶点优先
      拓扑排序
        Kahn算法
        DFS算法
    动态规划
      线性DP
        最长递增子序列
        最大子数组和
        编辑距离
      区间DP
        矩阵链乘法
        石子合并
      树形DP
        树的直径
        树的重心
      状态压缩DP
        TSP旅行商
        集合覆盖
    数据结构
      线性结构
        数组 连续存储
        链表 链式存储
        栈 LIFO
        队列 FIFO
      树结构
        二叉树
        B树/B+树
        字典树 Trie
        线段树
      图结构
        邻接表
        邻接矩阵
        稀疏图
      高级结构
        并查集 Union-Find
        跳表 SkipList
        布隆过滤器
```

---

## 2. 排序算法可视化

### 快速排序流程

```mermaid
flowchart TD
    Start[开始: 数组] --> Check{数组长度 ≤ 1?}
    Check -->|是| Return[返回数组]
    Check -->|否| SelectPivot[选择基准pivot]
    
    SelectPivot --> Partition[分区操作]
    Partition --> Less[左分区 < pivot]
    Partition --> Equal[中间 = pivot]
    Partition --> Greater[右分区 > pivot]
    
    Less --> RecurseLeft[递归排序左分区]
    Greater --> RecurseRight[递归排序右分区]
    
    RecurseLeft --> Merge1[合并]
    Equal --> Merge1
    RecurseRight --> Merge2[合并]
    Merge1 --> Merge2
    
    Merge2 --> Result[有序数组]
    Return --> End[结束]
    Result --> End
    
    style Start fill:#e3f2fd
    style Partition fill:#fff3e0
    style Result fill:#c8e6c9
    style End fill:#f3e5f5
```

### 归并排序过程

```mermaid
graph TB
    subgraph 分治阶段
        A[原数组: 38,27,43,3,9,82,10]
        A --> B1[38,27,43,3]
        A --> B2[9,82,10]
        
        B1 --> C1[38,27]
        B1 --> C2[43,3]
        B2 --> C3[9,82]
        B2 --> C4[10]
        
        C1 --> D1[38]
        C1 --> D2[27]
        C2 --> D3[43]
        C2 --> D4[3]
        C3 --> D5[9]
        C3 --> D6[82]
    end
    
    subgraph 合并阶段
        D1 --> E1[27,38]
        D2 --> E1
        D3 --> E2[3,43]
        D4 --> E2
        D5 --> E3[9,82]
        D6 --> E3
        C4 --> E4[10]
        
        E1 --> F1[3,27,38,43]
        E2 --> F1
        E3 --> F2[9,10,82]
        E4 --> F2
        
        F1 --> G[3,9,10,27,38,43,82]
        F2 --> G
    end
    
    style A fill:#ffccbc
    style G fill:#c8e6c9
```

---

## 3. 搜索算法可视化

### 二分搜索流程

```mermaid
sequenceDiagram
    participant U as 用户
    participant A as 算法
    participant D as 有序数组
    
    Note over D: [1,3,5,7,9,11,13,15,17,19]
    
    U->>A: 查找目标: 13
    A->>D: 初始化 left=0, right=9
    
    loop 二分查找
        A->>A: mid = (left + right) / 2 = 4
        A->>D: array[4] = 9
        A->>A: 9 < 13, left = mid + 1 = 5
        
        A->>A: mid = (5 + 9) / 2 = 7
        A->>D: array[7] = 15
        A->>A: 15 > 13, right = mid - 1 = 6
        
        A->>A: mid = (5 + 6) / 2 = 5
        A->>D: array[5] = 11
        A->>A: 11 < 13, left = mid + 1 = 6
        
        A->>A: mid = (6 + 6) / 2 = 6
        A->>D: array[6] = 13
        A->>A: 找到! 返回索引 6
    end
    
    A->>U: 结果: 索引 6
```

### 深度优先搜索

```mermaid
graph TB
    Start[起点: A] --> A
    A --> B
    A --> C
    B --> D
    B --> E
    C --> F
    C --> G
    E --> H
    E --> I
    
    style A fill:#ffccbc,stroke:#333,stroke-width:4px
    style B fill:#ffccbc,stroke:#333,stroke-width:4px
    style D fill:#ffccbc,stroke:#333,stroke-width:4px
    style E fill:#ffccbc,stroke:#333,stroke-width:4px
    style H fill:#ffccbc,stroke:#333,stroke-width:4px
    style I fill:#ffccbc,stroke:#333,stroke-width:4px
    style C fill:#e1bee7
    style F fill:#e1bee7
    style G fill:#e1bee7
    
    note1[访问顺序: A→B→D→E→H→I→C→F→G]
```

---

## 4. 图算法可视化

### Dijkstra最短路径

```mermaid
graph LR
    A((A<br/>0)) -->|4| B((B<br/>4))
    A -->|2| C((C<br/>2))
    B -->|5| D((D<br/>9))
    B -->|10| E((E<br/>14))
    C -->|3| B
    C -->|8| E
    C -->|2| D
    D -->|6| E
    
    style A fill:#c8e6c9,stroke:#2e7d32,stroke-width:4px
    style C fill:#fff9c4,stroke:#f57f17,stroke-width:3px
    style D fill:#fff9c4,stroke:#f57f17,stroke-width:3px
    style B fill:#fff9c4,stroke:#f57f17,stroke-width:3px
    style E fill:#ffccbc,stroke:#d84315,stroke-width:2px
    
    note1[绿色:起点 黄色:已确定 橙色:待处理]
```

### 最小生成树

```mermaid
graph TB
    subgraph Kruskal算法过程
        direction LR
        
        subgraph 原图
            A1((A)) ---|1| B1((B))
            A1 ---|4| C1((C))
            B1 ---|2| C1
            B1 ---|5| D1((D))
            C1 ---|3| D1
            D1 ---|6| E1((E))
            C1 ---|7| E1
        end
        
        subgraph 最小生成树
            A2((A)) ===|1| B2((B))
            B2 ===|2| C2((C))
            C2 ===|3| D2((D))
            D2 ===|6| E2((E))
        end
    end
    
    style A2 fill:#c8e6c9
    style B2 fill:#c8e6c9
    style C2 fill:#c8e6c9
    style D2 fill:#c8e6c9
    style E2 fill:#c8e6c9
    
    note2[总权重: 1+2+3+6=12]
```

---

## 5. 动态规划可视化

### 背包问题决策树

```mermaid
graph TD
    Root[物品1: 重量2,价值3]
    Root -->|选择| A1[容量-2, 价值+3]
    Root -->|不选| A2[容量不变, 价值不变]
    
    A1 -->|物品2| B1[选择: w-5,v+7]
    A1 -->|物品2| B2[不选]
    A2 -->|物品2| B3[选择: w-3,v+4]
    A2 -->|物品2| B4[不选]
    
    B1 --> C1[物品3...]
    B2 --> C2[物品3...]
    B3 --> C3[物品3...]
    B4 --> C4[物品3...]
    
    style Root fill:#e3f2fd
    style A1 fill:#fff3e0
    style B1 fill:#c8e6c9
    style B3 fill:#c8e6c9
```

### 最长公共子序列

```mermaid
graph TB
    subgraph DP表格
        direction TB
        T0["<br/>  A B C D E"]
        T1["A 1 1 1 1 1"]
        T2["C 1 1 2 2 2"]
        T3["E 1 1 2 2 3"]
        T4["<br/>LCS长度: 3"]
    end
    
    subgraph 回溯路径
        direction LR
        P1[A] --> P2[C] --> P3[E]
    end
    
    style T0 fill:#e3f2fd
    style T4 fill:#c8e6c9
    style P1 fill:#fff3e0
    style P2 fill:#fff3e0
    style P3 fill:#fff3e0
```

---

## 6. 数据结构演化

### 树结构演化

```mermaid
timeline
    title 树结构发展历程
    
    1960s : 二叉搜索树 BST
          : 基础树结构
    
    1962 : AVL树
         : 自平衡二叉树
         : 高度平衡
    
    1972 : B树
         : 多路搜索树
         : 磁盘友好
    
    1978 : 红黑树
         : 弱平衡
         : 高效插入
    
    1990s : 跳表
          : 概率平衡
          : 易实现
    
    2000s : Rust集合
          : BTreeMap
          : HashMap
          : 内存安全
```

---

## 7. 复杂度分析可视化

### 时间复杂度对比

```mermaid
%%{init: {'theme':'base'}}%%
graph LR
    subgraph "常见复杂度增长"
        O1[O(1)<br/>常数]
        OlogN[O(log n)<br/>对数]
        ON[O(n)<br/>线性]
        ONlogN[O(n log n)<br/>线性对数]
        ON2[O(n²)<br/>平方]
        ON3[O(n³)<br/>立方]
        O2N[O(2ⁿ)<br/>指数]
    end
    
    O1 --> OlogN
    OlogN --> ON
    ON --> ONlogN
    ONlogN --> ON2
    ON2 --> ON3
    ON3 --> O2N
    
    style O1 fill:#c8e6c9
    style OlogN fill:#c8e6c9
    style ON fill:#fff9c4
    style ONlogN fill:#fff9c4
    style ON2 fill:#ffccbc
    style ON3 fill:#ffccbc
    style O2N fill:#ef9a9a
```

**复杂度实例对比**:

```mermaid
quadrantChart
    title 算法复杂度分布
    x-axis 输入规模小 --> 输入规模大
    y-axis 时间短 --> 时间长
    
    quadrant-1 可接受区
    quadrant-2 需优化
    quadrant-3 优秀
    quadrant-4 理想
    
    二分搜索: [0.85, 0.15]
    快速排序: [0.7, 0.35]
    归并排序: [0.65, 0.4]
    堆排序: [0.6, 0.45]
    
    哈希查找: [0.9, 0.1]
    AVL树: [0.75, 0.25]
    
    冒泡排序: [0.3, 0.75]
    选择排序: [0.25, 0.8]
    插入排序: [0.4, 0.7]
    
    线性搜索: [0.5, 0.5]
```

---

## 相关文档

- [知识图谱](./KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)
- [多维对比](./MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)
- [算法指南](../guides/)
- [FAQ](../FAQ.md)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust-lang项目组

---

## 返回导航

- [返回主索引](../00_MASTER_INDEX.md)
- [返回README](../README.md)
- [查看理论文档](../theory/)
