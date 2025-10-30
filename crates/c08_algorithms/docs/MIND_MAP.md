# 算法学习思维导图 (Algorithm Learning Mind Map)

## 📊 目录

- [算法学习思维导图 (Algorithm Learning Mind Map)](#算法学习思维导图-algorithm-learning-mind-map)
  - [📊 目录](#-目录)
  - [🧠 总体知识架构思维导图](#-总体知识架构思维导图)
  - [📚 排序算法思维导图](#-排序算法思维导图)
  - [🌲 图算法思维导图](#-图算法思维导图)
  - [💡 动态规划思维导图](#-动态规划思维导图)
  - [🔤 字符串算法思维导图](#-字符串算法思维导图)
  - [🚀 学习路径思维导图](#-学习路径思维导图)
  - [🎯 问题分类思维导图](#-问题分类思维导图)
  - [🔧 Rust 特性应用思维导图](#-rust-特性应用思维导图)
  - [📊 复杂度分析思维导图](#-复杂度分析思维导图)
  - [🎓 核心概念关联图](#-核心概念关联图)
  - [📱 实战应用场景思维导图](#-实战应用场景思维导图)
  - [🏆 竞赛编程思维导图](#-竞赛编程思维导图)
  - [📚 参考资源](#-参考资源)

**版本**: 1.0.0
**Rust版本**: 1.90.0
**创建日期**: 2025年10月19日
**特性**: 思维导图 + 学习路径 + 知识关联

---

## 🧠 总体知识架构思维导图

```mermaid
mindmap
  root((算法与<br/>数据结构))
    基础概念
      复杂度分析
        时间复杂度
        空间复杂度
        Big-O 记号
        主定理
      算法设计范式
        分治法
        动态规划
        贪心算法
        回溯算法
        分支限界
      正确性证明
        循环不变式
        数学归纳法
        反证法

    数据结构
      线性结构
        数组
        链表
        栈
        队列
        双端队列
      树形结构
        二叉树
        二叉搜索树
        AVL 树
        红黑树
        B 树
        堆
        字典树
      图结构
        邻接表
        邻接矩阵
        边集数组
      高级结构
        并查集
        线段树
        树状数组
        跳表
        布隆过滤器

    算法分类
      排序算法
        比较排序
          冒泡排序
          选择排序
          插入排序
          归并排序
          快速排序
          堆排序
        非比较排序
          计数排序
          基数排序
          桶排序
      搜索算法
        线性搜索
        二分搜索
        深度优先搜索
        广度优先搜索
        A* 搜索
      图算法
        最短路径
          Dijkstra
          Bellman-Ford
          Floyd-Warshall
          SPFA
        最小生成树
          Kruskal
          Prim
        拓扑排序
        强连通分量
        网络流
      字符串算法
        KMP
        Boyer-Moore
        Rabin-Karp
        Aho-Corasick
        后缀数组
      动态规划
        线性 DP
        背包 DP
        区间 DP
        树形 DP
        状态压缩 DP
      数学算法
        数论
        组合数学
        概率论
        线性代数

    Rust 1.90 特性
      类型系统
        泛型
        Trait
        生命周期
        const 泛型
      并发编程
        线程
        同步原语
        rayon 并行
        Arc & Mutex
      异步编程
        async/await
        Future
        async fn in trait
        tokio 运行时
      性能优化
        零成本抽象
        SIMD
        内联优化
        内存对齐
```

---

## 📚 排序算法思维导图

```mermaid
mindmap
  root((排序算法))
    比较排序 O-n_log_n
      归并排序
        分治思想
        稳定排序
        空间 O-n
        适合链表
        Rust 实现
          递归版本
          迭代版本
          并行版本 rayon
          异步版本 async
      快速排序
        分治思想
        不稳定
        空间 O-log_n
        原地排序
        优化技巧
          三路划分
          随机pivot
          小数组插入排序
          尾递归优化
        Rust 实现
          标准版本
          并行版本 rayon
          三路快排
      堆排序
        堆数据结构
        不稳定
        空间 O-1
        优先队列应用
        Rust 实现
          BinaryHeap
          手动堆化

    比较排序 O-n²
      冒泡排序
        相邻交换
        稳定排序
        优化: 提前终止
      选择排序
        最值选择
        不稳定
        交换次数少
      插入排序
        构建有序序列
        稳定排序
        适合小数据
        适合近似有序

    非比较排序
      计数排序
        时间 O-n+k
        空间 O-k
        稳定排序
        适合整数小范围
      基数排序
        时间 O-d×-n+k
        多关键字排序
        稳定排序
        适合整数/字符串
      桶排序
        时间 O-n+k
        分桶处理
        适合均匀分布
        可并行化

    Rust 特性应用
      泛型约束
        Ord trait
        Clone trait
        Send + Sync
      并行化
        rayon::par_sort
        rayon::join
        分治并行
      异步化
        async fn in trait
        tokio::spawn
        异步 IO 排序
      性能优化
        内联优化
        避免拷贝
        切片操作
        unstable_sort
```

---

## 🌲 图算法思维导图

```mermaid
mindmap
  root((图算法))
    图的表示
      邻接矩阵
        适合稠密图
        空间 O-V²
        查询边 O-1
      邻接表
        适合稀疏图
        空间 O-V+E
        遍历邻居快
      边集数组
        简单实现
        适合Kruskal

    图的遍历
      深度优先搜索 DFS
        栈/递归实现
        时间 O-V+E
        应用场景
          拓扑排序
          连通性判定
          强连通分量
          环检测
        Rust 实现
          递归版本
          迭代版本
          并行DFS
      广度优先搜索 BFS
        队列实现
        时间 O-V+E
        应用场景
          最短路径 无权
          层次遍历
          二分图判定
        Rust 实现
          标准版本
          并行BFS
          异步BFS

    最短路径
      单源最短路径
        Dijkstra
          非负权图
          优先队列
          O-E+V_log_V
          Rust实现
            BinaryHeap
            async版本
        Bellman-Ford
          支持负权
          边松弛
          O-VE
          负环检测
        SPFA
          队列优化
          平均O-kE
          最坏O-VE
      全源最短路径
        Floyd-Warshall
          动态规划
          O-V³
          支持负权
          可并行化
      启发式搜索
        A* 算法
          启发函数
          优先队列
          游戏寻路

    最小生成树
      Kruskal 算法
        边排序
        并查集
        O-E_log_E
        适合稀疏图
        Rust实现
          sort + UnionFind
          并行排序
      Prim 算法
        点扩展
        优先队列
        O-E+V_log_V
        适合稠密图

    高级算法
      拓扑排序
        Kahn 算法
        DFS 后序
        DAG 判定
      强连通分量
        Tarjan 算法
        Kosaraju 算法
        时间戳
      网络流
        最大流
          Ford-Fulkerson
          Edmonds-Karp
          Dinic
        最小割
        二分图匹配

    Rust 特性
      泛型图
        HashMap 表示
        trait 抽象
      并行化
        并行BFS
        并行Bellman-Ford
        并行Floyd
      异步化
        async trait
        网络图加载
        分布式图算法
```

---

## 💡 动态规划思维导图

```mermaid
mindmap
  root((动态规划))
    核心思想
      最优子结构
      重叠子问题
      状态定义
      状态转移方程
      边界条件

    解题步骤
      1. 定义状态
      2. 找转移方程
      3. 初始化
      4. 填表顺序
      5. 返回结果
      6. 优化 空间/时间

    线性 DP
      最长递增子序列 LIS
        定义 dp[i]
        O-n² → O-n_log_n
        二分优化
      最长公共子序列 LCS
        二维 DP
        滚动数组优化
        O-mn
      编辑距离
        三种操作
        O-mn
        空间优化
      最大子数组和
        Kadane 算法
        O-n
        分治法

    背包问题
      0-1 背包
        物品不可重复
        倒序遍历
        空间 O-W
      完全背包
        物品可重复
        正序遍历
        空间 O-W
      多重背包
        数量限制
        二进制优化
      分组背包
        分组约束
        组内互斥

    区间 DP
      矩阵链乘
        区间枚举
        O-n³
      石子合并
        环形变链
        四边形优化
      括号匹配
        合法性判定

    树形 DP
      树的直径
        两次DFS
        树形DP
      树形背包
        子树合并
        O-nW
      树上最大独立集
        递归定义

    状态压缩 DP
      旅行商问题 TSP
        状态mask
        O-n²2ⁿ
      子集和
        位运算
        O-2ⁿ
      棋盘覆盖
        轮廓线DP

    优化技巧
      空间优化
        滚动数组
        一维DP
      时间优化
        单调队列
        斜率优化
        四边形不等式
        矩阵快速幂
      记忆化搜索
        Top-down
        递归+缓存

    Rust 实现
      数组DP
        Vec<Vec<T>>
        滚动数组 swap
      HashMap DP
        状态哈希
      并行DP
        分块并行
        rayon
      异步DP
        大规模数据
        spawn_blocking
```

---

## 🔤 字符串算法思维导图

```mermaid
mindmap
  root((字符串算法))
    基础概念
      前缀
      后缀
      子串
      子序列
      周期性
      边界数组

    单模式匹配
      朴素匹配
        双指针
        O-mn
        简单直接
      KMP 算法
        next 数组
        失配跳转
        O-m+n
        Rust实现
          next 构建
          匹配过程
          优化版本
      Boyer-Moore
        坏字符规则
        好后缀规则
        O-n/m 平均
        大字符集优势
      Rabin-Karp
        滚动哈希
        多模式扩展
        O-m+n 平均
        哈希冲突

    多模式匹配
      Aho-Corasick
        Trie 树
        失配指针
        O-n+m+z
        应用场景
          关键词过滤
          病毒扫描
          日志分析
        Rust实现
          build_trie
          build_fail
          search
      后缀自动机
        O-n 构建
        强大功能
        状态转移

    后缀结构
      后缀数组
        倍增算法
        DC3 算法
        O-n_log_n
        应用
          最长公共子串
          重复子串
          字典序第k小
      后缀树
        Ukkonen 算法
        O-n 构建
        O-m 查询
        功能最强
      后缀自动机
        在线构建
        O-n 时空

    字符串DP
      最长回文子串
        中心扩展
        Manacher
        O-n
      最长回文子序列
        区间DP
        O-n²
      正则匹配
        状态机
        回溯

    高级技巧
      字符串哈希
        单哈希
        双哈希
        滚动哈希
      Z 算法
        Z 数组
        O-n
      Manacher
        回文串
        O-n
      最小表示法
        字符串旋转
        O-n

    Rust 特性
      &str vs String
      字节操作
        as_bytes
        from_utf8
      迭代器
        chars
        bytes
        char_indices
      SIMD 优化
        批量比较
        std::simd
      并行匹配
        rayon
        多文本并行
```

---

## 🚀 学习路径思维导图

```mermaid
mindmap
  root((学习路径))
    第一阶段: 基础 1-2周
      基本概念
        算法定义
        复杂度分析
        Big-O 记号
      基础数据结构
        数组
        链表
        栈
        队列
      简单算法
        线性搜索
        二分搜索
        冒泡排序
        插入排序
      Rust 基础
        所有权
        借用
        生命周期
        Vec 和切片

    第二阶段: 进阶 2-3周
      高级数据结构
        树
        堆
        哈希表
        图
      排序算法
        归并排序
        快速排序
        堆排序
      图算法基础
        DFS
        BFS
        最短路径
      Rust 进阶
        泛型
        Trait
        迭代器
        错误处理

    第三阶段: 高级 3-4周
      动态规划
        线性DP
        背包问题
        区间DP
      字符串算法
        KMP
        Trie
        后缀数组
      高级图算法
        最小生成树
        网络流
        拓扑排序
      Rust 高级
        智能指针
        并发编程
        unsafe
        宏

    第四阶段: 专家 持续
      算法优化
        时间优化
        空间优化
        并行化
        分布式
      理论研究
        计算复杂度
        NP 完全
        近似算法
        随机算法
      Rust 专家
        异步编程
        tokio
        rayon
        性能调优
        SIMD
      实际应用
        竞赛编程
        工程实践
        系统设计
```

---

## 🎯 问题分类思维导图

```mermaid
mindmap
  root((算法问题))
    按数据结构
      数组问题
        双指针
        滑动窗口
        前缀和
        差分数组
      链表问题
        快慢指针
        反转链表
        环检测
      树问题
        遍历
        路径问题
        LCA
        树形DP
      图问题
        遍历
        最短路径
        连通性
        拓扑排序

    按算法范式
      分治法
        归并排序
        快速排序
        最大子数组
        最近点对
      动态规划
        最优化问题
        计数问题
        存在性问题
      贪心算法
        活动选择
        霍夫曼编码
        区间调度
      回溯算法
        排列组合
        N皇后
        数独

    按问题类型
      搜索问题
        DFS
        BFS
        二分搜索
        A*
      优化问题
        动态规划
        贪心
        线性规划
      计数问题
        组合数学
        DP
        容斥原理
      字符串问题
        模式匹配
        编辑距离
        回文串

    按难度
      Easy
        双指针
        简单DP
        基础图论
      Medium
        复杂DP
        图算法
        字符串
      Hard
        高级DP
        网络流
        计算几何
```

---

## 🔧 Rust 特性应用思维导图

```mermaid
mindmap
  root((Rust 1.90<br/>算法应用))
    类型系统
      泛型算法
        trait 约束
          Ord
          Clone
          PartialEq
        const 泛型
          数组大小
          编译期优化
      生命周期
        借用检查
        避免拷贝
        零成本抽象

    所有权系统
      移动语义
        避免深拷贝
        高效传递
      借用
        不可变借用
        可变借用
        迭代器
      切片
        数组视图
        零拷贝

    并发编程
      线程
        std::thread
        数据竞争安全
      rayon 并行
        par_iter
        par_sort
        join
        并行算法
      同步原语
        Mutex
        Arc
        RwLock
        Atomic

    异步编程
      async/await
        Future
        async fn in trait
        异步算法
      tokio
        spawn
        spawn_blocking
        async I/O
      异步图算法
        异步最短路径
        异步遍历

    性能优化
      零成本抽象
        迭代器
        闭包内联
        泛型单态化
      SIMD
        并行数据处理
        字符串匹配
      内存优化
        栈分配
        内存对齐
        缓存友好
      编译优化
        内联
        LTO
        PGO

    错误处理
      Result类型
      Option类型
      ? 操作符
      自定义错误

    测试与基准
      单元测试
      属性测试
      基准测试
        criterion
        black_box
```

---

## 📊 复杂度分析思维导图

```mermaid
mindmap
  root((复杂度分析))
    时间复杂度
      常见复杂度
        O-1 常数
        O-log_n 对数
        O-n 线性
        O-n_log_n 线性对数
        O-n² 平方
        O-n³ 立方
        O-2ⁿ 指数
        O-n! 阶乘
      分析方法
        最好情况
        平均情况
        最坏情况
        均摊分析
      优化策略
        减少循环层数
        空间换时间
        预处理
        剪枝

    空间复杂度
      内存使用
        输入空间
        辅助空间
        递归栈
      优化技术
        原地算法
        滚动数组
        位运算
        常数空间

    渐近记号
      O-大O
        上界
        最坏情况
      Ω-大Omega
        下界
        最好情况
      Θ-大Theta
        紧确界
        精确界
      o-小o
        非紧上界
      ω-小omega
        非紧下界

    主定理
      T-n=aT-n/b+f-n
      三种情况
        Case 1: f-n=O-n^c, c<log_b_a
        Case 2: f-n=Θ-n^c, c=log_b_a
        Case 3: f-n=Ω-n^c, c>log_b_a
      应用
        归并排序
        快速排序
        二分搜索

    分析技巧
      递归树方法
      代入法
      迭代法
      差分方程
      生成函数
```

---

## 🎓 核心概念关联图

```mermaid
mindmap
  root((核心概念))
    算法正确性
      循环不变式
        初始化
        保持
        终止
      数学归纳法
        基础步骤
        归纳步骤
      反证法
      构造性证明

    算法设计原则
      分而治之
        分解问题
        递归求解
        合并结果
      动态规划原则
        最优子结构
        重叠子问题
        无后效性
      贪心选择性质
        局部最优
        全局最优
        证明正确性

    数据结构特性
      抽象数据类型
        接口定义
        操作语义
      具体实现
        数组实现
        链表实现
        树实现
      性能权衡
        时间-空间
        读-写
        简单-复杂

    问题求解策略
      暴力枚举
      分治法
      动态规划
      贪心法
      回溯法
      分支限界
      启发式搜索
      近似算法
      随机算法
```

---

## 📱 实战应用场景思维导图

```mermaid
mindmap
  root((实战应用))
    Web 开发
      路由匹配
        Trie树
        正则表达式
      缓存策略
        LRU
        LFU
      负载均衡
        一致性哈希
        加权轮询

    数据库
      索引结构
        B+树
        哈希索引
        位图索引
      查询优化
        连接算法
        排序合并
      事务管理
        MVCC
        2PL

    机器学习
      数据预处理
        归一化
        特征选择
      算法实现
        KNN
        决策树
        神经网络
      优化算法
        梯度下降
        Adam

    游戏开发
      寻路算法
        A*
        Dijkstra
      碰撞检测
        空间划分
        包围盒
      AI 算法
        状态机
        行为树
        MCTS

    系统设计
      分布式系统
        一致性算法
        Paxos
        Raft
      负载均衡
        哈希算法
        最小连接
      缓存系统
        淘汰策略
        一致性
```

---

## 🏆 竞赛编程思维导图

```mermaid
mindmap
  root((竞赛编程))
    基础算法
      排序
      搜索
      前缀和
      差分
      双指针
      滑动窗口

    数据结构
      并查集
      线段树
      树状数组
      平衡树
      堆
      单调栈/队列

    图论
      最短路
      最小生成树
      拓扑排序
      强连通分量
      二分图
      网络流

    动态规划
      线性DP
      背包DP
      区间DP
      树形DP
      状压DP
      数位DP

    数学
      数论
        质数
        GCD/LCM
        快速幂
        逆元
      组合数学
        排列组合
        容斥原理
        鸽巢原理
      概率期望

    字符串
      KMP
      字符串哈希
      Trie
      AC自动机
      后缀数组
      Manacher

    技巧
      二分答案
      贪心
      构造
      博弈论
      计算几何
```

---

## 📚 参考资源

- [VisuAlgo](https://visualgo.net/) - 算法可视化
- [LeetCode](https://leetcode.com/) - 算法练习
- [Codeforces](https://codeforces.com/) - 竞赛编程
- [OI Wiki](https://oi-wiki.org/) - 竞赛知识库

---

**最后更新**: 2025年10月19日
**文档版本**: 1.0.0
**维护者**: c08_algorithms 团队
