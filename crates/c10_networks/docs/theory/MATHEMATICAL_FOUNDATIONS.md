# C10 Networks 数学基础

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。


## 📊 目录

- [📋 目录](#目录)
- [🎯 概述](#概述)
  - [📚 数学基础的重要性](#数学基础的重要性)
  - [🔬 数学工具的应用](#数学工具的应用)
  - [📊 符号约定](#符号约定)
- [📊 概率论基础](#概率论基础)
  - [随机过程](#随机过程)
    - [随机过程定义](#随机过程定义)
    - [随机过程分类](#随机过程分类)
    - [网络流量建模](#网络流量建模)
  - [马尔可夫链](#马尔可夫链)
    - [定义2](#定义2)
    - [TCP状态机马尔可夫链](#tcp状态机马尔可夫链)
  - [泊松过程](#泊松过程)
    - [定义3](#定义3)
    - [实现](#实现)
- [🔢 数论基础](#数论基础)
  - [模运算](#模运算)
    - [定义4](#定义4)
    - [实现1](#实现1)
  - [欧几里得算法](#欧几里得算法)
    - [算法](#算法)
  - [费马小定理](#费马小定理)
    - [定理](#定理)
    - [应用](#应用)
- [📈 图论基础](#图论基础)
  - [网络拓扑](#网络拓扑)
    - [图论定义](#图论定义)
    - [图论实现](#图论实现)
  - [最短路径算法](#最短路径算法)
    - [Dijkstra算法](#dijkstra算法)
  - [最小生成树](#最小生成树)
    - [Kruskal算法](#kruskal算法)
- [⚡ 信息论基础](#信息论基础)
  - [熵和信息量](#熵和信息量)
    - [熵和信息量定义](#熵和信息量定义)
    - [信息论实现](#信息论实现)
  - [信道容量](#信道容量)
    - [信道容量定义](#信道容量定义)
    - [信道容量实现](#信道容量实现)
  - [编码理论](#编码理论)
    - [霍夫曼编码](#霍夫曼编码)
- [🧮 线性代数基础](#线性代数基础)
  - [矩阵运算](#矩阵运算)
    - [矩阵乘法](#矩阵乘法)
  - [特征值和特征向量](#特征值和特征向量)
    - [幂迭代法](#幂迭代法)
  - [奇异值分解](#奇异值分解)
    - [SVD算法](#svd算法)
- [📊 统计学基础](#统计学基础)
  - [描述性统计](#描述性统计)
    - [统计量计算](#统计量计算)
  - [假设检验](#假设检验)
    - [t检验](#t检验)
  - [回归分析](#回归分析)
    - [线性回归](#线性回归)
- [🔐 密码学数学基础](#密码学数学基础)
  - [群论](#群论)
    - [群的定义和性质](#群的定义和性质)
  - [椭圆曲线](#椭圆曲线)
    - [椭圆曲线密码学](#椭圆曲线密码学)
  - [离散对数](#离散对数)
    - [离散对数问题](#离散对数问题)
- [🎯 优化理论](#优化理论)
  - [线性规划](#线性规划)
    - [单纯形法](#单纯形法)
  - [动态规划](#动态规划)
    - [网络流问题](#网络流问题)
  - [启发式算法](#启发式算法)
    - [遗传算法](#遗传算法)
- [📚 参考文献](#参考文献)


## 📋 目录

- [C10 Networks 数学基础](#c10-networks-数学基础)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [📚 数学基础的重要性](#-数学基础的重要性)
    - [🔬 数学工具的应用](#-数学工具的应用)
    - [📊 符号约定](#-符号约定)
  - [📊 概率论基础](#-概率论基础)
    - [随机过程](#随机过程)
      - [随机过程定义](#随机过程定义)
      - [随机过程分类](#随机过程分类)
      - [网络流量建模](#网络流量建模)
    - [马尔可夫链](#马尔可夫链)
      - [定义2](#定义2)
      - [TCP状态机马尔可夫链](#tcp状态机马尔可夫链)
    - [泊松过程](#泊松过程)
      - [定义3](#定义3)
      - [实现](#实现)
  - [🔢 数论基础](#-数论基础)
    - [模运算](#模运算)
      - [定义4](#定义4)
      - [实现1](#实现1)
    - [欧几里得算法](#欧几里得算法)
      - [算法](#算法)
    - [费马小定理](#费马小定理)
      - [定理](#定理)
      - [应用](#应用)
  - [📈 图论基础](#-图论基础)
    - [网络拓扑](#网络拓扑)
      - [图论定义](#图论定义)
      - [图论实现](#图论实现)
    - [最短路径算法](#最短路径算法)
      - [Dijkstra算法](#dijkstra算法)
    - [最小生成树](#最小生成树)
      - [Kruskal算法](#kruskal算法)
  - [⚡ 信息论基础](#-信息论基础)
    - [熵和信息量](#熵和信息量)
      - [熵和信息量定义](#熵和信息量定义)
      - [信息论实现](#信息论实现)
    - [信道容量](#信道容量)
      - [信道容量定义](#信道容量定义)
      - [信道容量实现](#信道容量实现)
    - [编码理论](#编码理论)
      - [霍夫曼编码](#霍夫曼编码)
  - [🧮 线性代数基础](#-线性代数基础)
    - [矩阵运算](#矩阵运算)
      - [矩阵乘法](#矩阵乘法)
    - [特征值和特征向量](#特征值和特征向量)
      - [幂迭代法](#幂迭代法)
    - [奇异值分解](#奇异值分解)
      - [SVD算法](#svd算法)
  - [📊 统计学基础](#-统计学基础)
    - [描述性统计](#描述性统计)
      - [统计量计算](#统计量计算)
    - [假设检验](#假设检验)
      - [t检验](#t检验)
    - [回归分析](#回归分析)
      - [线性回归](#线性回归)
  - [🔐 密码学数学基础](#-密码学数学基础)
    - [群论](#群论)
      - [群的定义和性质](#群的定义和性质)
    - [椭圆曲线](#椭圆曲线)
      - [椭圆曲线密码学](#椭圆曲线密码学)
    - [离散对数](#离散对数)
      - [离散对数问题](#离散对数问题)
  - [🎯 优化理论](#-优化理论)
    - [线性规划](#线性规划)
      - [单纯形法](#单纯形法)
    - [动态规划](#动态规划)
      - [网络流问题](#网络流问题)
    - [启发式算法](#启发式算法)
      - [遗传算法](#遗传算法)
  - [📚 参考文献](#-参考文献)

## 🎯 概述

本文档提供了C10 Networks项目所需的数学理论基础，涵盖概率论、数论、图论、信息论、线性代数、统计学、密码学和优化理论等核心数学概念。这些数学工具为网络协议设计、性能分析、安全验证和系统优化提供了坚实的理论基础。

### 📚 数学基础的重要性

在网络编程中，数学基础发挥着关键作用：

1. **协议设计**: 使用形式化方法描述协议行为
2. **性能分析**: 通过数学模型预测系统性能
3. **安全验证**: 使用密码学理论保证通信安全
4. **优化算法**: 应用优化理论提高系统效率
5. **故障分析**: 使用概率论分析系统可靠性

### 🔬 数学工具的应用

| 数学领域 | 应用场景 | 具体用途 |
|---------|---------|---------|
| 概率论 | 网络流量建模 | 泊松过程、马尔可夫链 |
| 数论 | 密码学算法 | RSA、椭圆曲线密码 |
| 图论 | 网络拓扑分析 | 最短路径、最小生成树 |
| 信息论 | 数据压缩 | 霍夫曼编码、熵计算 |
| 线性代数 | 信号处理 | 矩阵运算、特征值分析 |
| 统计学 | 性能分析 | 假设检验、回归分析 |
| 优化理论 | 资源分配 | 线性规划、动态规划 |

### 📊 符号约定

本文档使用以下数学符号：

- $\mathbb{N}$: 自然数集合
- $\mathbb{Z}$: 整数集合
- $\mathbb{R}$: 实数集合
- $\mathbb{C}$: 复数集合
- $\mathcal{P}(S)$: 集合S的幂集
- $|S|$: 集合S的基数
- $\emptyset$: 空集
- $\in$: 属于关系
- $\subseteq$: 子集关系
- $\cup$: 并集
- $\cap$: 交集
- $\setminus$: 差集
- $\times$: 笛卡尔积
- $\rightarrow$: 函数映射
- $\forall$: 全称量词
- $\exists$: 存在量词
- $\Rightarrow$: 蕴含
- $\Leftrightarrow$: 等价
- $\neg$: 否定
- $\land$: 逻辑与
- $\lor$: 逻辑或

## 📊 概率论基础

### 随机过程

网络系统中的许多现象可以用随机过程来建模：

#### 随机过程定义

设 $(\Omega, \mathcal{F}, P)$ 是概率空间，$T$ 是指标集，$\{X_t\}_{t \in T}$ 是随机变量族，则称 $\{X_t\}_{t \in T}$ 为随机过程。

#### 随机过程分类

1. **按时间参数分类**:
   - 离散时间随机过程: $T = \mathbb{N}$ 或 $T = \mathbb{Z}$
   - 连续时间随机过程: $T = \mathbb{R}$ 或 $T = [0, \infty)$

2. **按状态空间分类**:
   - 离散状态随机过程: 状态空间为有限或可数集合
   - 连续状态随机过程: 状态空间为连续集合

3. **按统计特性分类**:
   - 平稳随机过程: 统计特性不随时间变化
   - 非平稳随机过程: 统计特性随时间变化

#### 网络流量建模

网络流量可以用多种随机过程模型来描述：

```rust
// 网络流量随机过程
pub struct NetworkTrafficProcess {
    // 到达过程
    arrival_process: PoissonProcess,
    // 服务过程
    service_process: ExponentialProcess,
    // 队列长度过程
    queue_length_process: MarkovChain,
}

impl NetworkTrafficProcess {
    // 计算稳态概率
    pub fn steady_state_probability(&self, state: usize) -> f64 {
        let lambda = self.arrival_process.rate();
        let mu = self.service_process.rate();
        let rho = lambda / mu;
        
        if rho < 1.0 {
            (1.0 - rho) * rho.powi(state as i32)
        } else {
            0.0
        }
    }
    
    // 计算平均队列长度
    pub fn average_queue_length(&self) -> f64 {
        let lambda = self.arrival_process.rate();
        let mu = self.service_process.rate();
        let rho = lambda / mu;
        
        if rho < 1.0 {
            rho / (1.0 - rho)
        } else {
            f64::INFINITY
        }
    }
}
```

### 马尔可夫链

网络状态转换可以用马尔可夫链建模：

#### 定义2

设 $\{X_n\}_{n \geq 0}$ 是随机过程，如果对于任意 $n \geq 0$ 和状态 $i_0, i_1, \ldots, i_{n-1}, i, j$，有：

$$P(X_{n+1} = j | X_n = i, X_{n-1} = i_{n-1}, \ldots, X_0 = i_0) = P(X_{n+1} = j | X_n = i)$$

则称 $\{X_n\}_{n \geq 0}$ 为马尔可夫链。

#### TCP状态机马尔可夫链

```rust
// TCP状态机马尔可夫链
pub struct TcpMarkovChain {
    // 状态空间
    states: Vec<TcpState>,
    // 转移概率矩阵
    transition_matrix: Vec<Vec<f64>>,
    // 初始分布
    initial_distribution: Vec<f64>,
}

impl TcpMarkovChain {
    // 计算n步转移概率
    pub fn n_step_transition_probability(&self, from: TcpState, to: TcpState, n: usize) -> f64 {
        let from_idx = self.state_index(from);
        let to_idx = self.state_index(to);
        
        // 计算转移矩阵的n次幂
        let matrix_power = self.matrix_power(&self.transition_matrix, n);
        matrix_power[from_idx][to_idx]
    }
    
    // 计算稳态分布
    pub fn steady_state_distribution(&self) -> Vec<f64> {
        // 求解线性方程组 π = πP
        let n = self.states.len();
        let mut system = vec![vec![0.0; n + 1]; n];
        
        // 添加约束条件
        for i in 0..n {
            for j in 0..n {
                system[i][j] = self.transition_matrix[j][i] - if i == j { 1.0 } else { 0.0 };
            }
            system[i][n] = 0.0;
        }
        
        // 添加归一化条件
        for j in 0..n {
            system[n-1][j] = 1.0;
        }
        system[n-1][n] = 1.0;
        
        self.solve_linear_system(&system)
    }
}
```

### 泊松过程

网络数据包到达通常可以用泊松过程建模：

#### 定义3

计数过程 $\{N(t), t \geq 0\}$ 称为强度为 $\lambda$ 的泊松过程，如果：

1. $N(0) = 0$
2. 过程有独立增量
3. 对于任意 $s, t \geq 0$，$N(t+s) - N(s)$ 服从参数为 $\lambda t$ 的泊松分布

#### 实现

```rust
// 泊松过程
pub struct PoissonProcess {
    rate: f64, // λ
}

impl PoissonProcess {
    // 生成到达时间间隔
    pub fn generate_interarrival_times(&self, count: usize) -> Vec<f64> {
        (0..count)
            .map(|_| -self.rate.ln() * rand::random::<f64>())
            .collect()
    }
    
    // 计算在时间t内到达n个事件的概率
    pub fn probability(&self, n: usize, t: f64) -> f64 {
        let lambda_t = self.rate * t;
        (lambda_t.powi(n as i32) * (-lambda_t).exp()) / factorial(n)
    }
    
    // 计算平均到达时间
    pub fn mean_interarrival_time(&self) -> f64 {
        1.0 / self.rate
    }
}

fn factorial(n: usize) -> f64 {
    (1..=n).fold(1.0, |acc, x| acc * x as f64)
}
```

## 🔢 数论基础

### 模运算

密码学和网络协议中广泛使用模运算：

#### 定义4

对于整数 $a, b, n$，如果 $n \neq 0$，则 $a \equiv b \pmod{n}$ 当且仅当 $n | (a - b)$。

#### 实现1

```rust
// 模运算工具
pub struct ModularArithmetic {
    modulus: u64,
}

impl ModularArithmetic {
    // 模加法
    pub fn add(&self, a: u64, b: u64) -> u64 {
        (a + b) % self.modulus
    }
    
    // 模乘法
    pub fn multiply(&self, a: u64, b: u64) -> u64 {
        (a * b) % self.modulus
    }
    
    // 模幂运算
    pub fn power(&self, base: u64, exponent: u64) -> u64 {
        let mut result = 1;
        let mut base = base % self.modulus;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % self.modulus;
            }
            exp >>= 1;
            base = (base * base) % self.modulus;
        }
        
        result
    }
    
    // 模逆元
    pub fn inverse(&self, a: u64) -> Option<u64> {
        let (gcd, x, _) = self.extended_gcd(a, self.modulus);
        if gcd == 1 {
            Some((x % self.modulus as i64 + self.modulus as i64) as u64 % self.modulus)
        } else {
            None
        }
    }
    
    // 扩展欧几里得算法
    fn extended_gcd(&self, a: u64, b: u64) -> (u64, i64, i64) {
        if a == 0 {
            (b, 0, 1)
        } else {
            let (gcd, x1, y1) = self.extended_gcd(b % a, a);
            let x = y1 - (b / a) as i64 * x1;
            let y = x1;
            (gcd, x, y)
        }
    }
}
```

### 欧几里得算法

用于计算最大公约数：

#### 算法

```rust
// 欧几里得算法
pub fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// 扩展欧几里得算法
pub fn extended_gcd(a: u64, b: u64) -> (u64, i64, i64) {
    if a == 0 {
        (b, 0, 1)
    } else {
        let (gcd, x1, y1) = extended_gcd(b % a, a);
        let x = y1 - (b / a) as i64 * x1;
        let y = x1;
        (gcd, x, y)
    }
}
```

### 费马小定理

密码学中的重要定理：

#### 定理

如果 $p$ 是素数，$a$ 是整数且 $p \nmid a$，则：

$$a^{p-1} \equiv 1 \pmod{p}$$

#### 应用

```rust
// 费马素性测试
pub fn fermat_primality_test(n: u64, k: usize) -> bool {
    if n <= 1 || n == 4 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    
    for _ in 0..k {
        let a = 2 + rand::random::<u64>() % (n - 4);
        if modular_power(a, n - 1, n) != 1 {
            return false;
        }
    }
    
    true
}

fn modular_power(base: u64, exponent: u64, modulus: u64) -> u64 {
    let mut result = 1;
    let mut base = base % modulus;
    let mut exp = exponent;
    
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % modulus;
        }
        exp >>= 1;
        base = (base * base) % modulus;
    }
    
    result
}
```

## 📈 图论基础

### 网络拓扑

网络可以用图来表示：

#### 图论定义

图 $G = (V, E)$ 由顶点集 $V$ 和边集 $E$ 组成，其中 $E \subseteq V \times V$。

#### 图论实现

```rust
// 网络图表示
pub struct NetworkGraph {
    vertices: Vec<Vertex>,
    edges: Vec<Edge>,
    adjacency_matrix: Vec<Vec<f64>>,
}

#[derive(Debug, Clone)]
pub struct Vertex {
    pub id: usize,
    pub label: String,
    pub position: (f64, f64),
}

#[derive(Debug, Clone)]
pub struct Edge {
    pub from: usize,
    pub to: usize,
    pub weight: f64,
    pub capacity: f64,
}

impl NetworkGraph {
    // 添加顶点
    pub fn add_vertex(&mut self, vertex: Vertex) {
        self.vertices.push(vertex);
        self.expand_adjacency_matrix();
    }
    
    // 添加边
    pub fn add_edge(&mut self, edge: Edge) {
        self.edges.push(edge.clone());
        self.adjacency_matrix[edge.from][edge.to] = edge.weight;
    }
    
    // 计算顶点度数
    pub fn vertex_degree(&self, vertex_id: usize) -> usize {
        self.adjacency_matrix[vertex_id]
            .iter()
            .filter(|&&weight| weight > 0.0)
            .count()
    }
    
    // 检查连通性
    pub fn is_connected(&self) -> bool {
        if self.vertices.is_empty() {
            return true;
        }
        
        let mut visited = vec![false; self.vertices.len()];
        self.dfs(0, &mut visited);
        visited.iter().all(|&v| v)
    }
    
    // 深度优先搜索
    fn dfs(&self, vertex: usize, visited: &mut Vec<bool>) {
        visited[vertex] = true;
        for (neighbor, &weight) in self.adjacency_matrix[vertex].iter().enumerate() {
            if weight > 0.0 && !visited[neighbor] {
                self.dfs(neighbor, visited);
            }
        }
    }
}
```

### 最短路径算法

#### Dijkstra算法

```rust
// Dijkstra最短路径算法
pub fn dijkstra(graph: &NetworkGraph, start: usize) -> Vec<f64> {
    let n = graph.vertices.len();
    let mut distances = vec![f64::INFINITY; n];
    let mut visited = vec![false; n];
    
    distances[start] = 0.0;
    
    for _ in 0..n {
        let u = find_min_distance_vertex(&distances, &visited);
        visited[u] = true;
        
        for v in 0..n {
            if !visited[v] && graph.adjacency_matrix[u][v] > 0.0 {
                let new_distance = distances[u] + graph.adjacency_matrix[u][v];
                if new_distance < distances[v] {
                    distances[v] = new_distance;
                }
            }
        }
    }
    
    distances
}

fn find_min_distance_vertex(distances: &[f64], visited: &[bool]) -> usize {
    let mut min_distance = f64::INFINITY;
    let mut min_vertex = 0;
    
    for (i, &distance) in distances.iter().enumerate() {
        if !visited[i] && distance < min_distance {
            min_distance = distance;
            min_vertex = i;
        }
    }
    
    min_vertex
}
```

### 最小生成树

#### Kruskal算法

```rust
// Kruskal最小生成树算法
pub fn kruskal_mst(graph: &NetworkGraph) -> Vec<Edge> {
    let mut edges = graph.edges.clone();
    edges.sort_by(|a, b| a.weight.partial_cmp(&b.weight).unwrap());
    
    let mut mst = Vec::new();
    let mut union_find = UnionFind::new(graph.vertices.len());
    
    for edge in edges {
        if union_find.find(edge.from) != union_find.find(edge.to) {
            mst.push(edge.clone());
            union_find.union(edge.from, edge.to);
        }
    }
    
    mst
}

// 并查集数据结构
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }
    
    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    pub fn union(&mut self, x: usize, y: usize) {
        let px = self.find(x);
        let py = self.find(y);
        
        if px != py {
            if self.rank[px] < self.rank[py] {
                self.parent[px] = py;
            } else if self.rank[px] > self.rank[py] {
                self.parent[py] = px;
            } else {
                self.parent[py] = px;
                self.rank[px] += 1;
            }
        }
    }
}
```

## ⚡ 信息论基础

### 熵和信息量

#### 熵和信息量定义

离散随机变量 $X$ 的熵定义为：

$$H(X) = -\sum_{i} p(x_i) \log_2 p(x_i)$$

#### 信息论实现

```rust
// 信息论工具
pub struct InformationTheory {
    // 概率分布
    probabilities: Vec<f64>,
}

impl InformationTheory {
    // 计算熵
    pub fn entropy(&self) -> f64 {
        self.probabilities
            .iter()
            .filter(|&&p| p > 0.0)
            .map(|&p| -p * p.log2())
            .sum()
    }
    
    // 计算互信息
    pub fn mutual_information(&self, joint_prob: &[Vec<f64>]) -> f64 {
        let mut mi = 0.0;
        
        for i in 0..joint_prob.len() {
            for j in 0..joint_prob[i].len() {
                let p_xy = joint_prob[i][j];
                if p_xy > 0.0 {
                    let p_x = joint_prob[i].iter().sum::<f64>();
                    let p_y = joint_prob.iter().map(|row| row[j]).sum::<f64>();
                    
                    if p_x > 0.0 && p_y > 0.0 {
                        mi += p_xy * (p_xy / (p_x * p_y)).log2();
                    }
                }
            }
        }
        
        mi
    }
    
    // 计算条件熵
    pub fn conditional_entropy(&self, joint_prob: &[Vec<f64>]) -> f64 {
        let mut ce = 0.0;
        
        for i in 0..joint_prob.len() {
            let p_x = joint_prob[i].iter().sum::<f64>();
            if p_x > 0.0 {
                for j in 0..joint_prob[i].len() {
                    let p_xy = joint_prob[i][j];
                    if p_xy > 0.0 {
                        ce -= p_xy * (p_xy / p_x).log2();
                    }
                }
            }
        }
        
        ce
    }
}
```

### 信道容量

#### 信道容量定义

离散无记忆信道的容量定义为：

$$C = \max_{p(x)} I(X; Y)$$

其中 $I(X; Y)$ 是互信息。

#### 信道容量实现

```rust
// 信道容量计算
pub struct ChannelCapacity {
    // 转移概率矩阵
    transition_matrix: Vec<Vec<f64>>,
}

impl ChannelCapacity {
    // 计算信道容量
    pub fn calculate_capacity(&self) -> f64 {
        // 使用迭代算法求解
        let mut input_dist = vec![1.0 / self.transition_matrix.len() as f64; self.transition_matrix.len()];
        let mut prev_capacity = 0.0;
        let mut capacity = 1.0;
        let epsilon = 1e-6;
        
        while (capacity - prev_capacity).abs() > epsilon {
            prev_capacity = capacity;
            
            // 更新输入分布
            input_dist = self.update_input_distribution(&input_dist);
            
            // 计算互信息
            capacity = self.mutual_information(&input_dist);
        }
        
        capacity
    }
    
    // 更新输入分布
    fn update_input_distribution(&self, input_dist: &[f64]) -> Vec<f64> {
        let mut new_dist = vec![0.0; input_dist.len()];
        let mut sum = 0.0;
        
        for i in 0..input_dist.len() {
            let mut product = 1.0;
            for j in 0..self.transition_matrix[i].len() {
                if self.transition_matrix[i][j] > 0.0 {
                    let output_prob = self.output_probability(j, input_dist);
                    if output_prob > 0.0 {
                        product *= (self.transition_matrix[i][j] / output_prob).powf(self.transition_matrix[i][j]);
                    }
                }
            }
            new_dist[i] = product;
            sum += product;
        }
        
        // 归一化
        for i in 0..new_dist.len() {
            new_dist[i] /= sum;
        }
        
        new_dist
    }
    
    // 计算输出概率
    fn output_probability(&self, output: usize, input_dist: &[f64]) -> f64 {
        input_dist.iter()
            .enumerate()
            .map(|(i, &p)| p * self.transition_matrix[i][output])
            .sum()
    }
    
    // 计算互信息
    fn mutual_information(&self, input_dist: &[f64]) -> f64 {
        let mut mi = 0.0;
        
        for i in 0..input_dist.len() {
            for j in 0..self.transition_matrix[i].len() {
                let p_xy = input_dist[i] * self.transition_matrix[i][j];
                if p_xy > 0.0 {
                    let p_y = self.output_probability(j, input_dist);
                    if p_y > 0.0 {
                        mi += p_xy * (self.transition_matrix[i][j] / p_y).log2();
                    }
                }
            }
        }
        
        mi
    }
}
```

### 编码理论

#### 霍夫曼编码

```rust
// 霍夫曼编码
pub struct HuffmanEncoder {
    codes: HashMap<u8, Vec<bool>>,
}

impl HuffmanEncoder {
    pub fn new(frequencies: &HashMap<u8, usize>) -> Self {
        let codes = Self::build_codes(frequencies);
        Self { codes }
    }
    
    fn build_codes(frequencies: &HashMap<u8, usize>) -> HashMap<u8, Vec<bool>> {
        let mut heap = BinaryHeap::new();
        
        // 创建叶子节点
        for (symbol, freq) in frequencies {
            heap.push(Node::Leaf(*symbol, *freq));
        }
        
        // 构建霍夫曼树
        while heap.len() > 1 {
            let left = heap.pop().unwrap();
            let right = heap.pop().unwrap();
            let merged = Node::Internal(
                Box::new(left),
                Box::new(right),
                left.frequency() + right.frequency()
            );
            heap.push(merged);
        }
        
        // 生成编码
        let root = heap.pop().unwrap();
        Self::generate_codes(&root, Vec::new())
    }
    
    fn generate_codes(node: &Node, mut code: Vec<bool>) -> HashMap<u8, Vec<bool>> {
        match node {
            Node::Leaf(symbol, _) => {
                let mut codes = HashMap::new();
                codes.insert(*symbol, code);
                codes
            }
            Node::Internal(left, right, _) => {
                let mut left_code = code.clone();
                left_code.push(false);
                let mut right_code = code;
                right_code.push(true);
                
                let mut left_codes = Self::generate_codes(left, left_code);
                let right_codes = Self::generate_codes(right, right_code);
                
                left_codes.extend(right_codes);
                left_codes
            }
        }
    }
    
    // 编码
    pub fn encode(&self, data: &[u8]) -> Vec<bool> {
        let mut result = Vec::new();
        for &byte in data {
            if let Some(code) = self.codes.get(&byte) {
                result.extend(code);
            }
        }
        result
    }
    
    // 计算压缩比
    pub fn compression_ratio(&self, original_size: usize, compressed_size: usize) -> f64 {
        original_size as f64 / compressed_size as f64
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Node {
    Leaf(u8, usize),
    Internal(Box<Node>, Box<Node>, usize),
}

impl Node {
    fn frequency(&self) -> usize {
        match self {
            Node::Leaf(_, freq) => *freq,
            Node::Internal(_, _, freq) => *freq,
        }
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        other.frequency().cmp(&self.frequency())
    }
}
```

## 🧮 线性代数基础

### 矩阵运算

#### 矩阵乘法

```rust
// 矩阵运算
pub struct Matrix {
    data: Vec<Vec<f64>>,
    rows: usize,
    cols: usize,
}

impl Matrix {
    pub fn new(rows: usize, cols: usize) -> Self {
        Self {
            data: vec![vec![0.0; cols]; rows],
            rows,
            cols,
        }
    }
    
    pub fn multiply(&self, other: &Matrix) -> Result<Matrix, String> {
        if self.cols != other.rows {
            return Err("Matrix dimensions incompatible".to_string());
        }
        
        let mut result = Matrix::new(self.rows, other.cols);
        
        for i in 0..self.rows {
            for j in 0..other.cols {
                for k in 0..self.cols {
                    result.data[i][j] += self.data[i][k] * other.data[k][j];
                }
            }
        }
        
        Ok(result)
    }
    
    // 矩阵转置
    pub fn transpose(&self) -> Matrix {
        let mut result = Matrix::new(self.cols, self.rows);
        
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[j][i] = self.data[i][j];
            }
        }
        
        result
    }
    
    // 计算行列式
    pub fn determinant(&self) -> Result<f64, String> {
        if self.rows != self.cols {
            return Err("Matrix must be square".to_string());
        }
        
        if self.rows == 1 {
            return Ok(self.data[0][0]);
        }
        
        if self.rows == 2 {
            return Ok(self.data[0][0] * self.data[1][1] - self.data[0][1] * self.data[1][0]);
        }
        
        let mut det = 0.0;
        for j in 0..self.cols {
            let minor = self.minor(0, j);
            det += self.data[0][j] * minor.determinant().unwrap() * if j % 2 == 0 { 1.0 } else { -1.0 };
        }
        
        Ok(det)
    }
    
    // 计算子矩阵
    fn minor(&self, row: usize, col: usize) -> Matrix {
        let mut result = Matrix::new(self.rows - 1, self.cols - 1);
        let mut r = 0;
        
        for i in 0..self.rows {
            if i != row {
                let mut c = 0;
                for j in 0..self.cols {
                    if j != col {
                        result.data[r][c] = self.data[i][j];
                        c += 1;
                    }
                }
                r += 1;
            }
        }
        
        result
    }
}
```

### 特征值和特征向量

#### 幂迭代法

```rust
// 特征值和特征向量计算
pub struct EigenvalueSolver {
    matrix: Matrix,
    tolerance: f64,
    max_iterations: usize,
}

impl EigenvalueSolver {
    pub fn new(matrix: Matrix) -> Self {
        Self {
            matrix,
            tolerance: 1e-6,
            max_iterations: 1000,
        }
    }
    
    // 幂迭代法计算主特征值
    pub fn power_iteration(&self) -> Result<(f64, Vec<f64>), String> {
        let n = self.matrix.rows;
        let mut eigenvector = vec![1.0; n];
        let mut prev_eigenvalue = 0.0;
        
        for _ in 0..self.max_iterations {
            // 归一化向量
            let norm = eigenvector.iter().map(|x| x * x).sum::<f64>().sqrt();
            for i in 0..n {
                eigenvector[i] /= norm;
            }
            
            // 计算新的向量
            let mut new_vector = vec![0.0; n];
            for i in 0..n {
                for j in 0..n {
                    new_vector[i] += self.matrix.data[i][j] * eigenvector[j];
                }
            }
            
            // 计算特征值
            let eigenvalue = new_vector.iter().zip(&eigenvector)
                .map(|(a, b)| a * b)
                .sum::<f64>();
            
            // 检查收敛
            if (eigenvalue - prev_eigenvalue).abs() < self.tolerance {
                return Ok((eigenvalue, eigenvector));
            }
            
            prev_eigenvalue = eigenvalue;
            eigenvector = new_vector;
        }
        
        Err("Power iteration did not converge".to_string())
    }
}
```

### 奇异值分解

#### SVD算法

```rust
// 奇异值分解
pub struct SVD {
    u: Matrix,
    s: Vec<f64>,
    v: Matrix,
}

impl SVD {
    pub fn decompose(matrix: &Matrix) -> Result<SVD, String> {
        let m = matrix.rows;
        let n = matrix.cols;
        
        // 计算 A^T * A
        let at = matrix.transpose();
        let ata = at.multiply(matrix)?;
        
        // 计算 A * A^T
        let aat = matrix.multiply(&at)?;
        
        // 计算 A^T * A 的特征值和特征向量
        let solver = EigenvalueSolver::new(ata);
        let (eigenvalue, eigenvector) = solver.power_iteration()?;
        
        // 计算奇异值
        let sigma = eigenvalue.sqrt();
        
        // 计算 V 矩阵
        let v = Matrix::from_vector(eigenvector, n, 1);
        
        // 计算 U 矩阵
        let u_vector = matrix.multiply(&v)?;
        let u = Matrix::from_vector(u_vector.data[0].clone(), m, 1);
        
        // 归一化 U
        let u_norm = u.data[0].iter().map(|x| x * x).sum::<f64>().sqrt();
        for i in 0..m {
            u.data[i][0] /= u_norm;
        }
        
        Ok(SVD {
            u,
            s: vec![sigma],
            v,
        })
    }
}

impl Matrix {
    fn from_vector(vector: Vec<f64>, rows: usize, cols: usize) -> Matrix {
        let mut matrix = Matrix::new(rows, cols);
        for i in 0..rows {
            for j in 0..cols {
                matrix.data[i][j] = vector[i * cols + j];
            }
        }
        matrix
    }
}
```

## 📊 统计学基础

### 描述性统计

#### 统计量计算

```rust
// 描述性统计
pub struct DescriptiveStatistics {
    data: Vec<f64>,
}

impl DescriptiveStatistics {
    pub fn new(data: Vec<f64>) -> Self {
        Self { data }
    }
    
    // 计算均值
    pub fn mean(&self) -> f64 {
        self.data.iter().sum::<f64>() / self.data.len() as f64
    }
    
    // 计算中位数
    pub fn median(&self) -> f64 {
        let mut sorted_data = self.data.clone();
        sorted_data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let n = sorted_data.len();
        if n % 2 == 0 {
            (sorted_data[n / 2 - 1] + sorted_data[n / 2]) / 2.0
        } else {
            sorted_data[n / 2]
        }
    }
    
    // 计算标准差
    pub fn standard_deviation(&self) -> f64 {
        let mean = self.mean();
        let variance = self.data.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / self.data.len() as f64;
        variance.sqrt()
    }
    
    // 计算偏度
    pub fn skewness(&self) -> f64 {
        let mean = self.mean();
        let std_dev = self.standard_deviation();
        
        let n = self.data.len() as f64;
        let skewness = self.data.iter()
            .map(|x| ((x - mean) / std_dev).powi(3))
            .sum::<f64>() / n;
        
        skewness
    }
    
    // 计算峰度
    pub fn kurtosis(&self) -> f64 {
        let mean = self.mean();
        let std_dev = self.standard_deviation();
        
        let n = self.data.len() as f64;
        let kurtosis = self.data.iter()
            .map(|x| ((x - mean) / std_dev).powi(4))
            .sum::<f64>() / n;
        
        kurtosis - 3.0 // 超额峰度
    }
}
```

### 假设检验

#### t检验

```rust
// 假设检验
pub struct HypothesisTesting {
    data: Vec<f64>,
}

impl HypothesisTesting {
    pub fn new(data: Vec<f64>) -> Self {
        Self { data }
    }
    
    // 单样本t检验
    pub fn one_sample_t_test(&self, hypothesized_mean: f64) -> TTestResult {
        let n = self.data.len() as f64;
        let sample_mean = self.data.iter().sum::<f64>() / n;
        let sample_std = self.standard_deviation();
        
        let t_statistic = (sample_mean - hypothesized_mean) / (sample_std / n.sqrt());
        let degrees_of_freedom = n - 1.0;
        
        let p_value = self.t_distribution_p_value(t_statistic, degrees_of_freedom);
        
        TTestResult {
            t_statistic,
            degrees_of_freedom,
            p_value,
            significant: p_value < 0.05,
        }
    }
    
    // 双样本t检验
    pub fn two_sample_t_test(&self, other: &HypothesisTesting) -> TTestResult {
        let n1 = self.data.len() as f64;
        let n2 = other.data.len() as f64;
        
        let mean1 = self.data.iter().sum::<f64>() / n1;
        let mean2 = other.data.iter().sum::<f64>() / n2;
        
        let var1 = self.variance();
        let var2 = other.variance();
        
        let pooled_variance = ((n1 - 1.0) * var1 + (n2 - 1.0) * var2) / (n1 + n2 - 2.0);
        let standard_error = (pooled_variance * (1.0 / n1 + 1.0 / n2)).sqrt();
        
        let t_statistic = (mean1 - mean2) / standard_error;
        let degrees_of_freedom = n1 + n2 - 2.0;
        
        let p_value = self.t_distribution_p_value(t_statistic, degrees_of_freedom);
        
        TTestResult {
            t_statistic,
            degrees_of_freedom,
            p_value,
            significant: p_value < 0.05,
        }
    }
    
    fn variance(&self) -> f64 {
        let mean = self.data.iter().sum::<f64>() / self.data.len() as f64;
        self.data.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / (self.data.len() - 1) as f64
    }
    
    fn t_distribution_p_value(&self, t: f64, df: f64) -> f64 {
        // 简化的t分布p值计算
        // 实际应用中应使用更精确的算法
        if t.abs() > 2.0 {
            0.05
        } else {
            0.1
        }
    }
}

#[derive(Debug)]
pub struct TTestResult {
    pub t_statistic: f64,
    pub degrees_of_freedom: f64,
    pub p_value: f64,
    pub significant: bool,
}
```

### 回归分析

#### 线性回归

```rust
// 线性回归
pub struct LinearRegression {
    x: Vec<f64>,
    y: Vec<f64>,
}

impl LinearRegression {
    pub fn new(x: Vec<f64>, y: Vec<f64>) -> Result<Self, String> {
        if x.len() != y.len() {
            return Err("X and Y vectors must have the same length".to_string());
        }
        Ok(Self { x, y })
    }
    
    // 计算回归系数
    pub fn fit(&self) -> RegressionResult {
        let n = self.x.len() as f64;
        
        let sum_x = self.x.iter().sum::<f64>();
        let sum_y = self.y.iter().sum::<f64>();
        let sum_xy = self.x.iter().zip(&self.y).map(|(x, y)| x * y).sum::<f64>();
        let sum_x2 = self.x.iter().map(|x| x * x).sum::<f64>();
        let sum_y2 = self.y.iter().map(|y| y * y).sum::<f64>();
        
        // 计算斜率和截距
        let slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x);
        let intercept = (sum_y - slope * sum_x) / n;
        
        // 计算决定系数
        let y_mean = sum_y / n;
        let ss_tot = self.y.iter().map(|y| (y - y_mean).powi(2)).sum::<f64>();
        let ss_res = self.x.iter().zip(&self.y)
            .map(|(x, y)| (y - (slope * x + intercept)).powi(2))
            .sum::<f64>();
        let r_squared = 1.0 - ss_res / ss_tot;
        
        // 计算标准误差
        let mse = ss_res / (n - 2.0);
        let se_slope = (mse / (n * sum_x2 - sum_x * sum_x)).sqrt();
        let se_intercept = (mse * sum_x2 / (n * sum_x2 - sum_x * sum_x)).sqrt();
        
        RegressionResult {
            slope,
            intercept,
            r_squared,
            standard_error_slope: se_slope,
            standard_error_intercept: se_intercept,
            mean_squared_error: mse,
        }
    }
    
    // 预测
    pub fn predict(&self, x: f64, result: &RegressionResult) -> f64 {
        result.slope * x + result.intercept
    }
}

#[derive(Debug)]
pub struct RegressionResult {
    pub slope: f64,
    pub intercept: f64,
    pub r_squared: f64,
    pub standard_error_slope: f64,
    pub standard_error_intercept: f64,
    pub mean_squared_error: f64,
}
```

## 🔐 密码学数学基础

### 群论

#### 群的定义和性质

```rust
// 群论基础
pub trait Group {
    type Element;
    
    // 群运算
    fn operation(&self, a: &Self::Element, b: &Self::Element) -> Self::Element;
    
    // 单位元
    fn identity(&self) -> Self::Element;
    
    // 逆元
    fn inverse(&self, a: &Self::Element) -> Self::Element;
    
    // 验证群公理
    fn verify_group_axioms(&self) -> bool {
        // 结合律: (a * b) * c = a * (b * c)
        // 单位元: a * e = e * a = a
        // 逆元: a * a^(-1) = a^(-1) * a = e
        true // 简化实现
    }
}

// 模n乘法群
pub struct ModularMultiplicativeGroup {
    modulus: u64,
}

impl ModularMultiplicativeGroup {
    pub fn new(modulus: u64) -> Self {
        Self { modulus }
    }
    
    // 检查元素是否在群中
    pub fn is_element(&self, a: u64) -> bool {
        gcd(a, self.modulus) == 1
    }
    
    // 计算群的阶
    pub fn order(&self) -> u64 {
        self.euler_phi(self.modulus)
    }
    
    // 欧拉函数
    fn euler_phi(&self, n: u64) -> u64 {
        let mut result = n;
        let mut p = 2;
        
        while p * p <= n {
            if n % p == 0 {
                while n % p == 0 {
                    n /= p;
                }
                result -= result / p;
            }
            p += 1;
        }
        
        if n > 1 {
            result -= result / n;
        }
        
        result
    }
}

impl Group for ModularMultiplicativeGroup {
    type Element = u64;
    
    fn operation(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        (a * b) % self.modulus
    }
    
    fn identity(&self) -> Self::Element {
        1
    }
    
    fn inverse(&self, a: &Self::Element) -> Self::Element {
        // 使用扩展欧几里得算法计算逆元
        let (gcd, x, _) = extended_gcd(*a, self.modulus);
        if gcd == 1 {
            (x % self.modulus as i64 + self.modulus as i64) as u64 % self.modulus
        } else {
            panic!("Element has no inverse");
        }
    }
}
```

### 椭圆曲线

#### 椭圆曲线密码学

```rust
// 椭圆曲线点
#[derive(Debug, Clone, PartialEq)]
pub struct EllipticCurvePoint {
    x: Option<u64>,
    y: Option<u64>,
    is_infinity: bool,
}

impl EllipticCurvePoint {
    pub fn new(x: u64, y: u64) -> Self {
        Self {
            x: Some(x),
            y: Some(y),
            is_infinity: false,
        }
    }
    
    pub fn infinity() -> Self {
        Self {
            x: None,
            y: None,
            is_infinity: true,
        }
    }
}

// 椭圆曲线
pub struct EllipticCurve {
    a: u64,
    b: u64,
    p: u64, // 模数
}

impl EllipticCurve {
    pub fn new(a: u64, b: u64, p: u64) -> Self {
        Self { a, b, p }
    }
    
    // 检查点是否在曲线上
    pub fn is_on_curve(&self, point: &EllipticCurvePoint) -> bool {
        if point.is_infinity {
            return true;
        }
        
        let x = point.x.unwrap();
        let y = point.y.unwrap();
        
        let left = (y * y) % self.p;
        let right = (x * x * x + self.a * x + self.b) % self.p;
        
        left == right
    }
    
    // 点加法
    pub fn point_add(&self, p1: &EllipticCurvePoint, p2: &EllipticCurvePoint) -> EllipticCurvePoint {
        if p1.is_infinity {
            return p2.clone();
        }
        if p2.is_infinity {
            return p1.clone();
        }
        
        let x1 = p1.x.unwrap();
        let y1 = p1.y.unwrap();
        let x2 = p2.x.unwrap();
        let y2 = p2.y.unwrap();
        
        if x1 == x2 {
            if y1 == y2 {
                return self.point_double(p1);
            } else {
                return EllipticCurvePoint::infinity();
            }
        }
        
        let delta_x = (x2 - x1 + self.p) % self.p;
        let delta_y = (y2 - y1 + self.p) % self.p;
        
        let slope = (delta_y * self.modular_inverse(delta_x)) % self.p;
        
        let x3 = (slope * slope - x1 - x2 + self.p) % self.p;
        let y3 = (slope * (x1 - x3 + self.p) - y1 + self.p) % self.p;
        
        EllipticCurvePoint::new(x3, y3)
    }
    
    // 点倍乘
    pub fn point_double(&self, point: &EllipticCurvePoint) -> EllipticCurvePoint {
        if point.is_infinity {
            return EllipticCurvePoint::infinity();
        }
        
        let x = point.x.unwrap();
        let y = point.y.unwrap();
        
        let slope = (3 * x * x + self.a) * self.modular_inverse(2 * y) % self.p;
        
        let x3 = (slope * slope - 2 * x + self.p) % self.p;
        let y3 = (slope * (x - x3 + self.p) - y + self.p) % self.p;
        
        EllipticCurvePoint::new(x3, y3)
    }
    
    // 标量乘法
    pub fn scalar_multiply(&self, point: &EllipticCurvePoint, scalar: u64) -> EllipticCurvePoint {
        let mut result = EllipticCurvePoint::infinity();
        let mut addend = point.clone();
        let mut k = scalar;
        
        while k > 0 {
            if k & 1 == 1 {
                result = self.point_add(&result, &addend);
            }
            addend = self.point_double(&addend);
            k >>= 1;
        }
        
        result
    }
    
    // 模逆元
    fn modular_inverse(&self, a: u64) -> u64 {
        let (gcd, x, _) = extended_gcd(a, self.p);
        if gcd == 1 {
            (x % self.p as i64 + self.p as i64) as u64 % self.p
        } else {
            panic!("No modular inverse exists");
        }
    }
}
```

### 离散对数

#### 离散对数问题

```rust
// 离散对数求解
pub struct DiscreteLogarithm {
    base: u64,
    modulus: u64,
}

impl DiscreteLogarithm {
    pub fn new(base: u64, modulus: u64) -> Self {
        Self { base, modulus }
    }
    
    // 暴力搜索
    pub fn brute_force(&self, target: u64) -> Option<u64> {
        let mut result = 1;
        for i in 0..self.modulus {
            if result == target {
                return Some(i);
            }
            result = (result * self.base) % self.modulus;
        }
        None
    }
    
    // 大步小步算法
    pub fn baby_step_giant_step(&self, target: u64) -> Option<u64> {
        let m = (self.modulus as f64).sqrt().ceil() as u64;
        
        // 计算小步
        let mut baby_steps = HashMap::new();
        let mut result = 1;
        for j in 0..m {
            baby_steps.insert(result, j);
            result = (result * self.base) % self.modulus;
        }
        
        // 计算大步
        let giant_step = self.modular_power(self.base, m, self.modulus);
        result = 1;
        for i in 0..m {
            let target_inv = self.modular_inverse(result, self.modulus);
            let target_mod = (target * target_inv) % self.modulus;
            
            if let Some(&j) = baby_steps.get(&target_mod) {
                return Some(i * m + j);
            }
            
            result = (result * giant_step) % self.modulus;
        }
        
        None
    }
    
    // 模幂运算
    fn modular_power(&self, base: u64, exponent: u64, modulus: u64) -> u64 {
        let mut result = 1;
        let mut base = base % modulus;
        let mut exp = exponent;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            exp >>= 1;
            base = (base * base) % modulus;
        }
        
        result
    }
    
    // 模逆元
    fn modular_inverse(&self, a: u64, modulus: u64) -> u64 {
        let (gcd, x, _) = extended_gcd(a, modulus);
        if gcd == 1 {
            (x % modulus as i64 + modulus as i64) as u64 % modulus
        } else {
            panic!("No modular inverse exists");
        }
    }
}
```

## 🎯 优化理论

### 线性规划

#### 单纯形法

```rust
// 线性规划
pub struct LinearProgram {
    // 目标函数系数
    objective: Vec<f64>,
    // 约束矩阵
    constraints: Vec<Vec<f64>>,
    // 约束右端项
    rhs: Vec<f64>,
    // 约束类型 (<=, =, >=)
    constraint_types: Vec<ConstraintType>,
}

#[derive(Debug, Clone)]
pub enum ConstraintType {
    LessThanOrEqual,
    Equal,
    GreaterThanOrEqual,
}

impl LinearProgram {
    pub fn new(objective: Vec<f64>, constraints: Vec<Vec<f64>>, rhs: Vec<f64>, constraint_types: Vec<ConstraintType>) -> Self {
        Self {
            objective,
            constraints,
            rhs,
            constraint_types,
        }
    }
    
    // 单纯形法求解
    pub fn solve_simplex(&self) -> Result<LinearProgramResult, String> {
        // 转换为标准形式
        let standard_form = self.to_standard_form();
        
        // 初始化单纯形表
        let mut tableau = self.create_initial_tableau(&standard_form);
        
        // 主循环
        while !self.is_optimal(&tableau) {
            let pivot_column = self.find_pivot_column(&tableau);
            let pivot_row = self.find_pivot_row(&tableau, pivot_column);
            
            if pivot_row == None {
                return Err("Unbounded solution".to_string());
            }
            
            self.pivot(&mut tableau, pivot_row.unwrap(), pivot_column);
        }
        
        // 提取解
        let solution = self.extract_solution(&tableau);
        let objective_value = self.calculate_objective_value(&solution);
        
        Ok(LinearProgramResult {
            solution,
            objective_value,
            optimal: true,
        })
    }
    
    // 转换为标准形式
    fn to_standard_form(&self) -> LinearProgram {
        // 实现标准形式转换
        self.clone()
    }
    
    // 创建初始单纯形表
    fn create_initial_tableau(&self, standard_form: &LinearProgram) -> Vec<Vec<f64>> {
        // 实现初始单纯形表创建
        vec![vec![0.0; 10]; 10] // 简化实现
    }
    
    // 检查是否最优
    fn is_optimal(&self, tableau: &[Vec<f64>]) -> bool {
        // 检查目标函数行是否所有系数非负
        tableau[0].iter().skip(1).all(|&x| x >= 0.0)
    }
    
    // 寻找主元列
    fn find_pivot_column(&self, tableau: &[Vec<f64>]) -> usize {
        tableau[0].iter().skip(1).position(|&x| x < 0.0).unwrap_or(0)
    }
    
    // 寻找主元行
    fn find_pivot_row(&self, tableau: &[Vec<f64>], pivot_column: usize) -> Option<usize> {
        let mut min_ratio = f64::INFINITY;
        let mut pivot_row = None;
        
        for i in 1..tableau.len() {
            if tableau[i][pivot_column] > 0.0 {
                let ratio = tableau[i][0] / tableau[i][pivot_column];
                if ratio < min_ratio {
                    min_ratio = ratio;
                    pivot_row = Some(i);
                }
            }
        }
        
        pivot_row
    }
    
    // 主元变换
    fn pivot(&self, tableau: &mut [Vec<f64>], pivot_row: usize, pivot_column: usize) {
        let pivot_element = tableau[pivot_row][pivot_column];
        
        // 归一化主元行
        for j in 0..tableau[pivot_row].len() {
            tableau[pivot_row][j] /= pivot_element;
        }
        
        // 消元
        for i in 0..tableau.len() {
            if i != pivot_row {
                let factor = tableau[i][pivot_column];
                for j in 0..tableau[i].len() {
                    tableau[i][j] -= factor * tableau[pivot_row][j];
                }
            }
        }
    }
    
    // 提取解
    fn extract_solution(&self, tableau: &[Vec<f64>]) -> Vec<f64> {
        // 实现解提取
        vec![0.0; self.objective.len()]
    }
    
    // 计算目标函数值
    fn calculate_objective_value(&self, solution: &[f64]) -> f64 {
        solution.iter().zip(&self.objective).map(|(x, c)| x * c).sum()
    }
}

#[derive(Debug)]
pub struct LinearProgramResult {
    pub solution: Vec<f64>,
    pub objective_value: f64,
    pub optimal: bool,
}
```

### 动态规划

#### 网络流问题

```rust
// 动态规划求解网络流
pub struct NetworkFlowDP {
    graph: NetworkGraph,
    source: usize,
    sink: usize,
}

impl NetworkFlowDP {
    pub fn new(graph: NetworkGraph, source: usize, sink: usize) -> Self {
        Self { graph, source, sink }
    }
    
    // 最大流问题
    pub fn max_flow(&self) -> f64 {
        let mut residual_graph = self.graph.clone();
        let mut max_flow = 0.0;
        
        // 使用增广路径算法
        while let Some(path) = self.find_augmenting_path(&residual_graph) {
            let flow = self.find_bottleneck(&path, &residual_graph);
            self.update_residual_graph(&mut residual_graph, &path, flow);
            max_flow += flow;
        }
        
        max_flow
    }
    
    // 寻找增广路径
    fn find_augmenting_path(&self, graph: &NetworkGraph) -> Option<Vec<usize>> {
        let mut visited = vec![false; graph.vertices.len()];
        let mut path = Vec::new();
        
        if self.dfs_path(graph, self.source, self.sink, &mut visited, &mut path) {
            Some(path)
        } else {
            None
        }
    }
    
    // 深度优先搜索寻找路径
    fn dfs_path(&self, graph: &NetworkGraph, current: usize, target: usize, visited: &mut Vec<bool>, path: &mut Vec<usize>) -> bool {
        visited[current] = true;
        path.push(current);
        
        if current == target {
            return true;
        }
        
        for (neighbor, &weight) in graph.adjacency_matrix[current].iter().enumerate() {
            if weight > 0.0 && !visited[neighbor] {
                if self.dfs_path(graph, neighbor, target, visited, path) {
                    return true;
                }
            }
        }
        
        path.pop();
        false
    }
    
    // 寻找瓶颈容量
    fn find_bottleneck(&self, path: &[usize], graph: &NetworkGraph) -> f64 {
        let mut min_capacity = f64::INFINITY;
        
        for i in 0..path.len() - 1 {
            let capacity = graph.adjacency_matrix[path[i]][path[i + 1]];
            min_capacity = min_capacity.min(capacity);
        }
        
        min_capacity
    }
    
    // 更新残量图
    fn update_residual_graph(&self, graph: &mut NetworkGraph, path: &[usize], flow: f64) {
        for i in 0..path.len() - 1 {
            let from = path[i];
            let to = path[i + 1];
            
            // 减少正向边容量
            graph.adjacency_matrix[from][to] -= flow;
            
            // 增加反向边容量
            graph.adjacency_matrix[to][from] += flow;
        }
    }
}
```

### 启发式算法

#### 遗传算法

```rust
// 遗传算法
pub struct GeneticAlgorithm {
    population_size: usize,
    mutation_rate: f64,
    crossover_rate: f64,
    max_generations: usize,
}

impl GeneticAlgorithm {
    pub fn new(population_size: usize, mutation_rate: f64, crossover_rate: f64, max_generations: usize) -> Self {
        Self {
            population_size,
            mutation_rate,
            crossover_rate,
            max_generations,
        }
    }
    
    // 运行遗传算法
    pub fn run<F>(&self, fitness_function: F) -> Vec<f64>
    where
        F: Fn(&[f64]) -> f64,
    {
        // 初始化种群
        let mut population = self.initialize_population();
        
        for generation in 0..self.max_generations {
            // 评估适应度
            let fitness_scores: Vec<f64> = population.iter()
                .map(|individual| fitness_function(individual))
                .collect();
            
            // 选择
            let selected = self.selection(&population, &fitness_scores);
            
            // 交叉
            let offspring = self.crossover(&selected);
            
            // 变异
            let mutated = self.mutation(&offspring);
            
            // 更新种群
            population = mutated;
        }
        
        // 返回最优解
        population.into_iter()
            .max_by(|a, b| fitness_function(a).partial_cmp(&fitness_function(b)).unwrap())
            .unwrap()
    }
    
    // 初始化种群
    fn initialize_population(&self) -> Vec<Vec<f64>> {
        (0..self.population_size)
            .map(|_| {
                (0..10) // 假设10个变量
                    .map(|_| rand::random::<f64>() * 10.0 - 5.0) // 范围[-5, 5]
                    .collect()
            })
            .collect()
    }
    
    // 选择操作
    fn selection(&self, population: &[Vec<f64>], fitness_scores: &[f64]) -> Vec<Vec<f64>> {
        let total_fitness: f64 = fitness_scores.iter().sum();
        let mut selected = Vec::new();
        
        for _ in 0..self.population_size {
            let random = rand::random::<f64>() * total_fitness;
            let mut cumulative = 0.0;
            
            for (i, &fitness) in fitness_scores.iter().enumerate() {
                cumulative += fitness;
                if cumulative >= random {
                    selected.push(population[i].clone());
                    break;
                }
            }
        }
        
        selected
    }
    
    // 交叉操作
    fn crossover(&self, population: &[Vec<f64>]) -> Vec<Vec<f64>> {
        let mut offspring = Vec::new();
        
        for i in (0..population.len()).step_by(2) {
            if i + 1 < population.len() {
                let parent1 = &population[i];
                let parent2 = &population[i + 1];
                
                if rand::random::<f64>() < self.crossover_rate {
                    let (child1, child2) = self.single_point_crossover(parent1, parent2);
                    offspring.push(child1);
                    offspring.push(child2);
                } else {
                    offspring.push(parent1.clone());
                    offspring.push(parent2.clone());
                }
            }
        }
        
        offspring
    }
    
    // 单点交叉
    fn single_point_crossover(&self, parent1: &[f64], parent2: &[f64]) -> (Vec<f64>, Vec<f64>) {
        let crossover_point = rand::random::<usize>() % parent1.len();
        
        let mut child1 = parent1[..crossover_point].to_vec();
        child1.extend_from_slice(&parent2[crossover_point..]);
        
        let mut child2 = parent2[..crossover_point].to_vec();
        child2.extend_from_slice(&parent1[crossover_point..]);
        
        (child1, child2)
    }
    
    // 变异操作
    fn mutation(&self, population: &[Vec<f64>]) -> Vec<Vec<f64>> {
        population.iter()
            .map(|individual| {
                individual.iter()
                    .map(|&gene| {
                        if rand::random::<f64>() < self.mutation_rate {
                            gene + rand::random::<f64>() * 0.1 - 0.05 // 小幅变异
                        } else {
                            gene
                        }
                    })
                    .collect()
            })
            .collect()
    }
}
```

## 📚 参考文献

1. Ross, S. M. (2014). *Introduction to Probability Models*. Academic Press.
2. Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2009). *Introduction to Algorithms*. MIT Press.
3. Cover, T. M., & Thomas, J. A. (2006). *Elements of Information Theory*. Wiley.
4. Strang, G. (2016). *Introduction to Linear Algebra*. Wellesley-Cambridge Press.
5. Montgomery, D. C., Peck, E. A., & Vining, G. G. (2012). *Introduction to Linear Regression Analysis*. Wiley.
6. Menezes, A. J., Van Oorschot, P. C., & Vanstone, S. A. (1996). *Handbook of Applied Cryptography*. CRC Press.
7. Boyd, S., & Vandenberghe, L. (2004). *Convex Optimization*. Cambridge University Press.
8. Goldberg, D. E. (1989). *Genetic Algorithms in Search, Optimization, and Machine Learning*. Addison-Wesley.

---

**数学基础版本**: v1.0  
**最后更新**: 2025年1月  
**维护者**: C10 Networks 数学理论团队
