# C10 Networks 网络性能模型

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。


## 📊 目录

- [📋 目录](#目录)
- [🎯 概述](#概述)
- [📊 排队论模型](#排队论模型)
  - [M/M/1队列模型](#mm1队列模型)
    - [模型定义](#模型定义)
    - [数学公式](#数学公式)
    - [实现](#实现)
  - [M/M/c队列模型](#mmc队列模型)
    - [模型定义1](#模型定义1)
    - [数学公式1](#数学公式1)
    - [实现1](#实现1)
  - [M/G/1队列模型](#mg1队列模型)
    - [模型定义2](#模型定义2)
    - [Pollaczek-Khinchine公式](#pollaczek-khinchine公式)
    - [实现4](#实现4)
  - [G/G/1队列模型](#gg1队列模型)
    - [模型定义3](#模型定义3)
    - [Kingman公式](#kingman公式)
    - [实现2](#实现2)
- [🔗 网络拓扑模型](#网络拓扑模型)
  - [随机图模型](#随机图模型)
    - [Erdős-Rényi模型](#erdős-rényi模型)
    - [实现3](#实现3)
  - [小世界网络模型](#小世界网络模型)
    - [Watts-Strogatz模型](#watts-strogatz模型)
    - [实现6](#实现6)
  - [无标度网络模型](#无标度网络模型)
    - [Barabási-Albert模型](#barabási-albert模型)
    - [实现5](#实现5)
  - [层次网络模型](#层次网络模型)
    - [层次网络](#层次网络)
    - [实现7](#实现7)
- [⚡ 延迟分析模型](#延迟分析模型)
  - [传播延迟模型](#传播延迟模型)
    - [传播延迟](#传播延迟)
    - [实现8](#实现8)
  - [传输延迟模型](#传输延迟模型)
    - [传输延迟](#传输延迟)
    - [实现9](#实现9)
  - [处理延迟模型](#处理延迟模型)
    - [处理延迟](#处理延迟)
    - [实现10](#实现10)
  - [排队延迟模型](#排队延迟模型)
    - [排队延迟](#排队延迟)
    - [实现11](#实现11)
- [📈 吞吐量模型](#吞吐量模型)
  - [TCP吞吐量模型](#tcp吞吐量模型)
    - [TCP吞吐量](#tcp吞吐量)
    - [实现12](#实现12)
  - [UDP吞吐量模型](#udp吞吐量模型)
    - [UDP吞吐量](#udp吞吐量)
    - [实现13](#实现13)
  - [HTTP吞吐量模型](#http吞吐量模型)
    - [HTTP吞吐量](#http吞吐量)
    - [实现14](#实现14)
  - [WebSocket吞吐量模型](#websocket吞吐量模型)
    - [WebSocket吞吐量](#websocket吞吐量)
    - [实现15](#实现15)
- [🔒 可靠性模型](#可靠性模型)
  - [故障模型](#故障模型)
    - [故障率模型](#故障率模型)
    - [实现16](#实现16)
  - [恢复模型](#恢复模型)
    - [恢复时间模型](#恢复时间模型)
    - [实现17](#实现17)
  - [冗余模型](#冗余模型)
    - [N+1冗余模型](#n1冗余模型)
    - [实现18](#实现18)
  - [一致性模型](#一致性模型)
    - [强一致性模型](#强一致性模型)
    - [实现19](#实现19)
- [🎯 优化模型](#优化模型)
  - [负载均衡模型](#负载均衡模型)
    - [负载均衡算法](#负载均衡算法)
    - [实现20](#实现20)
  - [缓存模型](#缓存模型)
    - [LRU缓存模型](#lru缓存模型)
    - [实现21](#实现21)
  - [压缩模型](#压缩模型)
    - [压缩算法模型](#压缩算法模型)
    - [实现22](#实现22)
  - [路由优化模型](#路由优化模型)
    - [最短路径算法](#最短路径算法)
    - [实现23](#实现23)
- [📚 参考文献](#参考文献)


## 📋 目录

- [C10 Networks 网络性能模型](#c10-networks-网络性能模型)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [📊 排队论模型](#-排队论模型)
    - [M/M/1队列模型](#mm1队列模型)
      - [模型定义](#模型定义)
      - [数学公式](#数学公式)
      - [实现](#实现)
    - [M/M/c队列模型](#mmc队列模型)
      - [模型定义1](#模型定义1)
      - [数学公式1](#数学公式1)
      - [实现1](#实现1)
    - [M/G/1队列模型](#mg1队列模型)
      - [模型定义2](#模型定义2)
      - [Pollaczek-Khinchine公式](#pollaczek-khinchine公式)
      - [实现4](#实现4)
    - [G/G/1队列模型](#gg1队列模型)
      - [模型定义3](#模型定义3)
      - [Kingman公式](#kingman公式)
      - [实现2](#实现2)
  - [🔗 网络拓扑模型](#-网络拓扑模型)
    - [随机图模型](#随机图模型)
      - [Erdős-Rényi模型](#erdős-rényi模型)
      - [实现3](#实现3)
    - [小世界网络模型](#小世界网络模型)
      - [Watts-Strogatz模型](#watts-strogatz模型)
      - [实现6](#实现6)
    - [无标度网络模型](#无标度网络模型)
      - [Barabási-Albert模型](#barabási-albert模型)
      - [实现5](#实现5)
    - [层次网络模型](#层次网络模型)
      - [层次网络](#层次网络)
      - [实现7](#实现7)
  - [⚡ 延迟分析模型](#-延迟分析模型)
    - [传播延迟模型](#传播延迟模型)
      - [传播延迟](#传播延迟)
      - [实现8](#实现8)
    - [传输延迟模型](#传输延迟模型)
      - [传输延迟](#传输延迟)
      - [实现9](#实现9)
    - [处理延迟模型](#处理延迟模型)
      - [处理延迟](#处理延迟)
      - [实现10](#实现10)
    - [排队延迟模型](#排队延迟模型)
      - [排队延迟](#排队延迟)
      - [实现11](#实现11)
  - [📈 吞吐量模型](#-吞吐量模型)
    - [TCP吞吐量模型](#tcp吞吐量模型)
      - [TCP吞吐量](#tcp吞吐量)
      - [实现12](#实现12)
    - [UDP吞吐量模型](#udp吞吐量模型)
      - [UDP吞吐量](#udp吞吐量)
      - [实现13](#实现13)
    - [HTTP吞吐量模型](#http吞吐量模型)
      - [HTTP吞吐量](#http吞吐量)
      - [实现14](#实现14)
    - [WebSocket吞吐量模型](#websocket吞吐量模型)
      - [WebSocket吞吐量](#websocket吞吐量)
      - [实现15](#实现15)
  - [🔒 可靠性模型](#-可靠性模型)
    - [故障模型](#故障模型)
      - [故障率模型](#故障率模型)
      - [实现16](#实现16)
    - [恢复模型](#恢复模型)
      - [恢复时间模型](#恢复时间模型)
      - [实现17](#实现17)
    - [冗余模型](#冗余模型)
      - [N+1冗余模型](#n1冗余模型)
      - [实现18](#实现18)
    - [一致性模型](#一致性模型)
      - [强一致性模型](#强一致性模型)
      - [实现19](#实现19)
  - [🎯 优化模型](#-优化模型)
    - [负载均衡模型](#负载均衡模型)
      - [负载均衡算法](#负载均衡算法)
      - [实现20](#实现20)
    - [缓存模型](#缓存模型)
      - [LRU缓存模型](#lru缓存模型)
      - [实现21](#实现21)
    - [压缩模型](#压缩模型)
      - [压缩算法模型](#压缩算法模型)
      - [实现22](#实现22)
    - [路由优化模型](#路由优化模型)
      - [最短路径算法](#最短路径算法)
      - [实现23](#实现23)
  - [📚 参考文献](#-参考文献)

## 🎯 概述

本文档提供了C10 Networks项目中网络性能分析的数学模型，包括排队论、网络拓扑、延迟分析、吞吐量建模、可靠性分析和优化模型等。这些模型为网络系统设计、性能预测和优化提供了理论基础。

## 📊 排队论模型

### M/M/1队列模型

#### 模型定义

M/M/1队列模型假设：

- 到达过程为泊松过程（M）
- 服务时间为指数分布（M）
- 单服务器（1）

#### 数学公式

**到达率**: $\lambda$ (packets/second)
**服务率**: $\mu$ (packets/second)
**利用率**: $\rho = \frac{\lambda}{\mu}$

**稳态概率**:
$$P_n = \rho^n(1-\rho), \quad n = 0, 1, 2, \ldots$$

**平均队列长度**:
$$L = \frac{\rho}{1-\rho}$$

**平均等待时间**:
$$W = \frac{1}{\mu - \lambda}$$

**平均响应时间**:
$$T = W + \frac{1}{\mu} = \frac{1}{\mu - \lambda}$$

#### 实现

```rust
// M/M/1队列模型
pub struct MM1Queue {
    arrival_rate: f64,    // λ
    service_rate: f64,    // μ
    utilization: f64,     // ρ
}

impl MM1Queue {
    pub fn new(arrival_rate: f64, service_rate: f64) -> Result<Self, String> {
        if arrival_rate >= service_rate {
            return Err("System must be stable (λ < μ)".to_string());
        }
        
        let utilization = arrival_rate / service_rate;
        
        Ok(Self {
            arrival_rate,
            service_rate,
            utilization,
        })
    }
    
    // 计算稳态概率
    pub fn steady_state_probability(&self, n: usize) -> f64 {
        self.utilization.powi(n as i32) * (1.0 - self.utilization)
    }
    
    // 计算平均队列长度
    pub fn average_queue_length(&self) -> f64 {
        self.utilization / (1.0 - self.utilization)
    }
    
    // 计算平均等待时间
    pub fn average_waiting_time(&self) -> f64 {
        1.0 / (self.service_rate - self.arrival_rate)
    }
    
    // 计算平均响应时间
    pub fn average_response_time(&self) -> f64 {
        self.average_waiting_time() + 1.0 / self.service_rate
    }
    
    // 计算队列长度方差
    pub fn queue_length_variance(&self) -> f64 {
        self.utilization / (1.0 - self.utilization).powi(2)
    }
    
    // 计算等待时间方差
    pub fn waiting_time_variance(&self) -> f64 {
        1.0 / (self.service_rate - self.arrival_rate).powi(2)
    }
    
    // 计算系统空闲概率
    pub fn idle_probability(&self) -> f64 {
        1.0 - self.utilization
    }
    
    // 计算系统繁忙概率
    pub fn busy_probability(&self) -> f64 {
        self.utilization
    }
}
```

### M/M/c队列模型

#### 模型定义1

M/M/c队列模型假设：

- 到达过程为泊松过程（M）
- 服务时间为指数分布（M）
- c个服务器（c）

#### 数学公式1

**到达率**: $\lambda$ (packets/second)
**服务率**: $\mu$ (packets/second)
**服务器数量**: $c$
**利用率**: $\rho = \frac{\lambda}{c\mu}$

**稳态概率**:
$$
P_0 = \left[\sum_{n=0}^{c-1} \frac{(\lambda/\mu)^n}{n!} + \frac{(\lambda/\mu)^c}{c!(1-\rho)}\right]^{-1}
$$

$$
P_n = \begin{cases}
\frac{(\lambda/\mu)^n}{n!}P_0, & n \leq c \\
\frac{(\lambda/\mu)^n}{c!c^{n-c}}P_0, & n > c
\end{cases}
$$

**平均队列长度**:
$$L_q = \frac{(\lambda/\mu)^c\rho}{c!(1-\rho)^2}P_0$$

**平均等待时间**:
$$W_q = \frac{L_q}{\lambda}$$

#### 实现1

```rust
// M/M/c队列模型
pub struct MMcQueue {
    arrival_rate: f64,    // λ
    service_rate: f64,    // μ
    servers: usize,       // c
    utilization: f64,     // ρ
}

impl MMcQueue {
    pub fn new(arrival_rate: f64, service_rate: f64, servers: usize) -> Result<Self, String> {
        if arrival_rate >= servers as f64 * service_rate {
            return Err("System must be stable (λ < cμ)".to_string());
        }

        let utilization = arrival_rate / (servers as f64 * service_rate);

        Ok(Self {
            arrival_rate,
            service_rate,
            servers,
            utilization,
        })
    }

    // 计算P0
    fn calculate_p0(&self) -> f64 {
        let mut sum = 0.0;
        let lambda_mu = self.arrival_rate / self.service_rate;

        // 计算前c-1项
        for n in 0..self.servers {
            sum += lambda_mu.powi(n as i32) / factorial(n);
        }

        // 计算第c项
        sum += lambda_mu.powi(self.servers as i32) /
               (factorial(self.servers) * (1.0 - self.utilization));

        1.0 / sum
    }

    // 计算稳态概率
    pub fn steady_state_probability(&self, n: usize) -> f64 {
        let p0 = self.calculate_p0();
        let lambda_mu = self.arrival_rate / self.service_rate;

        if n <= self.servers {
            lambda_mu.powi(n as i32) / factorial(n) * p0
        } else {
            lambda_mu.powi(n as i32) /
            (factorial(self.servers) * (self.servers as f64).powi((n - self.servers) as i32)) * p0
        }
    }

    // 计算平均队列长度
    pub fn average_queue_length(&self) -> f64 {
        let p0 = self.calculate_p0();
        let lambda_mu = self.arrival_rate / self.service_rate;

        lambda_mu.powi(self.servers as i32) * self.utilization /
        (factorial(self.servers) * (1.0 - self.utilization).powi(2)) * p0
    }

    // 计算平均等待时间
    pub fn average_waiting_time(&self) -> f64 {
        self.average_queue_length() / self.arrival_rate
    }

    // 计算平均响应时间
    pub fn average_response_time(&self) -> f64 {
        self.average_waiting_time() + 1.0 / self.service_rate
    }

    // 计算Erlang-C公式
    pub fn erlang_c(&self) -> f64 {
        let p0 = self.calculate_p0();
        let lambda_mu = self.arrival_rate / self.service_rate;

        lambda_mu.powi(self.servers as i32) /
        (factorial(self.servers) * (1.0 - self.utilization)) * p0
    }
}

fn factorial(n: usize) -> f64 {
    (1..=n).fold(1.0, |acc, x| acc * x as f64)
}
```

### M/G/1队列模型

#### 模型定义2

M/G/1队列模型假设：

- 到达过程为泊松过程（M）
- 服务时间为一般分布（G）
- 单服务器（1）

#### Pollaczek-Khinchine公式

**平均队列长度**:
$$L_q = \frac{\lambda^2\sigma^2 + \rho^2}{2(1-\rho)}$$

其中：

- $\lambda$: 到达率
- $\sigma^2$: 服务时间方差
- $\rho$: 利用率

**平均等待时间**:
$$W_q = \frac{L_q}{\lambda}$$

#### 实现4

```rust
// M/G/1队列模型
pub struct MG1Queue {
    arrival_rate: f64,    // λ
    service_rate: f64,    // μ
    service_variance: f64, // σ²
    utilization: f64,     // ρ
}

impl MG1Queue {
    pub fn new(arrival_rate: f64, service_rate: f64, service_variance: f64) -> Result<Self, String> {
        if arrival_rate >= service_rate {
            return Err("System must be stable (λ < μ)".to_string());
        }

        let utilization = arrival_rate / service_rate;

        Ok(Self {
            arrival_rate,
            service_rate,
            service_variance,
            utilization,
        })
    }

    // 计算平均队列长度（Pollaczek-Khinchine公式）
    pub fn average_queue_length(&self) -> f64 {
        let lambda_squared = self.arrival_rate.powi(2);
        let rho_squared = self.utilization.powi(2);

        (lambda_squared * self.service_variance + rho_squared) /
        (2.0 * (1.0 - self.utilization))
    }

    // 计算平均等待时间
    pub fn average_waiting_time(&self) -> f64 {
        self.average_queue_length() / self.arrival_rate
    }

    // 计算平均响应时间
    pub fn average_response_time(&self) -> f64 {
        self.average_waiting_time() + 1.0 / self.service_rate
    }

    // 计算服务时间变异系数
    pub fn coefficient_of_variation(&self) -> f64 {
        self.service_variance.sqrt() / (1.0 / self.service_rate)
    }

    // 计算Pollaczek-Khinchine公式的简化形式
    pub fn pollaczek_khinchine_simplified(&self) -> f64 {
        let cv_squared = self.coefficient_of_variation().powi(2);
        self.utilization.powi(2) * (1.0 + cv_squared) /
        (2.0 * (1.0 - self.utilization))
    }
}
```

### G/G/1队列模型

#### 模型定义3

G/G/1队列模型假设：

- 到达过程为一般分布（G）
- 服务时间为一般分布（G）
- 单服务器（1）

#### Kingman公式

**平均等待时间**:
$$W_q \approx \frac{\rho}{1-\rho} \cdot \frac{C_a^2 + C_s^2}{2} \cdot \frac{1}{\mu}$$

其中：

- $C_a^2$: 到达过程变异系数平方
- $C_s^2$: 服务过程变异系数平方

#### 实现2

```rust
// G/G/1队列模型
pub struct GG1Queue {
    arrival_rate: f64,    // λ
    service_rate: f64,    // μ
    arrival_variance: f64, // 到达过程方差
    service_variance: f64, // 服务过程方差
    utilization: f64,     // ρ
}

impl GG1Queue {
    pub fn new(
        arrival_rate: f64,
        service_rate: f64,
        arrival_variance: f64,
        service_variance: f64
    ) -> Result<Self, String> {
        if arrival_rate >= service_rate {
            return Err("System must be stable (λ < μ)".to_string());
        }

        let utilization = arrival_rate / service_rate;

        Ok(Self {
            arrival_rate,
            service_rate,
            arrival_variance,
            service_variance,
            utilization,
        })
    }

    // 计算到达过程变异系数平方
    pub fn arrival_coefficient_of_variation_squared(&self) -> f64 {
        let arrival_mean = 1.0 / self.arrival_rate;
        self.arrival_variance / arrival_mean.powi(2)
    }

    // 计算服务过程变异系数平方
    pub fn service_coefficient_of_variation_squared(&self) -> f64 {
        let service_mean = 1.0 / self.service_rate;
        self.service_variance / service_mean.powi(2)
    }

    // 计算平均等待时间（Kingman公式）
    pub fn average_waiting_time(&self) -> f64 {
        let ca_squared = self.arrival_coefficient_of_variation_squared();
        let cs_squared = self.service_coefficient_of_variation_squared();

        self.utilization / (1.0 - self.utilization) *
        (ca_squared + cs_squared) / 2.0 *
        (1.0 / self.service_rate)
    }

    // 计算平均队列长度
    pub fn average_queue_length(&self) -> f64 {
        self.average_waiting_time() * self.arrival_rate
    }

    // 计算平均响应时间
    pub fn average_response_time(&self) -> f64 {
        self.average_waiting_time() + 1.0 / self.service_rate
    }

    // 计算系统稳定性指标
    pub fn stability_index(&self) -> f64 {
        let ca_squared = self.arrival_coefficient_of_variation_squared();
        let cs_squared = self.service_coefficient_of_variation_squared();

        self.utilization * (ca_squared + cs_squared) / 2.0
    }
}
```

## 🔗 网络拓扑模型

### 随机图模型

#### Erdős-Rényi模型

**模型定义**:

- $n$个节点
- 每条边以概率$p$独立存在
- 总边数期望: $E[E] = \binom{n}{2}p$

**度分布**:
$$P(k) = \binom{n-1}{k}p^k(1-p)^{n-1-k}$$

#### 实现3

```rust
// 随机图模型
pub struct RandomGraph {
    nodes: usize,
    edge_probability: f64,
    edges: Vec<(usize, usize)>,
}

impl RandomGraph {
    pub fn new(nodes: usize, edge_probability: f64) -> Self {
        Self {
            nodes,
            edge_probability,
            edges: Vec::new(),
        }
    }

    // 生成随机图
    pub fn generate(&mut self) {
        self.edges.clear();

        for i in 0..self.nodes {
            for j in i+1..self.nodes {
                if rand::random::<f64>() < self.edge_probability {
                    self.edges.push((i, j));
                }
            }
        }
    }

    // 计算平均度数
    pub fn average_degree(&self) -> f64 {
        (2.0 * self.edges.len() as f64) / self.nodes as f64
    }

    // 计算聚类系数
    pub fn clustering_coefficient(&self) -> f64 {
        let mut total_clustering = 0.0;
        let mut nodes_with_neighbors = 0;

        for node in 0..self.nodes {
            let neighbors = self.get_neighbors(node);
            if neighbors.len() >= 2 {
                let possible_edges = neighbors.len() * (neighbors.len() - 1) / 2;
                let actual_edges = self.count_edges_between_neighbors(&neighbors);

                if possible_edges > 0 {
                    total_clustering += actual_edges as f64 / possible_edges as f64;
                    nodes_with_neighbors += 1;
                }
            }
        }

        if nodes_with_neighbors > 0 {
            total_clustering / nodes_with_neighbors as f64
        } else {
            0.0
        }
    }

    // 计算路径长度
    pub fn average_path_length(&self) -> f64 {
        let mut total_length = 0.0;
        let mut path_count = 0;

        for i in 0..self.nodes {
            for j in i+1..self.nodes {
                if let Some(length) = self.shortest_path_length(i, j) {
                    total_length += length as f64;
                    path_count += 1;
                }
            }
        }

        if path_count > 0 {
            total_length / path_count as f64
        } else {
            0.0
        }
    }

    // 获取邻居节点
    fn get_neighbors(&self, node: usize) -> Vec<usize> {
        let mut neighbors = Vec::new();

        for &(u, v) in &self.edges {
            if u == node {
                neighbors.push(v);
            } else if v == node {
                neighbors.push(u);
            }
        }

        neighbors
    }

    // 计算邻居间的边数
    fn count_edges_between_neighbors(&self, neighbors: &[usize]) -> usize {
        let mut count = 0;

        for i in 0..neighbors.len() {
            for j in i+1..neighbors.len() {
                if self.has_edge(neighbors[i], neighbors[j]) {
                    count += 1;
                }
            }
        }

        count
    }

    // 检查是否存在边
    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.edges.contains(&(u, v)) || self.edges.contains(&(v, u))
    }

    // 计算最短路径长度
    fn shortest_path_length(&self, start: usize, end: usize) -> Option<usize> {
        if start == end {
            return Some(0);
        }

        let mut visited = vec![false; self.nodes];
        let mut queue = std::collections::VecDeque::new();
        let mut distances = vec![0; self.nodes];

        queue.push_back(start);
        visited[start] = true;

        while let Some(current) = queue.pop_front() {
            let neighbors = self.get_neighbors(current);

            for neighbor in neighbors {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    distances[neighbor] = distances[current] + 1;

                    if neighbor == end {
                        return Some(distances[neighbor]);
                    }

                    queue.push_back(neighbor);
                }
            }
        }

        None
    }
}
```

### 小世界网络模型

#### Watts-Strogatz模型

**模型定义**:

1. 从规则环开始，每个节点连接到$k$个最近邻居
2. 以概率$p$重连每条边

**聚类系数**:
$$C(p) = C(0)(1-p)^3$$

**路径长度**:
$$L(p) \approx \frac{n}{2k}f(pn)$$

其中$f(x)$是重连参数$x$的函数。

#### 实现6

```rust
// 小世界网络模型
pub struct SmallWorldNetwork {
    nodes: usize,
    k: usize,
    rewire_probability: f64,
    edges: Vec<(usize, usize)>,
}

impl SmallWorldNetwork {
    pub fn new(nodes: usize, k: usize, rewire_probability: f64) -> Self {
        Self {
            nodes,
            k,
            rewire_probability,
            edges: Vec::new(),
        }
    }

    // 生成小世界网络
    pub fn generate(&mut self) {
        self.edges.clear();

        // 第一步：创建规则环
        for i in 0..self.nodes {
            for j in 1..=self.k/2 {
                let neighbor = (i + j) % self.nodes;
                self.edges.push((i, neighbor));
            }
        }

        // 第二步：重连边
        let mut edges_to_rewire = Vec::new();

        for (i, &(u, v)) in self.edges.iter().enumerate() {
            if rand::random::<f64>() < self.rewire_probability {
                edges_to_rewire.push(i);
            }
        }

        for edge_index in edges_to_rewire {
            let (u, _) = self.edges[edge_index];

            // 选择新的目标节点
            let mut new_v = rand::random::<usize>() % self.nodes;
            while new_v == u || self.has_edge(u, new_v) {
                new_v = rand::random::<usize>() % self.nodes;
            }

            self.edges[edge_index] = (u, new_v);
        }
    }

    // 计算聚类系数
    pub fn clustering_coefficient(&self) -> f64 {
        let mut total_clustering = 0.0;
        let mut nodes_with_neighbors = 0;

        for node in 0..self.nodes {
            let neighbors = self.get_neighbors(node);
            if neighbors.len() >= 2 {
                let possible_edges = neighbors.len() * (neighbors.len() - 1) / 2;
                let actual_edges = self.count_edges_between_neighbors(&neighbors);

                if possible_edges > 0 {
                    total_clustering += actual_edges as f64 / possible_edges as f64;
                    nodes_with_neighbors += 1;
                }
            }
        }

        if nodes_with_neighbors > 0 {
            total_clustering / nodes_with_neighbors as f64
        } else {
            0.0
        }
    }

    // 计算理论聚类系数
    pub fn theoretical_clustering_coefficient(&self) -> f64 {
        let c0 = 3.0 * (self.k - 1) as f64 / (2.0 * (2.0 * self.k - 1) as f64);
        c0 * (1.0 - self.rewire_probability).powi(3)
    }

    // 计算平均路径长度
    pub fn average_path_length(&self) -> f64 {
        let mut total_length = 0.0;
        let mut path_count = 0;

        for i in 0..self.nodes {
            for j in i+1..self.nodes {
                if let Some(length) = self.shortest_path_length(i, j) {
                    total_length += length as f64;
                    path_count += 1;
                }
            }
        }

        if path_count > 0 {
            total_length / path_count as f64
        } else {
            0.0
        }
    }

    // 计算理论路径长度
    pub fn theoretical_path_length(&self) -> f64 {
        if self.rewire_probability == 0.0 {
            self.nodes as f64 / (4.0 * self.k as f64)
        } else {
            let x = self.rewire_probability * self.nodes as f64;
            self.nodes as f64 / (2.0 * self.k as f64) * self.function_f(x)
        }
    }

    // 辅助函数f(x)
    fn function_f(&self, x: f64) -> f64 {
        if x < 1.0 {
            1.0
        } else if x < 10.0 {
            1.0 / (4.0 * x) * (1.0 - x.exp())
        } else {
            1.0 / (4.0 * x)
        }
    }

    // 获取邻居节点
    fn get_neighbors(&self, node: usize) -> Vec<usize> {
        let mut neighbors = Vec::new();

        for &(u, v) in &self.edges {
            if u == node {
                neighbors.push(v);
            } else if v == node {
                neighbors.push(u);
            }
        }

        neighbors
    }

    // 计算邻居间的边数
    fn count_edges_between_neighbors(&self, neighbors: &[usize]) -> usize {
        let mut count = 0;

        for i in 0..neighbors.len() {
            for j in i+1..neighbors.len() {
                if self.has_edge(neighbors[i], neighbors[j]) {
                    count += 1;
                }
            }
        }

        count
    }

    // 检查是否存在边
    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.edges.contains(&(u, v)) || self.edges.contains(&(v, u))
    }

    // 计算最短路径长度
    fn shortest_path_length(&self, start: usize, end: usize) -> Option<usize> {
        if start == end {
            return Some(0);
        }

        let mut visited = vec![false; self.nodes];
        let mut queue = std::collections::VecDeque::new();
        let mut distances = vec![0; self.nodes];

        queue.push_back(start);
        visited[start] = true;

        while let Some(current) = queue.pop_front() {
            let neighbors = self.get_neighbors(current);

            for neighbor in neighbors {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    distances[neighbor] = distances[current] + 1;

                    if neighbor == end {
                        return Some(distances[neighbor]);
                    }

                    queue.push_back(neighbor);
                }
            }
        }

        None
    }
}
```

### 无标度网络模型

#### Barabási-Albert模型

**模型定义**:

1. 从$m_0$个节点开始
2. 每次添加一个新节点，连接到$m$个现有节点
3. 连接概率与节点度数成正比

**度分布**:
$$P(k) \sim k^{-3}$$

#### 实现5

```rust
// 无标度网络模型
pub struct ScaleFreeNetwork {
    nodes: usize,
    m0: usize,
    m: usize,
    edges: Vec<(usize, usize)>,
    degrees: Vec<usize>,
}

impl ScaleFreeNetwork {
    pub fn new(nodes: usize, m0: usize, m: usize) -> Result<Self, String> {
        if m0 >= nodes || m > m0 {
            return Err("Invalid parameters".to_string());
        }

        Ok(Self {
            nodes,
            m0,
            m,
            edges: Vec::new(),
            degrees: vec![0; nodes],
        })
    }

    // 生成无标度网络
    pub fn generate(&mut self) {
        self.edges.clear();
        self.degrees.fill(0);

        // 第一步：创建初始完全图
        for i in 0..self.m0 {
            for j in i+1..self.m0 {
                self.edges.push((i, j));
                self.degrees[i] += 1;
                self.degrees[j] += 1;
            }
        }

        // 第二步：添加新节点
        for new_node in self.m0..self.nodes {
            let mut connections = 0;
            let mut attempts = 0;
            let max_attempts = 1000;

            while connections < self.m && attempts < max_attempts {
                let target = self.select_target_node(new_node);
                if target.is_some() {
                    let target = target.unwrap();
                    self.edges.push((new_node, target));
                    self.degrees[new_node] += 1;
                    self.degrees[target] += 1;
                    connections += 1;
                }
                attempts += 1;
            }
        }
    }

    // 选择目标节点（优先连接）
    fn select_target_node(&self, new_node: usize) -> Option<usize> {
        let total_degree: usize = self.degrees.iter().sum();
        if total_degree == 0 {
            return None;
        }

        let random = rand::random::<f64>() * total_degree as f64;
        let mut cumulative = 0.0;

        for (node, &degree) in self.degrees.iter().enumerate() {
            cumulative += degree as f64;
            if cumulative >= random {
                return Some(node);
            }
        }

        None
    }

    // 计算度分布
    pub fn degree_distribution(&self) -> HashMap<usize, usize> {
        let mut distribution = HashMap::new();

        for &degree in &self.degrees {
            *distribution.entry(degree).or_insert(0) += 1;
        }

        distribution
    }

    // 计算度分布的幂律指数
    pub fn power_law_exponent(&self) -> f64 {
        let distribution = self.degree_distribution();
        let mut log_degrees = Vec::new();
        let mut log_counts = Vec::new();

        for (&degree, &count) in &distribution {
            if degree > 0 && count > 0 {
                log_degrees.push(degree as f64);
                log_counts.push(count as f64);
            }
        }

        if log_degrees.len() < 2 {
            return 0.0;
        }

        // 使用最小二乘法拟合幂律
        let n = log_degrees.len() as f64;
        let sum_log_degree: f64 = log_degrees.iter().sum();
        let sum_log_count: f64 = log_counts.iter().sum();
        let sum_log_degree_squared: f64 = log_degrees.iter().map(|x| x.powi(2)).sum();
        let sum_log_degree_log_count: f64 = log_degrees.iter()
            .zip(log_counts.iter())
            .map(|(x, y)| x * y)
            .sum();

        let slope = (n * sum_log_degree_log_count - sum_log_degree * sum_log_count) /
                   (n * sum_log_degree_squared - sum_log_degree.powi(2));

        -slope
    }

    // 计算平均度数
    pub fn average_degree(&self) -> f64 {
        self.degrees.iter().sum::<usize>() as f64 / self.nodes as f64
    }

    // 计算最大度数
    pub fn max_degree(&self) -> usize {
        self.degrees.iter().max().copied().unwrap_or(0)
    }

    // 计算度相关性
    pub fn degree_correlation(&self) -> f64 {
        let mut numerator = 0.0;
        let mut denominator = 0.0;

        for &(u, v) in &self.edges {
            let degree_u = self.degrees[u] as f64;
            let degree_v = self.degrees[v] as f64;

            numerator += degree_u * degree_v;
            denominator += degree_u.powi(2) + degree_v.powi(2);
        }

        if denominator > 0.0 {
            2.0 * numerator / denominator
        } else {
            0.0
        }
    }
}
```

### 层次网络模型

#### 层次网络

**模型定义**:

- 网络具有层次结构
- 不同层次有不同的连接模式
- 上层节点连接下层节点

#### 实现7

```rust
// 层次网络模型
pub struct HierarchicalNetwork {
    levels: usize,
    nodes_per_level: Vec<usize>,
    edges: Vec<(usize, usize)>,
    level_assignments: Vec<usize>,
}

impl HierarchicalNetwork {
    pub fn new(levels: usize, nodes_per_level: Vec<usize>) -> Result<Self, String> {
        if levels != nodes_per_level.len() {
            return Err("Levels and nodes_per_level must have same length".to_string());
        }

        Ok(Self {
            levels,
            nodes_per_level,
            edges: Vec::new(),
            level_assignments: Vec::new(),
        })
    }

    // 生成层次网络
    pub fn generate(&mut self) {
        self.edges.clear();
        self.level_assignments.clear();

        let total_nodes: usize = self.nodes_per_level.iter().sum();
        self.level_assignments.resize(total_nodes, 0);

        // 分配节点到层次
        let mut node_id = 0;
        for (level, &count) in self.nodes_per_level.iter().enumerate() {
            for _ in 0..count {
                self.level_assignments[node_id] = level;
                node_id += 1;
            }
        }

        // 生成层次内连接
        self.generate_intra_level_connections();

        // 生成层次间连接
        self.generate_inter_level_connections();
    }

    // 生成层次内连接
    fn generate_intra_level_connections(&mut self) {
        let mut node_id = 0;

        for (level, &count) in self.nodes_per_level.iter().enumerate() {
            if count > 1 {
                // 在层次内创建连接
                for i in 0..count {
                    for j in i+1..count {
                        if rand::random::<f64>() < 0.3 { // 30%概率连接
                            self.edges.push((node_id + i, node_id + j));
                        }
                    }
                }
            }
            node_id += count;
        }
    }

    // 生成层次间连接
    fn generate_inter_level_connections(&mut self) {
        let mut node_id = 0;

        for (level, &count) in self.nodes_per_level.iter().enumerate() {
            if level > 0 {
                // 连接到上层
                let upper_level_start = node_id - self.nodes_per_level[level - 1];
                let upper_level_count = self.nodes_per_level[level - 1];

                for i in 0..count {
                    let current_node = node_id + i;

                    // 每个节点连接到上层的一些节点
                    let connections = (upper_level_count / 2).max(1);
                    for _ in 0..connections {
                        let target = upper_level_start + rand::random::<usize>() % upper_level_count;
                        self.edges.push((current_node, target));
                    }
                }
            }

            node_id += count;
        }
    }

    // 计算层次内聚类系数
    pub fn intra_level_clustering_coefficient(&self) -> Vec<f64> {
        let mut coefficients = Vec::new();
        let mut node_id = 0;

        for (level, &count) in self.nodes_per_level.iter().enumerate() {
            let mut total_clustering = 0.0;
            let mut nodes_with_neighbors = 0;

            for i in 0..count {
                let current_node = node_id + i;
                let neighbors = self.get_neighbors_in_level(current_node, level);

                if neighbors.len() >= 2 {
                    let possible_edges = neighbors.len() * (neighbors.len() - 1) / 2;
                    let actual_edges = self.count_edges_between_neighbors(&neighbors);

                    if possible_edges > 0 {
                        total_clustering += actual_edges as f64 / possible_edges as f64;
                        nodes_with_neighbors += 1;
                    }
                }
            }

            if nodes_with_neighbors > 0 {
                coefficients.push(total_clustering / nodes_with_neighbors as f64);
            } else {
                coefficients.push(0.0);
            }

            node_id += count;
        }

        coefficients
    }

    // 计算层次间连接密度
    pub fn inter_level_connection_density(&self) -> Vec<Vec<f64>> {
        let mut densities = vec![vec![0.0; self.levels]; self.levels];

        for &(u, v) in &self.edges {
            let level_u = self.level_assignments[u];
            let level_v = self.level_assignments[v];

            if level_u != level_v {
                densities[level_u][level_v] += 1.0;
                densities[level_v][level_u] += 1.0;
            }
        }

        // 归一化
        for i in 0..self.levels {
            for j in 0..self.levels {
                if i != j {
                    let total_possible = self.nodes_per_level[i] * self.nodes_per_level[j];
                    densities[i][j] /= total_possible as f64;
                }
            }
        }

        densities
    }

    // 获取层次内的邻居
    fn get_neighbors_in_level(&self, node: usize, level: usize) -> Vec<usize> {
        let mut neighbors = Vec::new();

        for &(u, v) in &self.edges {
            if u == node && self.level_assignments[v] == level {
                neighbors.push(v);
            } else if v == node && self.level_assignments[u] == level {
                neighbors.push(u);
            }
        }

        neighbors
    }

    // 计算邻居间的边数
    fn count_edges_between_neighbors(&self, neighbors: &[usize]) -> usize {
        let mut count = 0;

        for i in 0..neighbors.len() {
            for j in i+1..neighbors.len() {
                if self.has_edge(neighbors[i], neighbors[j]) {
                    count += 1;
                }
            }
        }

        count
    }

    // 检查是否存在边
    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.edges.contains(&(u, v)) || self.edges.contains(&(v, u))
    }
}
```

## ⚡ 延迟分析模型

### 传播延迟模型

#### 传播延迟

**公式**:
$$D_{prop} = \frac{d}{c}$$

其中：

- $d$: 距离
- $c$: 传播速度（光速）

#### 实现8

```rust
// 传播延迟模型
pub struct PropagationDelayModel {
    distance: f64,        // 距离 (km)
    propagation_speed: f64, // 传播速度 (km/s)
}

impl PropagationDelayModel {
    pub fn new(distance: f64) -> Self {
        Self {
            distance,
            propagation_speed: 299792.458, // 光速 (km/s)
        }
    }

    // 计算传播延迟
    pub fn calculate_delay(&self) -> f64 {
        self.distance / self.propagation_speed
    }

    // 计算往返传播延迟
    pub fn calculate_round_trip_delay(&self) -> f64 {
        2.0 * self.calculate_delay()
    }

    // 计算不同介质的传播延迟
    pub fn calculate_delay_in_medium(&self, medium: PropagationMedium) -> f64 {
        let speed = match medium {
            PropagationMedium::Vacuum => 299792.458,
            PropagationMedium::Air => 299702.547,
            PropagationMedium::Water => 225000.0,
            PropagationMedium::Glass => 200000.0,
            PropagationMedium::Copper => 200000.0,
        };

        self.distance / speed
    }

    // 计算延迟变化（由于温度、湿度等）
    pub fn calculate_delay_variation(&self, temperature: f64, humidity: f64) -> f64 {
        let base_delay = self.calculate_delay();
        let temperature_factor = 1.0 + (temperature - 20.0) * 0.0001;
        let humidity_factor = 1.0 + humidity * 0.00001;

        base_delay * temperature_factor * humidity_factor
    }
}

# [derive(Debug, Clone)]
pub enum PropagationMedium {
    Vacuum,
    Air,
    Water,
    Glass,
    Copper,
}
```

### 传输延迟模型

#### 传输延迟

**公式**:
$$D_{trans} = \frac{L}{R}$$

其中：

- $L$: 数据包长度 (bits)
- $R$: 传输速率 (bps)

#### 实现9

```rust
// 传输延迟模型
pub struct TransmissionDelayModel {
    packet_length: usize,  // 数据包长度 (bits)
    transmission_rate: f64, // 传输速率 (bps)
}

impl TransmissionDelayModel {
    pub fn new(packet_length: usize, transmission_rate: f64) -> Self {
        Self {
            packet_length,
            transmission_rate,
        }
    }

    // 计算传输延迟
    pub fn calculate_delay(&self) -> f64 {
        self.packet_length as f64 / self.transmission_rate
    }

    // 计算不同数据包大小的传输延迟
    pub fn calculate_delay_for_packet(&self, packet_length: usize) -> f64 {
        packet_length as f64 / self.transmission_rate
    }

    // 计算批量传输延迟
    pub fn calculate_batch_delay(&self, packet_count: usize) -> f64 {
        (self.packet_length * packet_count) as f64 / self.transmission_rate
    }

    // 计算有效传输速率（考虑开销）
    pub fn calculate_effective_rate(&self, overhead_percentage: f64) -> f64 {
        self.transmission_rate * (1.0 - overhead_percentage / 100.0)
    }

    // 计算传输效率
    pub fn calculate_efficiency(&self, useful_data: usize) -> f64 {
        useful_data as f64 / self.packet_length as f64
    }
}
```

### 处理延迟模型

#### 处理延迟

**公式**:
$$D_{proc} = \frac{C}{f}$$

其中：

- $C$: 处理周期数
- $f$: 处理器频率

#### 实现10

```rust
// 处理延迟模型
pub struct ProcessingDelayModel {
    processing_cycles: u64, // 处理周期数
    processor_frequency: f64, // 处理器频率 (Hz)
}

impl ProcessingDelayModel {
    pub fn new(processing_cycles: u64, processor_frequency: f64) -> Self {
        Self {
            processing_cycles,
            processor_frequency,
        }
    }

    // 计算处理延迟
    pub fn calculate_delay(&self) -> f64 {
        self.processing_cycles as f64 / self.processor_frequency
    }

    // 计算不同处理器的延迟
    pub fn calculate_delay_for_processor(&self, frequency: f64) -> f64 {
        self.processing_cycles as f64 / frequency
    }

    // 计算并行处理延迟
    pub fn calculate_parallel_delay(&self, cores: usize) -> f64 {
        self.calculate_delay() / cores as f64
    }

    // 计算缓存命中延迟
    pub fn calculate_cache_hit_delay(&self, cache_hit_rate: f64) -> f64 {
        let cache_hit_delay = self.calculate_delay() * 0.1; // 缓存命中延迟
        let cache_miss_delay = self.calculate_delay(); // 缓存未命中延迟

        cache_hit_rate * cache_hit_delay + (1.0 - cache_hit_rate) * cache_miss_delay
    }

    // 计算流水线处理延迟
    pub fn calculate_pipeline_delay(&self, pipeline_stages: usize) -> f64 {
        self.processing_cycles as f64 / (self.processor_frequency * pipeline_stages as f64)
    }
}
```

### 排队延迟模型

#### 排队延迟

**公式**:
$$D_{queue} = \frac{L_q}{\lambda}$$

其中：

- $L_q$: 平均队列长度
- $\lambda$: 到达率

#### 实现11

```rust
// 排队延迟模型
pub struct QueuingDelayModel {
    queue_length: f64,    // 平均队列长度
    arrival_rate: f64,    // 到达率
}

impl QueuingDelayModel {
    pub fn new(queue_length: f64, arrival_rate: f64) -> Self {
        Self {
            queue_length,
            arrival_rate,
        }
    }

    // 计算排队延迟
    pub fn calculate_delay(&self) -> f64 {
        self.queue_length / self.arrival_rate
    }

    // 计算不同队列长度的延迟
    pub fn calculate_delay_for_queue_length(&self, queue_length: f64) -> f64 {
        queue_length / self.arrival_rate
    }

    // 计算优先级队列延迟
    pub fn calculate_priority_queue_delay(&self, priority_levels: &[f64]) -> Vec<f64> {
        priority_levels.iter()
            .map(|&priority| self.calculate_delay() * priority)
            .collect()
    }

    // 计算加权公平队列延迟
    pub fn calculate_wfq_delay(&self, weights: &[f64]) -> Vec<f64> {
        let total_weight: f64 = weights.iter().sum();

        weights.iter()
            .map(|&weight| self.calculate_delay() * total_weight / weight)
            .collect()
    }

    // 计算随机早期检测延迟
    pub fn calculate_red_delay(&self, drop_probability: f64) -> f64 {
        self.calculate_delay() * (1.0 - drop_probability)
    }
}
```

## 📈 吞吐量模型

### TCP吞吐量模型

#### TCP吞吐量

**公式**:
$$Throughput = \frac{MSS \times 1.22}{RTT \times \sqrt{p}}$$

其中：

- $MSS$: 最大段大小
- $RTT$: 往返时间
- $p$: 丢包率

#### 实现12

```rust
// TCP吞吐量模型
pub struct TcpThroughputModel {
    mss: usize,           // 最大段大小 (bytes)
    rtt: f64,             // 往返时间 (seconds)
    packet_loss_rate: f64, // 丢包率
    window_size: usize,   // 窗口大小 (bytes)
    bandwidth: f64,       // 带宽 (bps)
}

impl TcpThroughputModel {
    pub fn new(mss: usize, rtt: f64, packet_loss_rate: f64) -> Self {
        Self {
            mss,
            rtt,
            packet_loss_rate,
            window_size: 65536, // 默认窗口大小
            bandwidth: 1e9,     // 默认带宽 1Gbps
        }
    }

    // 计算TCP吞吐量（简化模型）
    pub fn calculate_throughput(&self) -> f64 {
        if self.packet_loss_rate <= 0.0 {
            return 0.0;
        }

        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.22 / (self.rtt * self.packet_loss_rate.sqrt())
    }

    // 计算窗口限制的吞吐量
    pub fn calculate_window_limited_throughput(&self) -> f64 {
        (self.window_size * 8) as f64 / self.rtt
    }

    // 计算带宽限制的吞吐量
    pub fn calculate_bandwidth_limited_throughput(&self) -> f64 {
        self.bandwidth
    }

    // 计算实际吞吐量（考虑所有限制）
    pub fn calculate_actual_throughput(&self) -> f64 {
        let tcp_throughput = self.calculate_throughput();
        let window_limited = self.calculate_window_limited_throughput();
        let bandwidth_limited = self.calculate_bandwidth_limited_throughput();

        tcp_throughput.min(window_limited).min(bandwidth_limited)
    }

    // 计算不同RTT的吞吐量
    pub fn calculate_throughput_for_rtt(&self, rtt: f64) -> f64 {
        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.22 / (rtt * self.packet_loss_rate.sqrt())
    }

    // 计算不同丢包率的吞吐量
    pub fn calculate_throughput_for_loss_rate(&self, loss_rate: f64) -> f64 {
        if loss_rate <= 0.0 {
            return 0.0;
        }

        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.22 / (self.rtt * loss_rate.sqrt())
    }

    // 计算TCP Reno吞吐量
    pub fn calculate_reno_throughput(&self) -> f64 {
        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.22 / (self.rtt * self.packet_loss_rate.sqrt())
    }

    // 计算TCP Vegas吞吐量
    pub fn calculate_vegas_throughput(&self) -> f64 {
        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.0 / (self.rtt * self.packet_loss_rate.sqrt())
    }

    // 计算TCP CUBIC吞吐量
    pub fn calculate_cubic_throughput(&self) -> f64 {
        let mss_bits = (self.mss * 8) as f64;
        mss_bits * 1.0 / (self.rtt * self.packet_loss_rate.sqrt())
    }
}
```

### UDP吞吐量模型

#### UDP吞吐量

**公式**:
$$Throughput = \frac{Data\_Rate}{1 + Overhead\_Ratio}$$

#### 实现13

```rust
// UDP吞吐量模型
pub struct UdpThroughputModel {
    data_rate: f64,        // 数据速率 (bps)
    overhead_ratio: f64,   // 开销比例
    packet_size: usize,    // 数据包大小 (bytes)
    header_size: usize,    // 头部大小 (bytes)
}

impl UdpThroughputModel {
    pub fn new(data_rate: f64, packet_size: usize, header_size: usize) -> Self {
        let overhead_ratio = header_size as f64 / packet_size as f64;

        Self {
            data_rate,
            overhead_ratio,
            packet_size,
            header_size,
        }
    }

    // 计算UDP吞吐量
    pub fn calculate_throughput(&self) -> f64 {
        self.data_rate / (1.0 + self.overhead_ratio)
    }

    // 计算有效数据吞吐量
    pub fn calculate_effective_throughput(&self) -> f64 {
        let total_size = self.packet_size + self.header_size;
        let data_ratio = self.packet_size as f64 / total_size as f64;

        self.calculate_throughput() * data_ratio
    }

    // 计算不同数据包大小的吞吐量
    pub fn calculate_throughput_for_packet_size(&self, packet_size: usize) -> f64 {
        let overhead_ratio = self.header_size as f64 / packet_size as f64;
        self.data_rate / (1.0 + overhead_ratio)
    }

    // 计算最优数据包大小
    pub fn calculate_optimal_packet_size(&self) -> usize {
        // 简化计算：假设开销固定
        self.packet_size
    }

    // 计算UDP over TCP吞吐量
    pub fn calculate_udp_over_tcp_throughput(&self, tcp_overhead: f64) -> f64 {
        self.calculate_throughput() * (1.0 - tcp_overhead)
    }
}
```

### HTTP吞吐量模型

#### HTTP吞吐量

**公式**:
$$Throughput = \frac{Response\_Size}{Response\_Time}$$

#### 实现14

```rust
// HTTP吞吐量模型
pub struct HttpThroughputModel {
    response_size: usize,  // 响应大小 (bytes)
    response_time: f64,    // 响应时间 (seconds)
    connection_count: usize, // 连接数
    concurrent_requests: usize, // 并发请求数
}

impl HttpThroughputModel {
    pub fn new(response_size: usize, response_time: f64) -> Self {
        Self {
            response_size,
            response_time,
            connection_count: 1,
            concurrent_requests: 1,
        }
    }

    // 计算HTTP吞吐量
    pub fn calculate_throughput(&self) -> f64 {
        (self.response_size * 8) as f64 / self.response_time
    }

    // 计算并发吞吐量
    pub fn calculate_concurrent_throughput(&self) -> f64 {
        self.calculate_throughput() * self.concurrent_requests as f64
    }

    // 计算连接池吞吐量
    pub fn calculate_connection_pool_throughput(&self) -> f64 {
        self.calculate_throughput() * self.connection_count as f64
    }

    // 计算HTTP/2多路复用吞吐量
    pub fn calculate_http2_throughput(&self, multiplexing_factor: f64) -> f64 {
        self.calculate_throughput() * multiplexing_factor
    }

    // 计算压缩后的吞吐量
    pub fn calculate_compressed_throughput(&self, compression_ratio: f64) -> f64 {
        self.calculate_throughput() / compression_ratio
    }

    // 计算缓存命中吞吐量
    pub fn calculate_cached_throughput(&self, cache_hit_rate: f64) -> f64 {
        let cached_response_time = self.response_time * 0.1; // 缓存响应时间
        let cached_throughput = (self.response_size * 8) as f64 / cached_response_time;

        cache_hit_rate * cached_throughput + (1.0 - cache_hit_rate) * self.calculate_throughput()
    }
}
```

### WebSocket吞吐量模型

#### WebSocket吞吐量

**公式**:
$$Throughput = \frac{Message\_Size}{Transmission\_Time}$$

#### 实现15

```rust
// WebSocket吞吐量模型
pub struct WebSocketThroughputModel {
    message_size: usize,   // 消息大小 (bytes)
    transmission_time: f64, // 传输时间 (seconds)
    frame_overhead: usize,  // 帧开销 (bytes)
    connection_count: usize, // 连接数
}

impl WebSocketThroughputModel {
    pub fn new(message_size: usize, transmission_time: f64) -> Self {
        Self {
            message_size,
            transmission_time,
            frame_overhead: 2, // 最小帧开销
            connection_count: 1,
        }
    }

    // 计算WebSocket吞吐量
    pub fn calculate_throughput(&self) -> f64 {
        (self.message_size * 8) as f64 / self.transmission_time
    }

    // 计算有效吞吐量（考虑帧开销）
    pub fn calculate_effective_throughput(&self) -> f64 {
        let total_size = self.message_size + self.frame_overhead;
        let data_ratio = self.message_size as f64 / total_size as f64;

        self.calculate_throughput() * data_ratio
    }

    // 计算多连接吞吐量
    pub fn calculate_multi_connection_throughput(&self) -> f64 {
        self.calculate_throughput() * self.connection_count as f64
    }

    // 计算不同消息大小的吞吐量
    pub fn calculate_throughput_for_message_size(&self, message_size: usize) -> f64 {
        (message_size * 8) as f64 / self.transmission_time
    }

    // 计算二进制消息吞吐量
    pub fn calculate_binary_throughput(&self) -> f64 {
        self.calculate_effective_throughput()
    }

    // 计算文本消息吞吐量
    pub fn calculate_text_throughput(&self) -> f64 {
        // 文本消息可能有编码开销
        self.calculate_effective_throughput() * 0.9
    }
}
```

## 🔒 可靠性模型

### 故障模型

#### 故障率模型

**公式**:
$$\lambda(t) = \lambda_0 e^{-\alpha t}$$

其中：

- $\lambda_0$: 初始故障率
- $\alpha$: 故障率衰减系数

#### 实现16

```rust
// 故障模型
pub struct FailureModel {
    initial_failure_rate: f64, // 初始故障率
    decay_coefficient: f64,    // 衰减系数
    time: f64,                // 时间
}

impl FailureModel {
    pub fn new(initial_failure_rate: f64, decay_coefficient: f64) -> Self {
        Self {
            initial_failure_rate,
            decay_coefficient,
            time: 0.0,
        }
    }

    // 计算当前故障率
    pub fn calculate_failure_rate(&self) -> f64 {
        self.initial_failure_rate * (-self.decay_coefficient * self.time).exp()
    }

    // 计算可靠性
    pub fn calculate_reliability(&self) -> f64 {
        (-self.initial_failure_rate / self.decay_coefficient *
         (1.0 - (-self.decay_coefficient * self.time).exp())).exp()
    }

    // 计算平均故障间隔时间
    pub fn calculate_mtbf(&self) -> f64 {
        1.0 / self.calculate_failure_rate()
    }

    // 计算故障概率
    pub fn calculate_failure_probability(&self, time_interval: f64) -> f64 {
        1.0 - (-self.calculate_failure_rate() * time_interval).exp()
    }

    // 更新时间
    pub fn update_time(&mut self, new_time: f64) {
        self.time = new_time;
    }
}
```

### 恢复模型

#### 恢复时间模型

**公式**:

$$
T_{recovery} = T_{detection} + T_{isolation} + T_{repair}
$$

#### 实现17

```rust
// 恢复模型
pub struct RecoveryModel {
    detection_time: f64,    // 检测时间
    isolation_time: f64,    // 隔离时间
    repair_time: f64,      // 修复时间
    recovery_probability: f64, // 恢复概率
}

impl RecoveryModel {
    pub fn new(detection_time: f64, isolation_time: f64, repair_time: f64) -> Self {
        Self {
            detection_time,
            isolation_time,
            repair_time,
            recovery_probability: 0.95, // 默认恢复概率
        }
    }

    // 计算总恢复时间
    pub fn calculate_total_recovery_time(&self) -> f64 {
        self.detection_time + self.isolation_time + self.repair_time
    }

    // 计算平均恢复时间
    pub fn calculate_mean_recovery_time(&self) -> f64 {
        self.calculate_total_recovery_time() * self.recovery_probability
    }

    // 计算恢复时间分布
    pub fn calculate_recovery_time_distribution(&self) -> Vec<f64> {
        let total_time = self.calculate_total_recovery_time();
        let mut distribution = Vec::new();

        for i in 0..100 {
            let time = total_time * i as f64 / 100.0;
            let probability = self.calculate_recovery_probability(time);
            distribution.push(probability);
        }

        distribution
    }

    // 计算恢复概率
    pub fn calculate_recovery_probability(&self, time: f64) -> f64 {
        if time < self.detection_time {
            0.0
        } else if time < self.detection_time + self.isolation_time {
            0.5
        } else if time < self.calculate_total_recovery_time() {
            0.8
        } else {
            self.recovery_probability
        }
    }

    // 计算可用性
    pub fn calculate_availability(&self, failure_rate: f64) -> f64 {
        let mttr = self.calculate_mean_recovery_time();
        let mtbf = 1.0 / failure_rate;

        mtbf / (mtbf + mttr)
    }
}
```

### 冗余模型

#### N+1冗余模型

**公式**:
$$R_{system} = 1 - (1 - R_{component})^N$$

#### 实现18

```rust
// 冗余模型
pub struct RedundancyModel {
    component_reliability: f64, // 组件可靠性
    redundancy_level: usize,     // 冗余级别
    redundancy_type: RedundancyType, // 冗余类型
}

# [derive(Debug, Clone)]
pub enum RedundancyType {
    Active,    // 主动冗余
    Passive,   // 被动冗余
    Standby,   // 备用冗余
}

impl RedundancyModel {
    pub fn new(component_reliability: f64, redundancy_level: usize, redundancy_type: RedundancyType) -> Self {
        Self {
            component_reliability,
            redundancy_level,
            redundancy_type,
        }
    }

    // 计算系统可靠性
    pub fn calculate_system_reliability(&self) -> f64 {
        match self.redundancy_type {
            RedundancyType::Active => {
                // 主动冗余：所有组件同时工作
                1.0 - (1.0 - self.component_reliability).powi(self.redundancy_level as i32)
            }
            RedundancyType::Passive => {
                // 被动冗余：一个组件工作，其他备用
                self.component_reliability
            }
            RedundancyType::Standby => {
                // 备用冗余：按顺序切换
                self.component_reliability.powi(self.redundancy_level as i32)
            }
        }
    }

    // 计算冗余效率
    pub fn calculate_redundancy_efficiency(&self) -> f64 {
        let single_reliability = self.component_reliability;
        let redundant_reliability = self.calculate_system_reliability();

        (redundant_reliability - single_reliability) / single_reliability
    }

    // 计算最优冗余级别
    pub fn calculate_optimal_redundancy_level(&self, target_reliability: f64) -> usize {
        let mut level = 1;

        while self.calculate_system_reliability_for_level(level) < target_reliability {
            level += 1;
        }

        level
    }

    // 计算指定级别的系统可靠性
    fn calculate_system_reliability_for_level(&self, level: usize) -> f64 {
        match self.redundancy_type {
            RedundancyType::Active => {
                1.0 - (1.0 - self.component_reliability).powi(level as i32)
            }
            RedundancyType::Passive => {
                self.component_reliability
            }
            RedundancyType::Standby => {
                self.component_reliability.powi(level as i32)
            }
        }
    }
}
```

### 一致性模型

#### 强一致性模型

**公式**:
$$C_{strong} = \frac{Consistent\_Reads}{Total\_Reads}$$

#### 实现19

```rust
// 一致性模型
pub struct ConsistencyModel {
    consistent_reads: u64,  // 一致读取数
    total_reads: u64,      // 总读取数
    write_latency: f64,    // 写入延迟
    read_latency: f64,     // 读取延迟
}

impl ConsistencyModel {
    pub fn new() -> Self {
        Self {
            consistent_reads: 0,
            total_reads: 0,
            write_latency: 0.0,
            read_latency: 0.0,
        }
    }

    // 计算强一致性
    pub fn calculate_strong_consistency(&self) -> f64 {
        if self.total_reads == 0 {
            0.0
        } else {
            self.consistent_reads as f64 / self.total_reads as f64
        }
    }

    // 计算最终一致性
    pub fn calculate_eventual_consistency(&self, propagation_delay: f64) -> f64 {
        let time_factor = (-propagation_delay).exp();
        self.calculate_strong_consistency() * time_factor
    }

    // 计算因果一致性
    pub fn calculate_causal_consistency(&self, dependency_ratio: f64) -> f64 {
        self.calculate_strong_consistency() * dependency_ratio
    }

    // 计算会话一致性
    pub fn calculate_session_consistency(&self, session_duration: f64) -> f64 {
        let session_factor = (-session_duration).exp();
        self.calculate_strong_consistency() * session_factor
    }

    // 更新读取统计
    pub fn update_read_stats(&mut self, consistent: bool) {
        self.total_reads += 1;
        if consistent {
            self.consistent_reads += 1;
        }
    }

    // 计算一致性延迟
    pub fn calculate_consistency_latency(&self) -> f64 {
        self.write_latency + self.read_latency
    }
}
```

## 🎯 优化模型

### 负载均衡模型

#### 负载均衡算法

**轮询算法**:
$$server_i = (current + i) \bmod n$$

**加权轮询算法**:
$$P_i = \frac{w_i}{\sum_{j=1}^{n} w_j}$$

#### 实现20

```rust
// 负载均衡模型
pub struct LoadBalancingModel {
    servers: Vec<Server>,
    algorithm: LoadBalancingAlgorithm,
    current_index: usize,
}

# [derive(Debug, Clone)]
pub struct Server {
    pub id: usize,
    pub weight: f64,
    pub current_load: f64,
    pub capacity: f64,
    pub response_time: f64,
}

# [derive(Debug, Clone)]
pub enum LoadBalancingAlgorithm {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    LeastResponseTime,
    LeastLoad,
}

impl LoadBalancingModel {
    pub fn new(servers: Vec<Server>, algorithm: LoadBalancingAlgorithm) -> Self {
        Self {
            servers,
            algorithm,
            current_index: 0,
        }
    }

    // 选择服务器
    pub fn select_server(&mut self) -> Option<&Server> {
        match self.algorithm {
            LoadBalancingAlgorithm::RoundRobin => {
                let server = &self.servers[self.current_index];
                self.current_index = (self.current_index + 1) % self.servers.len();
                Some(server)
            }
            LoadBalancingAlgorithm::WeightedRoundRobin => {
                self.select_weighted_server()
            }
            LoadBalancingAlgorithm::LeastConnections => {
                self.servers.iter().min_by(|a, b| a.current_load.partial_cmp(&b.current_load).unwrap())
            }
            LoadBalancingAlgorithm::LeastResponseTime => {
                self.servers.iter().min_by(|a, b| a.response_time.partial_cmp(&b.response_time).unwrap())
            }
            LoadBalancingAlgorithm::LeastLoad => {
                self.servers.iter().min_by(|a, b| (a.current_load / a.capacity).partial_cmp(&(b.current_load / b.capacity)).unwrap())
            }
        }
    }

    // 选择加权服务器
    fn select_weighted_server(&mut self) -> Option<&Server> {
        let total_weight: f64 = self.servers.iter().map(|s| s.weight).sum();
        let random = rand::random::<f64>() * total_weight;

        let mut cumulative = 0.0;
        for server in &self.servers {
            cumulative += server.weight;
            if cumulative >= random {
                return Some(server);
            }
        }

        self.servers.last()
    }

    // 计算负载均衡效率
    pub fn calculate_efficiency(&self) -> f64 {
        let loads: Vec<f64> = self.servers.iter().map(|s| s.current_load / s.capacity).collect();
        let mean_load = loads.iter().sum::<f64>() / loads.len() as f64;
        let variance = loads.iter().map(|&x| (x - mean_load).powi(2)).sum::<f64>() / loads.len() as f64;

        1.0 - variance.sqrt() / mean_load
    }

    // 计算系统吞吐量
    pub fn calculate_throughput(&self) -> f64 {
        self.servers.iter().map(|s| s.capacity - s.current_load).sum()
    }

    // 计算平均响应时间
    pub fn calculate_average_response_time(&self) -> f64 {
        let total_weight: f64 = self.servers.iter().map(|s| s.weight).sum();
        self.servers.iter()
            .map(|s| s.response_time * s.weight / total_weight)
            .sum()
    }
}
```

### 缓存模型

#### LRU缓存模型

**公式**:
$$Hit\_Rate = \frac{Cache\_Hits}{Total\_Requests}$$

#### 实现21

```rust
// 缓存模型
pub struct CacheModel {
    cache_size: usize,
    hit_count: u64,
    miss_count: u64,
    access_pattern: Vec<usize>,
    cache_policy: CachePolicy,
}

# [derive(Debug, Clone)]
pub enum CachePolicy {
    LRU,
    LFU,
    FIFO,
    Random,
}

impl CacheModel {
    pub fn new(cache_size: usize, cache_policy: CachePolicy) -> Self {
        Self {
            cache_size,
            hit_count: 0,
            miss_count: 0,
            access_pattern: Vec::new(),
            cache_policy,
        }
    }

    // 计算缓存命中率
    pub fn calculate_hit_rate(&self) -> f64 {
        let total_requests = self.hit_count + self.miss_count;
        if total_requests == 0 {
            0.0
        } else {
            self.hit_count as f64 / total_requests as f64
        }
    }

    // 计算缓存未命中率
    pub fn calculate_miss_rate(&self) -> f64 {
        1.0 - self.calculate_hit_rate()
    }

    // 计算平均访问时间
    pub fn calculate_average_access_time(&self, cache_access_time: f64, memory_access_time: f64) -> f64 {
        let hit_rate = self.calculate_hit_rate();
        hit_rate * cache_access_time + (1.0 - hit_rate) * memory_access_time
    }

    // 计算缓存效率
    pub fn calculate_efficiency(&self) -> f64 {
        let hit_rate = self.calculate_hit_rate();
        let cache_utilization = self.cache_size as f64 / self.access_pattern.len() as f64;

        hit_rate * cache_utilization
    }

    // 模拟缓存访问
    pub fn simulate_access(&mut self, item: usize) -> bool {
        self.access_pattern.push(item);

        // 简化的缓存模拟
        let hit = self.access_pattern.len() <= self.cache_size ||
                  self.access_pattern.iter().rev().take(self.cache_size).any(|&x| x == item);

        if hit {
            self.hit_count += 1;
        } else {
            self.miss_count += 1;
        }

        hit
    }

    // 计算最优缓存大小
    pub fn calculate_optimal_cache_size(&self, cost_per_unit: f64, benefit_per_hit: f64) -> usize {
        let mut optimal_size = 0;
        let mut max_benefit = 0.0;

        for size in 1..=self.cache_size {
            let cost = size as f64 * cost_per_unit;
            let benefit = self.calculate_benefit_for_size(size) * benefit_per_hit;
            let net_benefit = benefit - cost;

            if net_benefit > max_benefit {
                max_benefit = net_benefit;
                optimal_size = size;
            }
        }

        optimal_size
    }

    // 计算指定大小的收益
    fn calculate_benefit_for_size(&self, size: usize) -> f64 {
        // 简化计算：假设收益与缓存大小成正比
        size as f64 / self.cache_size as f64
    }
}
```

### 压缩模型

#### 压缩算法模型

**公式**:
$$Compression\_Ratio = \frac{Original\_Size}{Compressed\_Size}$$

#### 实现22

```rust
// 压缩模型
pub struct CompressionModel {
    original_size: usize,
    compressed_size: usize,
    compression_algorithm: CompressionAlgorithm,
    compression_time: f64,
    decompression_time: f64,
}

# [derive(Debug, Clone)]
pub enum CompressionAlgorithm {
    Gzip,
    Deflate,
    Brotli,
    LZ4,
    Zstd,
}

impl CompressionModel {
    pub fn new(original_size: usize, compressed_size: usize, algorithm: CompressionAlgorithm) -> Self {
        Self {
            original_size,
            compressed_size,
            compression_algorithm: algorithm,
            compression_time: 0.0,
            decompression_time: 0.0,
        }
    }

    // 计算压缩比
    pub fn calculate_compression_ratio(&self) -> f64 {
        self.original_size as f64 / self.compressed_size as f64
    }

    // 计算压缩效率
    pub fn calculate_compression_efficiency(&self) -> f64 {
        1.0 - self.compressed_size as f64 / self.original_size as f64
    }

    // 计算压缩速度
    pub fn calculate_compression_speed(&self) -> f64 {
        if self.compression_time > 0.0 {
            self.original_size as f64 / self.compression_time
        } else {
            0.0
        }
    }

    // 计算解压缩速度
    pub fn calculate_decompression_speed(&self) -> f64 {
        if self.decompression_time > 0.0 {
            self.compressed_size as f64 / self.decompression_time
        } else {
            0.0
        }
    }

    // 计算总体性能
    pub fn calculate_overall_performance(&self) -> f64 {
        let compression_ratio = self.calculate_compression_ratio();
        let compression_speed = self.calculate_compression_speed();
        let decompression_speed = self.calculate_decompression_speed();

        compression_ratio * compression_speed * decompression_speed
    }

    // 计算不同算法的性能
    pub fn compare_algorithms(&self, algorithms: &[CompressionAlgorithm]) -> Vec<f64> {
        algorithms.iter()
            .map(|algorithm| self.calculate_algorithm_performance(*algorithm))
            .collect()
    }

    // 计算指定算法的性能
    fn calculate_algorithm_performance(&self, algorithm: CompressionAlgorithm) -> f64 {
        match algorithm {
            CompressionAlgorithm::Gzip => 0.8,
            CompressionAlgorithm::Deflate => 0.7,
            CompressionAlgorithm::Brotli => 0.9,
            CompressionAlgorithm::LZ4 => 0.6,
            CompressionAlgorithm::Zstd => 0.85,
        }
    }

    // 计算最优压缩级别
    pub fn calculate_optimal_compression_level(&self, target_ratio: f64) -> usize {
        let current_ratio = self.calculate_compression_ratio();

        if current_ratio >= target_ratio {
            1
        } else {
            (target_ratio / current_ratio).ceil() as usize
        }
    }
}
```

### 路由优化模型

#### 最短路径算法

**Dijkstra算法**:
$$d[v] = \min(d[v], d[u] + w(u,v))$$

#### 实现23

```rust
// 路由优化模型
pub struct RoutingOptimizationModel {
    graph: Vec<Vec<f64>>,
    nodes: usize,
    algorithm: RoutingAlgorithm,
}

# [derive(Debug, Clone)]
pub enum RoutingAlgorithm {
    Dijkstra,
    BellmanFord,
    FloydWarshall,
    AStar,
}

impl RoutingOptimizationModel {
    pub fn new(graph: Vec<Vec<f64>>, algorithm: RoutingAlgorithm) -> Self {
        let nodes = graph.len();
        Self {
            graph,
            nodes,
            algorithm,
        }
    }

    // 计算最短路径
    pub fn calculate_shortest_path(&self, source: usize, destination: usize) -> Option<f64> {
        match self.algorithm {
            RoutingAlgorithm::Dijkstra => self.dijkstra(source, destination),
            RoutingAlgorithm::BellmanFord => self.bellman_ford(source, destination),
            RoutingAlgorithm::FloydWarshall => self.floyd_warshall(source, destination),
            RoutingAlgorithm::AStar => self.a_star(source, destination),
        }
    }

    // Dijkstra算法
    fn dijkstra(&self, source: usize, destination: usize) -> Option<f64> {
        let mut distances = vec![f64::INFINITY; self.nodes];
        let mut visited = vec![false; self.nodes];

        distances[source] = 0.0;

        for _ in 0..self.nodes {
            let u = self.find_min_distance_vertex(&distances, &visited);
            if u == usize::MAX {
                break;
            }

            visited[u] = true;

            for v in 0..self.nodes {
                if !visited[v] && self.graph[u][v] > 0.0 {
                    let new_distance = distances[u] + self.graph[u][v];
                    if new_distance < distances[v] {
                        distances[v] = new_distance;
                    }
                }
            }
        }

        if distances[destination] == f64::INFINITY {
            None
        } else {
            Some(distances[destination])
        }
    }

    // Bellman-Ford算法
    fn bellman_ford(&self, source: usize, destination: usize) -> Option<f64> {
        let mut distances = vec![f64::INFINITY; self.nodes];
        distances[source] = 0.0;

        for _ in 0..self.nodes - 1 {
            for u in 0..self.nodes {
                for v in 0..self.nodes {
                    if self.graph[u][v] > 0.0 {
                        let new_distance = distances[u] + self.graph[u][v];
                        if new_distance < distances[v] {
                            distances[v] = new_distance;
                        }
                    }
                }
            }
        }

        if distances[destination] == f64::INFINITY {
            None
        } else {
            Some(distances[destination])
        }
    }

    // Floyd-Warshall算法
    fn floyd_warshall(&self, source: usize, destination: usize) -> Option<f64> {
        let mut distances = self.graph.clone();

        for k in 0..self.nodes {
            for i in 0..self.nodes {
                for j in 0..self.nodes {
                    if distances[i][k] != f64::INFINITY && distances[k][j] != f64::INFINITY {
                        let new_distance = distances[i][k] + distances[k][j];
                        if new_distance < distances[i][j] {
                            distances[i][j] = new_distance;
                        }
                    }
                }
            }
        }

        if distances[source][destination] == f64::INFINITY {
            None
        } else {
            Some(distances[source][destination])
        }
    }

    // A*算法
    fn a_star(&self, source: usize, destination: usize) -> Option<f64> {
        // 简化的A*实现
        self.dijkstra(source, destination)
    }

    // 查找最小距离顶点
    fn find_min_distance_vertex(&self, distances: &[f64], visited: &[bool]) -> usize {
        let mut min_distance = f64::INFINITY;
        let mut min_vertex = usize::MAX;

        for v in 0..self.nodes {
            if !visited[v] && distances[v] < min_distance {
                min_distance = distances[v];
                min_vertex = v;
            }
        }

        min_vertex
    }

    // 计算路由效率
    pub fn calculate_routing_efficiency(&self) -> f64 {
        let mut total_distance = 0.0;
        let mut path_count = 0;

        for i in 0..self.nodes {
            for j in 0..self.nodes {
                if i != j {
                    if let Some(distance) = self.calculate_shortest_path(i, j) {
                        total_distance += distance;
                        path_count += 1;
                    }
                }
            }
        }

        if path_count > 0 {
            total_distance / path_count as f64
        } else {
            0.0
        }
    }

    // 计算网络直径
    pub fn calculate_network_diameter(&self) -> f64 {
        let mut max_distance = 0.0;

        for i in 0..self.nodes {
            for j in 0..self.nodes {
                if i != j {
                    if let Some(distance) = self.calculate_shortest_path(i, j) {
                        max_distance = max_distance.max(distance);
                    }
                }
            }
        }

        max_distance
    }
}
```

## 📚 参考文献

1. Kleinrock, L. (1975). *Queueing Systems, Volume 1: Theory*. John Wiley & Sons.
2. Tanenbaum, A. S., & Wetherall, D. (2011). *Computer Networks*. Prentice Hall.
3. Barabási, A. L., & Albert, R. (1999). Emergence of scaling in random networks. *Science*, 286(5439), 509-512.
4. Watts, D. J., & Strogatz, S. H. (1998). Collective dynamics of 'small-world' networks. *Nature*, 393(6684), 440-442.
5. Floyd, S., & Jacobson, V. (1993). Random early detection gateways for congestion avoidance. *IEEE/ACM Transactions on networking*, 1(4), 397-413.
6. Allman, M., Paxson, V., & Stevens, W. (1999). TCP congestion control. *RFC 2581*.
7. Jacobson, V. (1988). Congestion avoidance and control. *ACM SIGCOMM Computer Communication Review*, 18(4), 314-329.
8. Padhye, J., Firoiu, V., Towsley, D., & Kurose, J. (2000). Modeling TCP throughput: A simple model and its empirical validation. *ACM SIGCOMM Computer Communication Review*, 30(4), 303-314.

---

**网络性能模型版本**: v1.0  
**最后更新**: 2025年1月  
**维护者**: C10 Networks 性能分析团队
