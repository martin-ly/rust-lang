# 算法分类、模型与形式化体系

**版本**: 1.0.0  
**Rust版本**: 1.90+  
**Edition**: 2024  
**最后更新**: 2025-10-02

---

## 📖 目录

- [算法分类、模型与形式化体系](#算法分类模型与形式化体系)
  - [📖 目录](#-目录)
  - [1. 算法的形式化定义](#1-算法的形式化定义)
    - [1.1 基本定义](#11-基本定义)
    - [1.2 算法的数学表示](#12-算法的数学表示)
      - [函数式定义](#函数式定义)
      - [图灵机定义](#图灵机定义)
      - [λ演算定义](#λ演算定义)
    - [1.3 Rust实现映射](#13-rust实现映射)
  - [2. 算法分类体系](#2-算法分类体系)
    - [2.1 按设计范式分类](#21-按设计范式分类)
      - [分治法 (Divide and Conquer)](#分治法-divide-and-conquer)
      - [动态规划 (Dynamic Programming)](#动态规划-dynamic-programming)
      - [贪心算法 (Greedy)](#贪心算法-greedy)
      - [回溯法 (Backtracking)](#回溯法-backtracking)
    - [2.2 按问题域分类](#22-按问题域分类)
      - [图算法](#图算法)
      - [字符串算法](#字符串算法)
      - [数值算法](#数值算法)
  - [3. 计算模型](#3-计算模型)
    - [3.1 图灵机 (Turing Machine)](#31-图灵机-turing-machine)
    - [3.2 RAM模型 (Random Access Machine)](#32-ram模型-random-access-machine)
    - [3.3 λ演算](#33-λ演算)
  - [4. 语义模型](#4-语义模型)
    - [4.1 操作语义 (Operational Semantics)](#41-操作语义-operational-semantics)
    - [4.2 指称语义 (Denotational Semantics)](#42-指称语义-denotational-semantics)
    - [4.3 公理语义 (Axiomatic Semantics)](#43-公理语义-axiomatic-semantics)
    - [4.4 分离逻辑 (Separation Logic)](#44-分离逻辑-separation-logic)
  - [5. 算法设计范式](#5-算法设计范式)
    - [5.1 范式对比表](#51-范式对比表)
    - [5.2 选择决策树](#52-选择决策树)
  - [6. 复杂度理论](#6-复杂度理论)
    - [6.1 时间复杂度](#61-时间复杂度)
    - [6.2 主定理 (Master Theorem)](#62-主定理-master-theorem)
    - [6.3 摊还分析 (Amortized Analysis)](#63-摊还分析-amortized-analysis)
  - [7. 正确性证明方法](#7-正确性证明方法)
    - [7.1 循环不变量](#71-循环不变量)
    - [7.2 数学归纳法](#72-数学归纳法)
    - [7.3 不变式与变式](#73-不变式与变式)
  - [8. Rust 1.90特性映射](#8-rust-190特性映射)
    - [8.1 类型系统增强](#81-类型系统增强)
      - [GATs (Generic Associated Types)](#gats-generic-associated-types)
      - [Async Traits](#async-traits)
    - [8.2 Edition 2024特性](#82-edition-2024特性)
      - [let-else语法](#let-else语法)
      - [返回位置impl Trait (RPITIT)](#返回位置impl-trait-rpitit)
    - [8.3 形式化验证集成](#83-形式化验证集成)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [文档体系](#文档体系)

---

## 1. 算法的形式化定义

### 1.1 基本定义

**定义 1.1（算法）**：算法是一个五元组 A = (I, O, S, δ, F)，其中：

```text
I: 输入空间 (Input Space)
O: 输出空间 (Output Space)
S: 状态空间 (State Space)
δ: S × I → S: 状态转换函数 (Transition Function)
F: S → O: 输出函数 (Output Function)
```

**关键性质**：

1. **确定性** (Determinism): ∀s ∈ S, ∀i ∈ I, δ(s,i) 唯一确定
2. **有限性** (Finiteness): 算法在有限步内终止
3. **有效性** (Effectiveness): 每步操作都是可执行的
4. **输入** (Input): 0个或多个输入
5. **输出** (Output): 至少1个输出

### 1.2 算法的数学表示

#### 函数式定义

```text
算法 A: I → O

对于输入 x ∈ I，算法计算函数 f(x) ∈ O
```

#### 图灵机定义

```text
图灵机 M = (Q, Σ, Γ, δ, q₀, qₐ, qᵣ)

Q: 有限状态集
Σ: 输入字母表
Γ: 带符号表 (Σ ⊆ Γ)
δ: Q × Γ → Q × Γ × {L, R}: 转换函数
q₀ ∈ Q: 初始状态
qₐ ∈ Q: 接受状态
qᵣ ∈ Q: 拒绝状态
```

#### λ演算定义

```text
算法可表示为λ表达式：

λx.e

其中 e 是由以下规则构造的表达式：
- 变量: x, y, z, ...
- 抽象: λx.e
- 应用: e₁ e₂
```

### 1.3 Rust实现映射

```rust
/// 算法的泛型表示
/// 
/// # 类型参数
/// - `I`: 输入类型
/// - `O`: 输出类型
/// - `S`: 状态类型（可选）
/// 
/// # 形式化对应
/// ```text
/// trait Algorithm<I, O> {
///     fn compute(&self, input: I) -> O;
/// }
/// 对应数学函数: f: I → O
/// ```
pub trait Algorithm<I, O> {
    /// 计算函数 f: I → O
    /// 
    /// # 前置条件
    /// - input 必须在定义域 I 内
    /// 
    /// # 后置条件
    /// - 返回值在值域 O 内
    /// - 算法在有限步内终止
    fn compute(&self, input: I) -> O;
    
    /// 算法名称（用于识别）
    fn name(&self) -> &'static str;
    
    /// 时间复杂度（渐进上界）
    fn time_complexity(&self) -> &'static str;
    
    /// 空间复杂度（渐进上界）
    fn space_complexity(&self) -> &'static str;
}

/// 带状态的算法（对应状态机模型）
/// 
/// # 形式化对应
/// ```text
/// A = (I, O, S, δ, F)
/// - current_state: s ∈ S
/// - step: δ: S × I → S
/// - output: F: S → O
/// ```
pub trait StatefulAlgorithm<I, O, S> {
    /// 获取当前状态
    fn current_state(&self) -> &S;
    
    /// 状态转换函数 δ
    fn step(&mut self, input: I) -> S;
    
    /// 输出函数 F
    fn output(&self) -> O;
}

/// 可验证算法（带前置/后置条件）
/// 
/// # 形式化对应（霍尔逻辑）
/// ```text
/// {P} A {Q}
/// - precondition: P(input) = true
/// - postcondition: Q(input, output) = true
/// ```
pub trait VerifiableAlgorithm<I, O>: Algorithm<I, O> {
    /// 前置条件 P
    /// 
    /// # 形式化
    /// ```text
    /// P: I → Bool
    /// 验证输入是否满足算法要求
    /// ```
    fn precondition(&self, input: &I) -> bool;
    
    /// 后置条件 Q
    /// 
    /// # 形式化
    /// ```text
    /// Q: I × O → Bool
    /// 验证输出是否正确
    /// ```
    fn postcondition(&self, input: &I, output: &O) -> bool;
    
    /// 验证计算（带运行时检查）
    /// 
    /// # 霍尔逻辑证明
    /// ```text
    /// {P} A {Q}
    /// 
    /// 1. assert P(input)
    /// 2. output = A.compute(input)
    /// 3. assert Q(input, output)
    /// ```
    fn compute_verified(&self, input: I) -> Result<O, &'static str> 
    where 
        I: Clone,
        O: Clone,
    {
        if !self.precondition(&input) {
            return Err("Precondition violated");
        }
        
        let output = self.compute(input.clone());
        
        if !self.postcondition(&input, &output) {
            return Err("Postcondition violated");
        }
        
        Ok(output)
    }
}
```

---

## 2. 算法分类体系

### 2.1 按设计范式分类

#### 分治法 (Divide and Conquer)

**定义**：将问题分解为若干子问题，递归求解，然后合并结果。

**形式化表示**：

```text
DivideAndConquer(P):
  if |P| ≤ threshold:
    return DirectSolve(P)
  else:
    分解: P → P₁, P₂, ..., Pₖ
    递归: Sᵢ = DivideAndConquer(Pᵢ)
    合并: return Combine(S₁, S₂, ..., Sₖ)
```

**复杂度分析**：

```text
递归关系: T(n) = aT(n/b) + f(n)
主定理: 
  Case 1: f(n) = O(n^c), c < log_b(a) ⟹ T(n) = Θ(n^(log_b a))
  Case 2: f(n) = Θ(n^c log^k n), c = log_b(a) ⟹ T(n) = Θ(n^c log^(k+1) n)
  Case 3: f(n) = Ω(n^c), c > log_b(a) ⟹ T(n) = Θ(f(n))
```

**典型算法**：

- 归并排序: T(n) = 2T(n/2) + O(n) = O(n log n)
- 快速排序: 平均 O(n log n)，最坏 O(n²)
- 二分查找: T(n) = T(n/2) + O(1) = O(log n)
- Strassen矩阵乘法: O(n^2.807)

**Rust实现模式**：

```rust
/// 分治算法的通用trait
pub trait DivideAndConquer<Problem, Solution> {
    /// 判断是否为基础情况
    fn is_base_case(&self, problem: &Problem) -> bool;
    
    /// 直接求解基础情况
    fn solve_base_case(&self, problem: Problem) -> Solution;
    
    /// 分解问题
    fn divide(&self, problem: Problem) -> Vec<Problem>;
    
    /// 递归求解
    fn conquer(&self, problem: Problem) -> Solution {
        if self.is_base_case(&problem) {
            self.solve_base_case(problem)
        } else {
            let subproblems = self.divide(problem);
            let subsolutions: Vec<_> = subproblems
                .into_iter()
                .map(|p| self.conquer(p))
                .collect();
            self.combine(subsolutions)
        }
    }
    
    /// 合并子问题解
    fn combine(&self, solutions: Vec<Solution>) -> Solution;
}

/// 示例：归并排序
pub struct MergeSort;

impl DivideAndConquer<Vec<i32>, Vec<i32>> for MergeSort {
    fn is_base_case(&self, problem: &Vec<i32>) -> bool {
        problem.len() <= 1
    }
    
    fn solve_base_case(&self, problem: Vec<i32>) -> Vec<i32> {
        problem
    }
    
    fn divide(&self, mut problem: Vec<i32>) -> Vec<Vec<i32>> {
        let mid = problem.len() / 2;
        let right = problem.split_off(mid);
        vec![problem, right]
    }
    
    fn combine(&self, mut solutions: Vec<Vec<i32>>) -> Vec<i32> {
        let right = solutions.pop().unwrap();
        let left = solutions.pop().unwrap();
        merge(left, right)
    }
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}
```

#### 动态规划 (Dynamic Programming)

**定义**：将问题分解为重叠子问题，通过存储子问题解避免重复计算。

**形式化表示**：

```text
DP[i][j] = optimal value for subproblem(i, j)

递归关系 (Bellman方程):
DP[i][j] = opt { DP[i'][j'] | (i',j') ∈ Predecessors(i,j) }

初始条件: DP[base] = known value
```

**原理**：

1. **最优子结构** (Optimal Substructure): 最优解包含子问题的最优解
2. **重叠子问题** (Overlapping Subproblems): 子问题重复出现
3. **无后效性** (No After-effect): 子问题独立

**典型算法**：

- 斐波那契数列: O(n)
- 最长公共子序列 (LCS): O(mn)
- 0-1背包: O(nW)
- 最短路径 (Floyd-Warshall): O(n³)

**Rust实现模式**：

```rust
/// 动态规划算法trait
pub trait DynamicProgramming<Problem, Solution> {
    /// 子问题类型
    type Subproblem;
    
    /// 将问题分解为子问题序列
    fn subproblems(&self, problem: &Problem) -> Vec<Self::Subproblem>;
    
    /// 判断是否为基础子问题
    fn is_base_subproblem(&self, subproblem: &Self::Subproblem) -> bool;
    
    /// 求解基础子问题
    fn solve_base(&self, subproblem: &Self::Subproblem) -> Solution;
    
    /// 递归关系（Bellman方程）
    fn recurrence(&self, subproblem: &Self::Subproblem, memo: &std::collections::HashMap<Self::Subproblem, Solution>) -> Solution
    where
        Self::Subproblem: std::hash::Hash + Eq;
    
    /// 自底向上求解
    fn solve(&self, problem: Problem) -> Solution
    where
        Self::Subproblem: std::hash::Hash + Eq + Clone,
        Solution: Clone,
    {
        let subproblems = self.subproblems(&problem);
        let mut memo = std::collections::HashMap::new();
        
        for subproblem in subproblems {
            let solution = if self.is_base_subproblem(&subproblem) {
                self.solve_base(&subproblem)
            } else {
                self.recurrence(&subproblem, &memo)
            };
            memo.insert(subproblem, solution);
        }
        
        // 返回原问题的解
        memo.values().last().unwrap().clone()
    }
}

/// 示例：斐波那契数列
/// 
/// # 递归关系
/// ```text
/// F(0) = 0
/// F(1) = 1
/// F(n) = F(n-1) + F(n-2), n ≥ 2
/// ```
pub fn fibonacci_dp(n: usize) -> u64 {
    if n == 0 { return 0; }
    if n == 1 { return 1; }
    
    let mut dp = vec![0; n + 1];
    dp[0] = 0;
    dp[1] = 1;
    
    // 自底向上填表
    for i in 2..=n {
        dp[i] = dp[i-1] + dp[i-2];
    }
    
    dp[n]
}
```

#### 贪心算法 (Greedy)

**定义**：每步选择局部最优，期望达到全局最优。

**形式化表示**：

```text
Greedy(S):
  Solution = ∅
  while S ≠ ∅:
    x = SelectBest(S)
    if IsFeasible(Solution ∪ {x}):
      Solution = Solution ∪ {x}
    S = S \ {x}
  return Solution
```

**正确性条件**：

1. **贪心选择性质** (Greedy Choice Property): 局部最优导致全局最优
2. **最优子结构** (Optimal Substructure): 问题的最优解包含子问题的最优解

**典型算法**：

- 活动选择: O(n log n)
- Huffman编码: O(n log n)
- Dijkstra最短路径: O((V+E) log V)
- Prim/Kruskal最小生成树: O(E log V)

**Rust实现**：

```rust
/// 贪心算法trait
pub trait GreedyAlgorithm<Item, Solution> {
    /// 选择贪心元素
    fn select_greedy(&self, candidates: &[Item]) -> Option<usize>;
    
    /// 检查可行性
    fn is_feasible(&self, solution: &Solution, item: &Item) -> bool;
    
    /// 添加到解中
    fn add_to_solution(&self, solution: &mut Solution, item: Item);
    
    /// 初始化空解
    fn empty_solution(&self) -> Solution;
    
    /// 贪心求解
    fn solve(&self, mut items: Vec<Item>) -> Solution 
    where
        Item: Clone,
    {
        let mut solution = self.empty_solution();
        
        while !items.is_empty() {
            if let Some(idx) = self.select_greedy(&items) {
                let item = items.remove(idx);
                if self.is_feasible(&solution, &item) {
                    self.add_to_solution(&mut solution, item);
                }
            } else {
                break;
            }
        }
        
        solution
    }
}

/// 示例：活动选择问题
/// 
/// # 问题
/// 给定n个活动，每个活动有开始和结束时间，选择最多的互不重叠活动
/// 
/// # 贪心策略
/// 按结束时间排序，每次选择最早结束的活动
#[derive(Clone, Debug)]
pub struct Activity {
    pub start: i32,
    pub end: i32,
}

pub struct ActivitySelection;

impl GreedyAlgorithm<Activity, Vec<Activity>> for ActivitySelection {
    fn select_greedy(&self, candidates: &[Activity]) -> Option<usize> {
        candidates.iter()
            .enumerate()
            .min_by_key(|(_, a)| a.end)
            .map(|(i, _)| i)
    }
    
    fn is_feasible(&self, solution: &Vec<Activity>, item: &Activity) -> bool {
        solution.last().map_or(true, |last| last.end <= item.start)
    }
    
    fn add_to_solution(&self, solution: &mut Vec<Activity>, item: Activity) {
        solution.push(item);
    }
    
    fn empty_solution(&self) -> Vec<Activity> {
        Vec::new()
    }
}
```

#### 回溯法 (Backtracking)

**定义**：通过试探搜索解空间，遇到不可行解时回退。

**形式化表示**：

```text
Backtrack(solution, candidates):
  if IsComplete(solution):
    RecordSolution(solution)
    return
  
  for c in candidates:
    if IsValid(solution, c):
      solution.add(c)
      Backtrack(solution, NextCandidates(solution))
      solution.remove(c)  // 回溯
```

**剪枝策略**：

1. **约束剪枝**: 违反约束时停止
2. **界限剪枝**: 超出最优界时停止
3. **对称性剪枝**: 避免对称解

**典型算法**：

- N皇后: O(N!)
- 全排列: O(N!)
- 子集生成: O(2^N)
- 图着色: 指数时间

**Rust实现**：

```rust
/// 回溯算法trait
pub trait Backtracking {
    type Solution;
    type Candidate;
    
    /// 判断是否为完整解
    fn is_complete(&self, solution: &Self::Solution) -> bool;
    
    /// 获取候选项
    fn candidates(&self, solution: &Self::Solution) -> Vec<Self::Candidate>;
    
    /// 检查候选项是否有效
    fn is_valid(&self, solution: &Self::Solution, candidate: &Self::Candidate) -> bool;
    
    /// 添加候选项到解中
    fn add_candidate(&self, solution: &mut Self::Solution, candidate: Self::Candidate);
    
    /// 移除候选项（回溯）
    fn remove_candidate(&self, solution: &mut Self::Solution) -> Option<Self::Candidate>;
    
    /// 回溯搜索
    fn backtrack(&self, solution: &mut Self::Solution, all_solutions: &mut Vec<Self::Solution>)
    where
        Self::Solution: Clone,
        Self::Candidate: Clone,
    {
        if self.is_complete(solution) {
            all_solutions.push(solution.clone());
            return;
        }
        
        for candidate in self.candidates(solution) {
            if self.is_valid(solution, &candidate) {
                self.add_candidate(solution, candidate);
                self.backtrack(solution, all_solutions);
                self.remove_candidate(solution);
            }
        }
    }
}

/// 示例：N皇后问题
/// 
/// # 问题
/// 在N×N棋盘上放置N个皇后，使得任意两个皇后不在同一行、列、对角线
/// 
/// # 解法
/// 逐行放置皇后，每行尝试N个位置，回溯不可行的位置
pub struct NQueens {
    n: usize,
}

impl Backtracking for NQueens {
    type Solution = Vec<usize>; // Solution[i] = 第i行皇后的列位置
    type Candidate = usize;     // 列位置
    
    fn is_complete(&self, solution: &Self::Solution) -> bool {
        solution.len() == self.n
    }
    
    fn candidates(&self, _solution: &Self::Solution) -> Vec<Self::Candidate> {
        (0..self.n).collect()
    }
    
    fn is_valid(&self, solution: &Self::Solution, candidate: &Self::Candidate) -> bool {
        let row = solution.len();
        for (r, &col) in solution.iter().enumerate() {
            // 检查列冲突
            if col == *candidate {
                return false;
            }
            // 检查对角线冲突
            if (row as i32 - r as i32).abs() == (*candidate as i32 - col as i32).abs() {
                return false;
            }
        }
        true
    }
    
    fn add_candidate(&self, solution: &mut Self::Solution, candidate: Self::Candidate) {
        solution.push(candidate);
    }
    
    fn remove_candidate(&self, solution: &mut Self::Solution) -> Option<Self::Candidate> {
        solution.pop()
    }
}
```

### 2.2 按问题域分类

#### 图算法

**基本概念**：

```text
图 G = (V, E)
- V: 顶点集
- E: 边集 ⊆ V × V

无向图: (u,v) ∈ E ⟺ (v,u) ∈ E
有向图: (u,v) ∈ E ⇏ (v,u) ∈ E
加权图: w: E → ℝ
```

**主要问题**：

1. **遍历**: DFS O(V+E), BFS O(V+E)
2. **最短路径**:
   - 单源: Dijkstra O((V+E)log V), Bellman-Ford O(VE)
   - 全对: Floyd-Warshall O(V³)
3. **最小生成树**: Prim O(E log V), Kruskal O(E log E)
4. **拓扑排序**: O(V+E)
5. **强连通分量**: Tarjan/Kosaraju O(V+E)

#### 字符串算法

**主要问题**：

1. **模式匹配**:
   - KMP O(n+m)
   - Boyer-Moore O(n)
   - Rabin-Karp O(n+m)
2. **多模式匹配**: Aho-Corasick O(n+m+z)
3. **后缀数组**: O(n log n)
4. **最长公共子串**: O(mn)

#### 数值算法

**主要问题**：

1. **排序**: O(n log n)
2. **搜索**: O(log n)
3. **矩阵运算**: O(n³) → O(n^2.37)
4. **快速傅里叶变换**: O(n log n)

---

## 3. 计算模型

### 3.1 图灵机 (Turing Machine)

**定义**：

```text
TM = (Q, Σ, Γ, δ, q₀, B, F)

Q: 状态集
Σ: 输入字母表
Γ: 带符号表 (Σ ⊂ Γ)
δ: Q × Γ → Q × Γ × {L,R,S}: 转换函数
q₀: 初始状态
B ∈ Γ: 空白符号
F ⊆ Q: 接受状态集
```

**Church-Turing论题**：任何可计算函数都可由图灵机计算。

### 3.2 RAM模型 (Random Access Machine)

**特点**：

- 随机访问内存
- 基本操作（+,-,*,/,比较）O(1)
- 用于分析实际算法复杂度

### 3.3 λ演算

**语法**：

```text
e ::= x           (变量)
    | λx.e        (抽象)
    | e₁ e₂       (应用)
```

**归约规则**：

```text
β归约: (λx.e₁) e₂ → e₁[x := e₂]
```

---

## 4. 语义模型

### 4.1 操作语义 (Operational Semantics)

**小步语义** (Small-step):

```text
⟨e, σ⟩ → ⟨e', σ'⟩

表示：在状态σ下，表达式e执行一步得到e'和新状态σ'
```

**大步语义** (Big-step):

```text
⟨e, σ⟩ ⇓ ⟨v, σ'⟩

表示：在状态σ下，表达式e求值到值v，最终状态σ'
```

### 4.2 指称语义 (Denotational Semantics)

将程序映射到数学对象：

```text
⟦e⟧: Env → Val

⟦x⟧ρ = ρ(x)
⟦λx.e⟧ρ = λv.⟦e⟧(ρ[x↦v])
⟦e₁ e₂⟧ρ = (⟦e₁⟧ρ)(⟦e₂⟧ρ)
```

### 4.3 公理语义 (Axiomatic Semantics)

**霍尔逻辑** (Hoare Logic):

```text
{P} C {Q}

P: 前置条件
C: 程序
Q: 后置条件
```

**推理规则**：

```text
赋值: {Q[x := e]} x := e {Q}

顺序: {P} C₁ {Q}, {Q} C₂ {R}
      ----------------------
         {P} C₁; C₂ {R}

条件: {P ∧ B} C₁ {Q}, {P ∧ ¬B} C₂ {Q}
      -----------------------------------
         {P} if B then C₁ else C₂ {Q}

循环: {I ∧ B} C {I}
      ----------------
      {I} while B do C {I ∧ ¬B}
```

### 4.4 分离逻辑 (Separation Logic)

**扩展霍尔逻辑**，处理指针和堆：

```text
P ::= emp                    空堆
    | e ↦ e'                 点指向
    | P * P                  分离合取
    | P -* P                 分离蕴含
```

**与Rust所有权的关系**：

```text
Rust所有权规则 ≈ 分离逻辑的空间分离

x: Box<T>  对应  x ↦ v
move语义  对应  资源转移
借用检查  对应  分离逻辑证明
```

---

## 5. 算法设计范式

### 5.1 范式对比表

| 范式 | 子问题关系 | 求解方式 | 时间复杂度 | 典型应用 |
|------|-----------|---------|-----------|---------|
| 分治 | 独立 | 递归分解 | O(n log n) | 排序、搜索 |
| 动态规划 | 重叠 | 记忆化/填表 | O(n²) ~ O(n³) | LCS、背包 |
| 贪心 | 无需回顾 | 局部最优 | O(n log n) | 最小生成树 |
| 回溯 | 约束满足 | 试探+剪枝 | 指数级 | N皇后、图着色 |

### 5.2 选择决策树

```text
问题特征
├─ 有最优子结构?
│  ├─ Yes: 有重叠子问题?
│  │  ├─ Yes → 动态规划
│  │  └─ No → 分治
│  └─ No: 需要全局搜索?
│     ├─ Yes → 回溯
│     └─ No → 贪心（需证明）
└─ 约束满足问题? → 回溯
```

---

## 6. 复杂度理论

### 6.1 时间复杂度

**渐进记号**：

```text
O(f(n)):  上界  g(n) ≤ c·f(n)
Ω(f(n)):  下界  g(n) ≥ c·f(n)
Θ(f(n)):  紧界  c₁·f(n) ≤ g(n) ≤ c₂·f(n)
o(f(n)):  严格上界
ω(f(n)):  严格下界
```

**常见复杂度**：

```text
O(1)      < O(log n)    < O(√n)      < O(n)       <
O(n log n)< O(n²)       < O(n³)      < O(2ⁿ)      < O(n!)
```

### 6.2 主定理 (Master Theorem)

```text
T(n) = aT(n/b) + f(n)

Case 1: f(n) = O(n^c), c < log_b a
        ⟹ T(n) = Θ(n^(log_b a))

Case 2: f(n) = Θ(n^c log^k n), c = log_b a
        ⟹ T(n) = Θ(n^c log^(k+1) n)

Case 3: f(n) = Ω(n^c), c > log_b a
        且 a·f(n/b) ≤ k·f(n) for k < 1
        ⟹ T(n) = Θ(f(n))
```

### 6.3 摊还分析 (Amortized Analysis)

**三种方法**：

1. **聚合分析** (Aggregate): 总代价 / 操作数
2. **记账法** (Accounting): 预付费用抵消昂贵操作
3. **势能法** (Potential): Φ(D) 表示数据结构势能

**示例：动态数组扩容**:

```text
操作序列：n次push
- 扩容代价：1 + 2 + 4 + ... + 2^k ≈ 2n
- 总代价：n + 2n = 3n
- 摊还：O(1)
```

---

## 7. 正确性证明方法

### 7.1 循环不变量

**模板**：

```text
初始化：循环开始前I为真
维护：若I为真且循环继续，则一次迭代后I仍为真
终止：循环结束时，I和终止条件蕴含正确性
```

**示例：插入排序**:

```rust
/// 插入排序（带循环不变量证明）
/// 
/// # 循环不变量 I
/// ```text
/// 在外层循环第i次迭代开始时：
/// arr[0..i] 是原始 arr[0..i] 的排序版本
/// ```
/// 
/// # 证明
/// ```text
/// 初始化：i=1时，arr[0..1]只有一个元素，已排序 ✓
/// 
/// 维护：假设arr[0..i]已排序
///       内层循环将arr[i]插入正确位置
///       因此arr[0..i+1]排序 ✓
/// 
/// 终止：i=n时，arr[0..n]全部排序 ✓
/// ```
pub fn insertion_sort<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        // 不变量：arr[0..i]已排序
        let mut j = i;
        while j > 0 && arr[j-1] > arr[j] {
            arr.swap(j-1, j);
            j -= 1;
        }
        // 不变量维护：arr[0..i+1]现在已排序
    }
    // 终止：arr[0..n]全部排序
}
```

### 7.2 数学归纳法

**结构**：

1. **基础情况**: 证明 P(0) 或 P(1)
2. **归纳假设**: 假设 P(k) 对某个 k 成立
3. **归纳步骤**: 证明 P(k) ⟹ P(k+1)

**示例：斐波那契**:

```text
定理：F(n) = (φⁿ - ψⁿ) / √5，其中 φ = (1+√5)/2, ψ = (1-√5)/2

基础：F(0) = 0 = (1-1)/√5 ✓
      F(1) = 1 = (φ-ψ)/√5 ✓

归纳：假设对 k, k-1 成立
      F(k+1) = F(k) + F(k-1)
             = (φᵏ - ψᵏ)/√5 + (φᵏ⁻¹ - ψᵏ⁻¹)/√5
             = (φᵏ⁻¹(φ+1) - ψᵏ⁻¹(ψ+1))/√5
             = (φᵏ⁺¹ - ψᵏ⁺¹)/√5  (因为 φ²=φ+1, ψ²=ψ+1) ✓
```

### 7.3 不变式与变式

**不变式** (Invariant): 始终为真的性质  
**变式** (Variant): 单调变化且有界的量（证明终止性）

**示例：Euclid算法**:

```rust
/// 最大公约数（Euclid算法）
/// 
/// # 不变式
/// ```text
/// gcd(a, b) = gcd(original_a, original_b)
/// ```
/// 
/// # 变式（证明终止）
/// ```text
/// V(a, b) = b
/// 每次迭代 b 严格递减且非负，因此必终止
/// ```
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    // 不变式：gcd(a,b) = gcd(原始a, 原始b)
    while b != 0 {
        let temp = b;
        b = a % b;  // b 递减
        a = temp;
        // 不变式维护：gcd(a,b)不变
    }
    a  // b=0时，gcd(a,0) = a
}
```

---

## 8. Rust 1.90特性映射

### 8.1 类型系统增强

#### GATs (Generic Associated Types)

**应用场景**：高阶算法抽象

```rust
/// 使用GATs定义算法族
pub trait AlgorithmFamily {
    type Input<'a>;
    type Output<'a>;
    
    /// 算法计算（生命周期灵活）
    fn compute<'a>(&self, input: Self::Input<'a>) -> Self::Output<'a>;
}

/// 示例：迭代器算法族
pub struct IteratorAlgorithms;

impl AlgorithmFamily for IteratorAlgorithms {
    type Input<'a> = &'a [i32];
    type Output<'a> = impl Iterator<Item = i32> + 'a;
    
    fn compute<'a>(&self, input: Self::Input<'a>) -> Self::Output<'a> {
        input.iter().copied().filter(|&x| x > 0)
    }
}
```

#### Async Traits

**应用场景**：异步算法接口

```rust
/// 异步算法trait（Rust 1.75+ 稳定）
pub trait AsyncAlgorithm<I, O> {
    /// 异步计算
    async fn compute_async(&self, input: I) -> O;
    
    /// 批量计算
    async fn batch_compute(&self, inputs: Vec<I>) -> Vec<O> {
        let mut results = Vec::new();
        for input in inputs {
            results.push(self.compute_async(input).await);
        }
        results
    }
}

/// 示例：异步排序
pub struct AsyncMergeSort;

impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncMergeSort {
    async fn compute_async(&self, mut input: Vec<i32>) -> Vec<i32> {
        if input.len() <= 1 {
            return input;
        }
        
        let mid = input.len() / 2;
        let right = input.split_off(mid);
        
        // 并行递归
        let (left, right) = tokio::join!(
            self.compute_async(input),
            self.compute_async(right)
        );
        
        merge(left, right)
    }
}
```

### 8.2 Edition 2024特性

#### let-else语法

```rust
/// 使用let-else简化错误处理
pub fn binary_search_with_let_else<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();
    
    while left < right {
        let mid = left + (right - left) / 2;
        
        // let-else：简洁的模式匹配
        let Some(mid_val) = arr.get(mid) else {
            return None;
        };
        
        match mid_val.cmp(target) {
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
            std::cmp::Ordering::Equal => return Some(mid),
        }
    }
    
    None
}
```

#### 返回位置impl Trait (RPITIT)

```rust
/// RPITIT：简化返回类型
pub trait GraphAlgorithm {
    type Node;
    
    /// 返回迭代器（无需Box）
    fn traverse(&self) -> impl Iterator<Item = Self::Node> + '_;
}

pub struct Graph {
    nodes: Vec<i32>,
}

impl GraphAlgorithm for Graph {
    type Node = i32;
    
    fn traverse(&self) -> impl Iterator<Item = i32> + '_ {
        self.nodes.iter().copied()
    }
}
```

### 8.3 形式化验证集成

```rust
/// 集成Rust验证工具的算法
/// 
/// # 验证工具
/// - Prusti: 契约式验证
/// - Creusot: 演绎验证
/// - Kani: 模型检查

#[cfg_attr(feature = "prusti", prusti::requires(arr.is_sorted()))]
#[cfg_attr(feature = "prusti", prusti::ensures(result.is_some() ==> arr[result.unwrap()] == target))]
pub fn verified_binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();
    
    // 循环不变量（Prusti语法）
    #[cfg_attr(feature = "prusti", prusti::invariant(left <= right))]
    #[cfg_attr(feature = "prusti", prusti::invariant(right <= arr.len()))]
    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
            std::cmp::Ordering::Equal => return Some(mid),
        }
    }
    
    None
}
```

---

## 总结

### 核心要点

1. **形式化基础**：算法 = (I, O, S, δ, F)，图灵等价
2. **设计范式**：分治、DP、贪心、回溯各有适用场景
3. **复杂度分析**：主定理、摊还分析、渐进记号
4. **正确性证明**：循环不变量、霍尔逻辑、数学归纳
5. **Rust映射**：类型系统保证安全性，所有权≈分离逻辑

### 文档体系

```text
算法理论体系
├── 形式化基础（本文档）
├── 异步同步等价关系
├── Actor/Reactor/CSP模式
├── 异步递归分析
└── 控制流执行流等价性
```

---

**作者**: Rust算法团队  
**参考文献**:

- *Introduction to Algorithms* (CLRS)
- *Types and Programming Languages* (Pierce)
- *Communicating Sequential Processes* (Hoare)
- Rust Language Reference
