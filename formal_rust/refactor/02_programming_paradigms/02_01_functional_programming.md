# 2.1 函数式编程理论

## 2.1.1 函数式编程基础

### 定义 2.1.1 (函数式编程)

函数式编程是一种编程范式，其中计算被视为数学函数的求值，避免状态和可变数据。

### 定义 2.1.2 (纯函数)

函数 $f: A \rightarrow B$ 是纯函数，当且仅当：

1. 对于相同的输入总是产生相同的输出
2. 没有副作用
3. 不依赖外部状态

形式化定义为：
$$\text{Pure}(f) \iff \forall x, y \in A, x = y \Rightarrow f(x) = f(y) \land \text{NoSideEffects}(f)$$

### 定理 2.1.1 (纯函数可组合性)

纯函数是可组合的：
$$\text{Pure}(f) \land \text{Pure}(g) \Rightarrow \text{Pure}(g \circ f)$$

**证明**：

1. 设 $f: A \rightarrow B$ 和 $g: B \rightarrow C$ 为纯函数
2. 对于任意 $x, y \in A$，如果 $x = y$，则 $f(x) = f(y)$
3. 因此 $g(f(x)) = g(f(y))$
4. 且 $g \circ f$ 没有副作用
5. 因此 $g \circ f$ 是纯函数

## 2.1.2 高阶函数理论

### 定义 2.1.3 (高阶函数)

高阶函数是接受函数作为参数或返回函数的函数：
$$\text{HigherOrder}(f) \iff f: \mathcal{F} \rightarrow \mathcal{F} \lor f: A \rightarrow \mathcal{F}$$

### 定义 2.1.4 (映射函数)

映射函数 $\text{map}: (A \rightarrow B) \rightarrow [A] \rightarrow [B]$ 定义为：
$$\text{map}(f)([a_1, a_2, \ldots, a_n]) = [f(a_1), f(a_2), \ldots, f(a_n)]$$

### 定理 2.1.2 (映射函数性质)

映射函数满足以下性质：

1. 单位律：$\text{map}(\text{id}) = \text{id}$
2. 结合律：$\text{map}(g \circ f) = \text{map}(g) \circ \text{map}(f)$

**证明**：

1. 单位律：$\text{map}(\text{id})([a_1, \ldots, a_n]) = [\text{id}(a_1), \ldots, \text{id}(a_n)] = [a_1, \ldots, a_n]$
2. 结合律：$\text{map}(g \circ f)([a_1, \ldots, a_n]) = [(g \circ f)(a_1), \ldots, (g \circ f)(a_n)] = [g(f(a_1)), \ldots, g(f(a_n))] = \text{map}(g)(\text{map}(f)([a_1, \ldots, a_n]))$

## 2.1.3 不可变性理论

### 定义 2.1.5 (不可变性)

数据结构是不可变的，当且仅当：
$$\text{Immutable}(d) \iff \forall t, t', d(t) = d(t')$$

### 定义 2.1.6 (持久化数据结构)

持久化数据结构支持多个版本同时存在：
$$\text{Persistent}(D) \iff \forall d \in D, \forall op, \text{Version}(op(d)) \neq \text{Version}(d)$$

### 定理 2.1.3 (不可变性线程安全)

不可变数据结构天然线程安全：
$$\text{Immutable}(d) \Rightarrow \text{ThreadSafe}(d)$$

**证明**：

1. 不可变数据结构不能被修改
2. 多个线程只能读取相同数据
3. 没有数据竞争
4. 因此线程安全

## 2.1.4 函数组合理论

### 定义 2.1.7 (函数组合)

函数组合 $\circ$ 定义为：
$$(g \circ f)(x) = g(f(x))$$

### 定义 2.1.8 (组合律)

函数组合满足结合律：
$$(h \circ g) \circ f = h \circ (g \circ f)$$

### 定理 2.1.4 (组合函数性质)

组合函数保持纯函数性质：
$$\text{Pure}(f) \land \text{Pure}(g) \Rightarrow \text{Pure}(g \circ f)$$

**证明**：

1. 设 $f: A \rightarrow B$ 和 $g: B \rightarrow C$ 为纯函数
2. 对于任意 $x, y \in A$，如果 $x = y$，则 $f(x) = f(y)$
3. 因此 $g(f(x)) = g(f(y))$
4. 且 $g \circ f$ 没有副作用
5. 因此 $g \circ f$ 是纯函数

## 2.1.5 单子理论

### 定义 2.1.9 (单子)

单子是一个三元组 $(M, \eta, \mu)$，其中：

- $M$ 是一个函子
- $\eta: A \rightarrow M(A)$ 是单位函数
- $\mu: M(M(A)) \rightarrow M(A)$ 是乘法函数

满足单子律：

1. $\mu \circ \eta_M = \text{id}_M$
2. $\mu \circ M(\eta) = \text{id}_M$
3. $\mu \circ \mu = \mu \circ M(\mu)$

### 定义 2.1.10 (Option 单子)

Option 单子定义为：

- $M(A) = \text{Option}(A)$
- $\eta(a) = \text{Some}(a)$
- $\mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
- $\mu(\text{Some}(\text{None})) = \text{None}$
- $\mu(\text{None}) = \text{None}$

### 定理 2.1.5 (Option 单子律)

Option 满足单子律。

**证明**：

1. $\mu \circ \eta_M(\text{Some}(a)) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
2. $\mu \circ M(\eta)(\text{Some}(a)) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
3. $\mu \circ \mu(\text{Some}(\text{Some}(\text{Some}(a)))) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$

## 2.1.6 函子理论

### 定义 2.1.11 (函子)

函子是一个映射 $F: \mathcal{C} \rightarrow \mathcal{D}$ 和一个函数 $\text{map}: (A \rightarrow B) \rightarrow (F(A) \rightarrow F(B))$，满足：

1. $\text{map}(\text{id}) = \text{id}$
2. $\text{map}(g \circ f) = \text{map}(g) \circ \text{map}(f)$

### 定义 2.1.12 (应用函子)

应用函子是函子加上应用操作：
$$\text{ap}: F(A \rightarrow B) \rightarrow F(A) \rightarrow F(B)$$

### 定理 2.1.6 (函子保持结构)

函子保持范畴结构：
$$\text{Functor}(F) \Rightarrow \text{PreserveStructure}(F)$$

**证明**：

1. 函子保持单位态射
2. 函子保持复合
3. 因此保持范畴结构

## 2.1.7 惰性求值理论

### 定义 2.1.13 (惰性求值)

惰性求值是一种求值策略，只在需要时才计算表达式的值：
$$\text{Lazy}(e) \iff \text{Evaluate}(e) \text{ only when } \text{Needed}(e)$$

### 定义 2.1.14 (流)

流是惰性列表：
$$\text{Stream}(A) = \text{Cons}(A, \text{Stream}(A)) \lor \text{Nil}$$

### 定理 2.1.7 (惰性求值效率)

惰性求值可以提高效率：
$$\text{Lazy}(e) \Rightarrow \text{Efficient}(e)$$

**证明**：

1. 惰性求值避免不必要的计算
2. 只在需要时计算
3. 因此提高效率

## 2.1.8 模式匹配理论

### 定义 2.1.15 (模式匹配)

模式匹配是函数式编程中的控制结构：
$$\text{Match}(e, p_1 \rightarrow e_1, p_2 \rightarrow e_2, \ldots, p_n \rightarrow e_n)$$

### 定义 2.1.16 (模式)

模式是值的结构描述：
$$\text{Pattern} = \text{Constructor}(\text{Pattern}_1, \text{Pattern}_2, \ldots, \text{Pattern}_n)$$

### 定理 2.1.8 (模式匹配完备性)

模式匹配是完备的：
$$\text{Complete}(\text{Pattern}) \Rightarrow \text{Exhaustive}(\text{Match})$$

**证明**：

1. 如果模式是完备的，则覆盖所有可能情况
2. 因此匹配是穷尽的

## 2.1.9 递归理论

### 定义 2.1.17 (递归函数)

递归函数是调用自身的函数：
$$f(x) = \text{BaseCase}(x) \lor f(\text{RecursiveCase}(x))$$

### 定义 2.1.18 (尾递归)

尾递归是递归调用在函数末尾的递归：
$$\text{TailRecursive}(f) \iff f(x) = \text{BaseCase}(x) \lor f(\text{RecursiveCase}(x))$$

### 定理 2.1.9 (尾递归优化)

尾递归可以被优化为循环：
$$\text{TailRecursive}(f) \Rightarrow \text{Optimizable}(f)$$

**证明**：

1. 尾递归调用后没有其他操作
2. 可以重用栈帧
3. 因此可以优化为循环

## 2.1.10 结论

函数式编程理论为 Rust 提供了强大的抽象能力，通过纯函数、高阶函数、不可变性、函数组合、单子等概念，实现了安全、高效、可维护的代码。这些理论为 Rust 的函数式编程特性提供了坚实的数学基础。

---

**参考文献**：

1. Pierce, B. C. (2002). Types and Programming Languages. MIT Press.
2. Bird, R., & Wadler, P. (1988). Introduction to Functional Programming. Prentice Hall.
3. Hutton, G. (2016). Programming in Haskell. Cambridge University Press.
4. Milewski, B. (2019). Category Theory for Programmers. Blurb.
