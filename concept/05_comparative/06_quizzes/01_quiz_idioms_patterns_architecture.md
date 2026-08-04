> **内容分级**: [测验级]

# 测验：Rust 惯用法、算法、设计模式与架构模式

**EN**: Quiz — Rust Idioms, Algorithms, Patterns, and Architecture
**Summary**: Verify understanding of Rust idioms, classic algorithms, design patterns, and architecture patterns.
**受众**: [进阶]
**Rust 版本**: 1.97.0+ (Edition 2024)
**权威来源**: 本文件为 `concept/` 权威页。
**定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
**前置概念**: [Rust 惯用法、算法、设计模式与架构模式](../05_idioms_patterns_architecture/README.md)

---

> **Bloom 层级**: L5-L6
> **难度图例**: 🟢 基础｜ 🟡 进阶｜ 🔴 专家
> **题型构成**: 代码阅读题 + 单选 + 多选 + 判断
> **定位**: 覆盖 P10-3 新增权威页的交互测验。

---

## 一、惯用法

### Q1. 🟢 【单选】 `Into` 与 `From` 之间有什么关系？

- A. 互不相关
- B. 实现了 `From<T>` 会自动获得 `Into<U>`
- C. 实现了 `Into<T>` 会自动获得 `From<U>`
- D. 必须同时手动实现两者

<details>
<summary>💡 答案与解析</summary>

**答案：B**

Rust 标准库提供 blanket impl：`impl<T, U> Into<U> for T where U: From<T>`。因此只要实现 `From<T>` for `U`，`T: Into<U>` 自动可用。

</details>

---

### Q2. 🟡 【代码阅读】 以下 Newtype 代码的输出是什么？

```rust
struct Meters(u32);
struct Kilometers(u32);

fn main() {
    let m = Meters(1000);
    let k = Kilometers(m.0 / 1000);
    println!("{}", k.0);
}
```

<details>
<summary>💡 答案与解析</summary>

**答案：输出 `1`**

Newtype 通过元组结构体包装底层类型；访问内部字段 `m.0` 得到原始 `u32`，因此表达式合法，`1000 / 1000 = 1`。

</details>

---

### Q3. 🟡 【单选】 Typestate 模式的核心收益是什么？

- A. 减少运行时分支
- B. 将状态约束提升到类型系统，在编译期阻止非法状态转换
- C. 提高运行时性能
- D. 避免使用枚举

<details>
<summary>💡 答案与解析</summary>

**答案：B**

Typestate 通过泛型参数将状态编码进类型，使得 `workflow.start()` 等非法操作在编译期被拒绝。

</details>

---

### Q4. 🟢 【单选】 Builder 模式最适合解决什么问题？

- A. 频繁的类型转换
- B. 构造包含多个可选字段的复杂对象
- C. 实现运行时多态
- D. 替代枚举

<details>
<summary>💡 答案与解析</summary>

**答案：B**

Builder 将复杂对象的构造拆分为多个链式调用，使可选字段和默认值管理更清晰。

</details>

---

## 二、算法

### Q5. 🟡 【单选】 线段树（Segment Tree）的单点更新和区间查询时间复杂度分别是？

- A. O(1) / O(n)
- B. O(log n) / O(log n)
- C. O(n) / O(log n)
- D. O(log n) / O(n)

<details>
<summary>💡 答案与解析</summary>

**答案：B**

线段树通过二分区间组织数据，单点更新与区间查询均沿树高下行/上行，复杂度为 O(log n)。

</details>

---

### Q6. 🟢 【单选】 并查集（Union-Find）使用路径压缩后的均摊查找复杂度接近？

- A. O(n)
- B. O(log n)
- C. O(α(n))，其中 α 为反阿克曼函数
- D. O(1)

<details>
<summary>💡 答案与解析</summary>

**答案：C**

路径压缩 + 按秩合并使并查集单次操作的均摊复杂度为反阿克曼函数，实际中可视为常数。

</details>

---

### Q7. 🟡 【单选】 下列哪种图算法最适合求解单源最短路径且边权非负？

- A. BFS
- B. DFS
- C. Dijkstra
- D. Trie 遍历

<details>
<summary>💡 答案与解析</summary>

**答案：C**

Dijkstra 算法在边权非负时能以贪心策略正确求解单源最短路径；BFS 仅适用于无权图。

</details>

---

## 三、设计模式

### Q8. 🟢 【单选】 Strategy 模式用于？

- A. 封装算法族并使其可相互替换
- B. 将请求封装为对象
- C. 表示对象的部分-整体层次
- D. 控制对象访问

<details>
<summary>💡 答案与解析</summary>

**答案：A**

Strategy 定义算法族，分别封装，并让它们可以互相替换，符合开闭原则。

</details>

---

### Q9. 🟡 【单选】 Command 模式的主要优势不包括？

- A. 支持撤销/重做
- B. 将调用者与接收者解耦
- C. 提高内存访问局部性
- D. 支持宏命令和延迟执行

<details>
<summary>💡 答案与解析</summary>

**答案：C**

Command 模式通过对象化请求实现解耦、撤销、队列化等，但与内存局部性无直接关系。

</details>

---

### Q10. 🟡 【单选】 Visitor 模式最适合的场景是？

- A. 需要频繁添加新元素类且元素结构稳定
- B. 需要频繁为稳定元素结构添加新操作
- C. 需要隐藏对象创建细节
- D. 需要实现对象深拷贝

<details>
<summary>💡 答案与解析</summary>

**答案：B**

Visitor 把操作集中到访问者，新增操作只需新增访问者，无需修改元素类；但新增元素类较困难。

</details>

---

## 四、架构模式

### Q11. 🟡 【单选】 Hexagonal Architecture（端口与适配器）强调？

- A. 业务逻辑直接依赖数据库 SDK
- B. 业务逻辑通过端口依赖抽象，适配器负责具体实现
- C. 所有服务共享同一个数据模型
- D. 使用微服务拆分所有模块

<details>
<summary>💡 答案与解析</summary>

**答案：B**

六边形架构将应用核心置于中心，通过端口（接口）与外部交互，适配器实现端口细节，从而隔离外部变化。

</details>

---

### Q12. 🟢 【单选】 CQRS 模式的核心含义是？

- A. 命令与查询使用同一模型
- B. 命令（写）与查询（读）使用不同模型
- C. 所有事件必须同步持久化
- D. 数据库必须分片

<details>
<summary>💡 答案与解析</summary>

**答案：B**

CQRS（Command Query Responsibility Segregation）将写模型与读模型分离，以优化各自场景。

</details>

---

## 五、综合判断

### Q13. 🟢 【判断】 Actor 模型通过共享内存进行并发通信

- A. 正确
- B. 错误

<details>
<summary>💡 答案与解析</summary>

**答案：B**

Actor 模型的核心是通过**异步消息传递**通信，避免共享可变状态，从而降低数据竞争风险。

</details>

---

### Q14. 🟢 【判断】 Event Bus 中发布者需要知道所有订阅者

- A. 正确
- B. 错误

<details>
<summary>💡 答案与解析</summary>

**答案：B**

发布者通过总线发布事件，无需知道订阅者；订阅者向总线注册即可解耦。

</details>

---

### Q15. 🔴 【多选】 在 Rust 中使用无锁数据结构的主要动机是？（多选）

- A. 完全避免锁竞争
- B. 提升某些并发场景下的吞吐和可扩展性
- C. 简化代码逻辑
- D. 消除数据竞争（仍需正确使用内存序）

<details>
<summary>💡 答案与解析</summary>

**答案：A、B、D**

无锁结构通过原子操作避免互斥锁竞争，可提升可扩展性，但代码更复杂；Rust 类型系统保证无数据竞争的前提是正确使用 `Send`/`Sync` 和内存序。

</details>
