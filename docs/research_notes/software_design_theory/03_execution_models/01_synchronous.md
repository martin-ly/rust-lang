# 同步执行模型形式化

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **分类**: 执行模型
> **安全边界**: 纯 Safe

---

## 📊 目录 {#-目录}

- [同步执行模型形式化](#同步执行模型形式化)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [形式化定义](#形式化定义)
  - [操作语义（小步）](#操作语义小步)
  - [Rust 对应与代码示例](#rust-对应与代码示例)
  - [调用栈与求值顺序](#调用栈与求值顺序)
  - [与 async/并发对比](#与-async并发对比)
  - [栈展开与 panic](#栈展开与-panic)
  - [典型场景（实质内容）](#典型场景实质内容)
    - [与设计模式组合](#与设计模式组合)
    - [常见陷阱](#常见陷阱)
    - [反例](#反例)
  - [何时选择同步](#何时选择同步)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（同步执行）**:

同步执行满足：

- 单线程、顺序求值
- 归约序列线性：$e_0 \to e_1 \to e_2 \to \cdots \to v$
- 无并发、无抢占；每步至多一个归约

**Def 1.2（归约关系）**:

设 $\to \subseteq \mathrm{Expr} \times \mathrm{Expr}$。若 $(e, e') \in \to$，记 $e \to e'$，表示 $e$ 一步归约至 $e'$。

**Axiom SY1**：求值顺序确定；无交错；无数据竞争。

**Axiom SY2**：归约保持类型：若 $\Gamma \vdash e : \tau$ 且 $e \to e'$，则 $\Gamma \vdash e' : \tau$。即 [type_system_foundations](../../type_theory/type_system_foundations.md) 保持性。

**定理 SY-T1**：由 type_system 进展性 T1、保持性 T2，良型程序 $e$ 可求值至值 $v$（$e \to^* v$）或无限归约。

**定理 SY-T2**：由 [ownership_model](../../formal_methods/ownership_model.md)、[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)，同步执行下所有权与借用规则保证内存安全与无数据竞争。

---

## 操作语义（小步）

```text
(λx.e) v     →  e[v/x]     （β 归约）
let x = v in e  →  e[v/x]  （let 展开）
match C(v) { C(x) => e }  →  e[v/x]  （模式匹配）
```

Rust 的 MIR 语义更细粒度，但上述为概念性简化。

---

## Rust 对应与代码示例

```rust
// 同步：无 async、无 spawn
fn main() {
    let x = 1;
    let y = x + 2;      // 顺序求值
    let z = compute(y); // 调用完成才继续
    println!("{}", z);
}

fn compute(n: i32) -> i32 {
    n * 2
}
```

**形式化对应**：`let x = 1` 为赋值；`x + 2` 求值后产生新值；`compute(y)` 传入所有权或复制，顺序执行。

---

## 调用栈与求值顺序

```text
main()
  ├── let x = 1          // 求值 1
  ├── let y = x + 2      // 求值 x，求值 2，加法，存 y
  ├── let z = compute(y) // 转入 compute，等待返回
  │     compute(n)
  │       └── n * 2      // 求值，返回
  └── println!("{}", z)  // 获得 z 后继续
```

每步至多一个活跃调用；无交错；由 Axiom SY1 保证。

---

## 与 async/并发对比

| 模型 | 线程 | 调度 | 数据竞争 |
| :--- | :--- | :--- | :--- |
| 同步 | 1 | 无 | 无 |
| 异步 | 1 | 协作式 | 无（单线程） |
| 并发 | N | 抢占式 | 需 Send/Sync |

---

## 栈展开与 panic

**Axiom SY3**：panic 时栈展开，按 LIFO 顺序 drop 局部变量；若展开到线程边界则线程终止。

**与所有权**：drop 顺序保证 RAII 资源正确释放；见 [ownership_model](../../formal_methods/ownership_model.md)。

---

## 典型场景（实质内容）

| 场景 | 说明 | 代码示例 |
| :--- | :--- | :--- |
| 批处理 | 顺序处理、无 I/O 等待 | `for item in items { process(item)?; }` |
| 脚本 | 一次性任务 | `fn main() { run_pipeline()?; }` |
| 算法核心 | 纯计算、无并发 | 排序、搜索、图算法 |
| 配置解析 | 启动时加载 | `let config = Config::load("config.toml")?;` |
| 单请求处理 | 简单 CLI/工具 | `let result = compute(input); println!("{}", result);` |

### 与设计模式组合

| 组合 | 说明 |
| :--- | :--- |
| 同步 + Factory Method | 运行时决定产品类型；`let product = factory.create();` |
| 同步 + Strategy | 可替换算法；`ctx.execute(&data)` |
| 同步 + Template Method | 算法骨架；`algorithm.run()` |
| 同步 + State | 状态机；`state.handle(&mut ctx)` |

### 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 同步中阻塞 I/O | 整个流程卡住 | 需 I/O 并发时用 async 或 spawn |
| 长计算无 yield | 单线程无响应 | 分批处理、或改为并行 |
| 递归过深 | 栈溢出 | 改为迭代、或 `Box` 堆分配 |

### 反例

| 反例 | 后果 | 正确做法 |
| :--- | :--- | :--- |
| `std::thread::sleep` 在同步主循环 | 整个程序阻塞；无响应 | 改用 async 或 spawn；或非阻塞 I/O |
| 无限递归无 `Box` | 栈溢出 | `Box` 堆分配；或改为迭代 |
| 同步中 `block_on` async | 死锁风险（单线程 executor） | 用 `#[tokio::main]` 或 `spawn_blocking` |

---

## 何时选择同步

```text
需要 I/O 并发？ → 否
需要 CPU 并行？ → 否
需要跨节点？   → 否
→ 同步足够
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模型 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 同步模型由语言语义定义，1.93 无变更 |
| 92 项落点 | 无 | 见 [06_boundary_analysis](06_boundary_analysis.md#rust-193-执行模型相关变更) |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、操作语义 |
| 代码 | ✅ | 调用栈示例 |
| 场景 | ✅ | 典型场景、何时选择同步 |
| 反例 | ✅ | 阻塞 I/O、递归过深 |
| 衔接 | ✅ | async、并发对比、ownership |
| 权威对应 | ✅ | [formal_methods](../../formal_methods/README.md)、[06_boundary_analysis](06_boundary_analysis.md) |
