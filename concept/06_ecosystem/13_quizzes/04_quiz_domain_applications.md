# 测验：领域应用生态（L6）

> **EN**: Domain Applications Ecosystem Quiz
> **Summary**: L6 standalone quiz on Rust's domain application ecosystems: blockchain contracts and deterministic execution, WebAssembly targets and JS interop, game ECS architecture, the ML/data-science stack, safety-critical AUTOSAR alignment, quantum computing toolkits, and competitive programming with formal verification.
> **受众**: [专家]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L6 生态层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [区块链](../11_domain_applications/01_blockchain.md) · [WebAssembly](../11_domain_applications/03_webassembly.md) · [游戏 ECS](../11_domain_applications/02_game_ecs.md) · [机器学习生态](../11_domain_applications/13_machine_learning_ecosystem.md) · [AUTOSAR 与 Rust](../11_domain_applications/22_autosar_and_rust.md) · [量子计算](../11_domain_applications/16_quantum_computing_rust.md) · [算法竞赛](../11_domain_applications/07_algorithms_competitive_programming.md) · [docs.rs — Rust crate 生态权威文档](https://docs.rs)（curl 200 实测 2026-07-13）
>
> **前置概念**:
> [区块链](../11_domain_applications/01_blockchain.md) ·
> [WebAssembly](../11_domain_applications/03_webassembly.md) ·
> [游戏 ECS](../11_domain_applications/02_game_ecs.md) ·
> [机器学习生态](../11_domain_applications/13_machine_learning_ecosystem.md) ·
> [安全关键专题索引](../11_domain_applications/21_safety_critical_topic_index.md) ·
> [AUTOSAR 与 Rust](../11_domain_applications/22_autosar_and_rust.md) ·
> [Rust vs Go（并发模型对比）](../../05_comparative/01_systems_languages/03_rust_vs_go.md)

---

> **Bloom 层级**: L2-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对 L6 领域应用子领域（区块链、Wasm、游戏、ML、安全关键、量子、算法竞赛）生态格局与选型的掌握。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、区块链与 WebAssembly

本节考查区块链与 Wasm 领域：Q1 对照区块链权威页，Q2 匹配 Wasm target 三元组与部署场景。

### Q1. 🟢【单选】按 [区块链](../11_domain_applications/01_blockchain.md) §1.1，Rust 智能合约相对 Solidity/EVM 的本质安全增益是？

- A. 运行时（Runtime）插入更多安全检查（类似 Solidity 0.8 checked math）
- B. 让整类漏洞（重入、溢出、未初始化存储）在编译期成为不可类型化的程序——从"防御性编程"到"构造性安全"
- C. 提供 gas 自动优化
- D. 用 GC 统一管理合约内存

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：权威页的漏洞对照表：所有权（Ownership） + `&mut` 独占访问 ⟹ 重入攻击在编译期不可表达；`u64`/`u128` 默认 overflow panic + `checked_add` 显式处理 ⟹ 整数溢出显式化；`Option<T>` + 编译期初始化检查 ⟹ 不存在未初始化存储指针。核心洞察是"让整类漏洞在编译期成为不可类型化的程序"。A 是 Solidity 的运行时路线；D 与区块链确定性执行要求矛盾（无 GC 才保证确定性）。

</details>

---

### Q2. 🟢 以下 Wasm 目标三元组与场景的对应，哪项正确？

```text
wasm32-unknown-unknown  —— sys: unknown（无操作系统）
wasm32-wasip1 / wasip2  —— sys: wasi（WebAssembly System Interface）
```

| 选项 | 判断 |
|:---|:---|
| A | 浏览器内 Wasm（经 wasm-bindgen 与 JS 交互）用 `wasm32-unknown-unknown`；服务端/边缘（文件系统、时钟等系统资源）用 `wasm32-wasip1/wasip2` + wasmtime |
| B | 两个目标完全等价，可随意互换 |
| C | `wasm32-unknown-unknown` 可直接使用 `std::fs`/`std::net` |
| D | WASI 目标只能运行在浏览器中 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：A。

**解析**：按 [WebAssembly](../11_domain_applications/03_webassembly.md) §2.1：`wasm32-unknown-unknown` 面向浏览器（无 OS，无文件系统/网络/`std::fs`/`std::net`），通过 wasm-bindgen 与 JS 交互；`wasm32-wasip1/wasip2` 面向服务端 Wasm，经 WASI 访问文件系统、环境变量、时钟、随机数。B/C/D 均与目标能力矩阵矛盾。

</details>

---

### Q3. 🟡【判断】`wasm-bindgen` 宏自动生成 JS 胶水代码与 Wasm 导入/导出包装，处理字符串编码（UTF-8 ↔ UTF-16）、JS 对象句柄管理与 panic → JS Error 的异常转换。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：按 [WebAssembly](../11_domain_applications/03_webassembly.md) §2.2，`#[wasm_bindgen]` 宏（Macro）生成 JS 胶水层，自动处理三类互操作负担：字符串编码转换、对象引用（JS 对象句柄表）管理、Rust panic 到 JS Error 的异常转换。开发者只需在 Rust 函数/结构体（Struct）/impl 上标注即可暴露给 JS。

</details>

---

### Q4. 🟡【多选】关于 Rust 区块链架构谱系，下列说法与权威页一致的有？（选出所有正确项）

- A. Solana 的 Sealevel 引擎支持并行合约执行，运行时对账户状态做与 Rust 编译期借用（Borrowing）检查同构的运行时借用检查
- B. Polkadot 基于 Substrate 框架与异构分片（平行链）模型
- C. Rust 合约的执行确定性来自无 GC 的内存管理——消除 GC 暂停与内存布局非确定性
- D. 类型系统（Type System）可以阻止 `block.timestamp` 被矿工/验证者操纵

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A/B/C 均出自 [区块链](../11_domain_applications/01_blockchain.md) §1.2 与 §二：Sealevel 并行执行 + 运行时借用检查、Substrate 异构分片、无 GC 确定性。D 错——权威页明确：时间操纵（timestamp manipulation）是类型系统**无法**阻止的漏洞类别，只能靠 `Instant`/`Slot` 类型强制显式处理，属"构造性安全"的边界案例。

</details>

---

## 二、游戏 ECS 架构

本节考查游戏 ECS：Q5 对照 ECS 权威页，Q6 用访问冲突规则判断两个 System 能否并行。

### Q5. 🟢【单选】按 [游戏 ECS](../11_domain_applications/02_game_ecs.md) §1.1 的形式化对应，ECS 三要素的 Rust 表达是？

- A. Entity=trait 对象、Component=枚举（Enum）、System=宏
- B. Entity=`u64` 包装标识符、Component=`#[derive(Component)]` 的 POD struct、System=带 `Query` 参数的普通函数
- C. Entity=全局变量、Component=闭包（Closures）、System=线程
- D. 三者都必须用 unsafe 实现

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：权威页的对应表：Entity 是轻量级标识符（`u64` 包装类型，无效 Entity 经 `Option` 显式处理）；Component 是纯数据结构（POD，`struct` + `#[derive(Component)]`）；System 是数据转换函数 `fn(Query<...>)`，借用检查器验证组件访问不冲突；World 是组件存储（SoA/Archetype）。核心洞察：ECS 的"数据与行为分离"与 Rust 的"数据与所有权分离"同构。

</details>

---

### Q6. 🟡 以下 Bevy 风格的两个 System，调度器能否并行执行它们？

```rust,ignore
fn move_system(mut q: Query<&mut Transform>) { /* ... */ }
fn render_system(q: Query<&Transform>) { /* ... */ }
```

| 选项 | 判断 |
|:---|:---|
| A | 可以并行：两个 System 从不同时运行 |
| B | 不能并行：`&mut Transform` 与 `&Transform` 访问同一组件类型且其一为独占访问，借用冲突使调度器串行化二者 |
| C | 可以并行：ECS 不使用借用检查 |
| D | 编译错误：同一组件类型不能被两个 System 查询 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：按 [游戏 ECS](../11_domain_applications/02_game_ecs.md) 认知路径第 3 步：借用检查成为 ECS 的调度安全网——System 的 `Query` 参数声明组件访问（读/写），写访问 `&mut` 与读访问 `&` 对同一组件构成冲突，调度器据此把冲突 System 串行化、无冲突 System 并行化，编译期/调度期消除数据竞争。C 错（ECS 恰恰复用借用语义）；D 错（合法，只是不能并行）。

</details>

---

### Q7. 🔴【判断】按权威页的 ER 图分析，System 不直接持有 Component，而是通过 World 间接查询（`Query`），这种间接性是 ECS 并行调度安全的前提。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：[游戏 ECS](../11_domain_applications/02_game_ecs.md) §1.1 的 ER 图认知说明明确：System 经 World 间接查询 Component——World 作为中心枢纽组织 Entity/Component/Archetype 的关联。正因为组件访问必须经过 `Query` 声明，调度器才能静态分析访问冲突并安全并行化；若 System 直接持有组件引用（Reference），所有权与别名关系将无法在系统边界上静态判定。这也是 SoA/Archetype 存储缓存友好性的架构前提。

</details>

---

## 三、机器学习与数据科学

本节考查 ML 与数据科学：Q8 生态定位，Q9 三层划分对应，Q10 评估「Rust 重写推理服务」的论据有效性。

### Q8. 🟡【单选】按 [机器学习生态](../11_domain_applications/13_machine_learning_ecosystem.md) 的属性矩阵，四个深度学习 crate 的定位对应正确的是？

- A. candle=PyTorch 绑定、burn=ONNX 推理、tch-rs=纯 Rust 推理、ort=训练框架
- B. candle=纯 Rust 推理引擎（HF）、burn=可移植训练+推理框架、tch-rs=PyTorch C++ API 绑定、ort=ONNX Runtime 绑定
- C. 四者都是纯 Rust 实现，无任何 C++ 依赖
- D. 四者都只支持 CPU

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：权威页属性矩阵：candle（HF 出品，纯 Rust 推理，GGML/Safetensors 导入，CUDA/Metal）、burn（纯 Rust，训练+推理完整，WGSL/CUDA 后端）、tch-rs（绑定 libtorch，迁移 PyTorch 模型，CUDA/ROCm）、ort（绑定 ONNX Runtime，跨平台推理部署）。C 错——tch-rs 依赖 libtorch、ort 依赖 ONNX Runtime（C++）；D 错——candle/burn/tch-rs/ort 均有 GPU 路径。

</details>

---

### Q9. 🟡【多选】关于 Rust 数据科学生态的三层划分，下列对应正确的有？（选出所有正确项）

- A. 存储层：列式内存格式与文件格式——`arrow-rs`、`parquet`
- B. 计算层：查询执行与 DataFrame 操作——`datafusion`、`polars`
- C. 应用层：ML 算法与模型推理——`linfa`、`candle`、`burn`
- D. 三层是竞争关系，同一 crate 只能属于一层

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：按 [机器学习生态](../11_domain_applications/13_machine_learning_ecosystem.md) §1.2 的分层表：存储层（arrow-rs/parquet，数据交换标准）→ 计算层（datafusion/polars，高性能分析）→ 应用层（linfa/candle/burn，端到端 ML）。数据流为：原始数据 → Arrow 格式 → DataFrame/查询 → 特征工程 → 训练 → 推理。D 错——三层是**互补**关系而非竞争，crate 按主要定位分层。

</details>

---

### Q10. 🔴 某团队论证"用 Rust 重写 Python 的 ML 推理服务"。按权威页，下列哪条论据与 Rust ML 生态的差异化定位一致？

| 选项 | 论据 |
|:---|:---|
| A | Rust 生态的模型与算子覆盖已全面超越 PyTorch/TensorFlow |
| B | 零成本抽象（Zero-Cost Abstraction） + 内存安全（Memory Safety） + 无 GIL 限制，适合高并发低延迟推理与边缘部署；但生态（尤其训练侧）仍在追赶 Python |
| C | Rust 没有 GC，因此任何 ML 代码都自动更快 |
| D | 选择 Rust 的主要原因是其动态类型更灵活 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：[机器学习生态](../11_domain_applications/13_machine_learning_ecosystem.md) §1.1 明确核心差异化：零成本抽象 + 内存安全 + 无 GIL 限制——这对多线程推理服务与边缘/WASM 部署是直接收益（candle 定位即"边缘推理"）。但权威页同时展示生态全景仍在建设：训练能力以 burn/tch-rs 为主，模型生态与 Python 差距明显。A 过度承诺；C 把必要条件当充分条件；D 事实错误（Rust 是静态类型）。

</details>

---

## 四、安全关键与 AUTOSAR

本节考查安全关键领域：Q11–Q13 围绕 AUTOSAR 的 Rust 进程、R23-11 文档与 Rust 的安全论证价值。

### Q11. 🟡【单选】按 [AUTOSAR 与 Rust](../11_domain_applications/22_autosar_and_rust.md)，Classic Platform（CP）与 Adaptive Platform（AP）的分工是？

- A. CP=高性能 SoC + POSIX + 服务导向通信；AP=MCU + 信号导向通信
- B. CP=MCU 资源受限 + C 基线 + 信号导向（CAN/LIN/FlexRay）+ RTE 静态生成；AP=高性能计算单元 + POSIX OS + C++14 基线 + 服务导向（SOME/IP、DDS）
- C. 两者硬件与通信模型完全相同的两个 API 方言
- D. CP 只用于座舱，AP 只用于动力

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：权威页 §一的分工表：CP 面向 MCU（AURIX/RH850）、C 语言基线、信号导向通信（CAN/LIN/FlexRay）、RTE 静态生成、至 ASIL D，典型场景为动力/底盘/车身 ECU；AP 面向高性能 SoC、POSIX OS（Linux/QNX）、C++14 基线（含 500+ 页编码指南）、服务导向通信（SOME/IP、DDS、`ara::com` 动态绑定），典型场景为自动驾驶/座舱/中央计算/OTA。A 把两者颠倒；C/D 与表矛盾。

</details>

---

### Q12. 🔴【判断】AUTOSAR R23-11 发布的 *Explanation of ARA Applications in Rust* 是规范性（normative）API 标准，Rust 绑定已成为 AP 的官方强制接口。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：按 [AUTOSAR 与 Rust](../11_domain_applications/22_autosar_and_rust.md) §2.2：R23-11（2023-11）该文档编号 1079，性质是 **EXP（Explanation，解释性文档）**——首次在标准文档层面给出用 Rust 开发 AP 应用的初步框架，但**不是规范性 API**；R24-11 发布更新版。它是官方认可的实践路径说明，不是强制接口。Rust 进入 AUTOSAR 的正式进程始于 2022 年 WG-SAF Rust 小组成立。

</details>

---

### Q13. 🔴【多选】按 WG-SAF 公开材料，Rust 对 AUTOSAR 安全论证的价值包括？（选出所有正确项）

- A. 编译器保证的内存安全（soundness）消除 C/C++ 中 UB 类缺陷的论证负担（访谈数据：约 90% 传统静态分析检查被编译器覆盖）
- B. `Send`/`Sync` 并发约束在编译期排除数据竞争，支撑 freedom from interference 论证
- C. 显式生命周期（Lifetimes）把 C++ 中"文档约定"的生命周期变为可机器检查
- D. Rust 的 async 模型在 AUTOSAR 中无任何工程权衡，可直接全面替代 C++20 `co_await`

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：[AUTOSAR 与 Rust](../11_domain_applications/22_autosar_and_rust.md) §三的论证表：内存安全 soundness（约 90% 传统静态分析检查被编译器覆盖）、`Send`/`Sync` 支撑无干扰论证、显式生命周期机器可检查、显式 `pub`/`mut`/`Result` 传播对应控制流可追溯性，以及 miri/kani/prusti/loom/creusot 验证工具链可纳入 V&V 证据链。D 错——权威页明确 async 对应 `co_await` 但存在"染色"效应（阻塞/异步混用成本），仍需工程权衡。

</details>

---

## 五、量子计算与算法竞赛

本节考查前沿领域：Q14 roqoqo 量子电路库的架构定位，Q15 Rust 在算法竞赛中的定位。

### Q14. 🔴 以下 roqoqo 电路代码体现了该库的什么架构定位？

```rust,ignore
use roqoqo::{Circuit, operations::*};
let mut circuit = Circuit::new();
circuit += Hadamard::new(0);
circuit += CNOT::new(0, 1);
circuit += MeasureQubit::new(0, "ro".to_string(), 0);
```

| 选项 | 判断 |
|:---|:---|
| A | roqoqo 是完整的量子算法库，内置 Shor/Grover 实现 |
| B | roqoqo 是纯 Rust 的量子电路表示/中间表示（IR）工具包，提供 Circuit/QuantumProgram/测量定义与序列化，但不含电路优化器或算法库；经 qoqo（Python 绑定）与多后端（QuEST/Qiskit/Braket/IQM）对接 |
| C | roqoqo 只能在 Python 中通过 qoqo 间接使用 |
| D | roqoqo 是量子硬件的固件 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：按 [量子计算](../11_domain_applications/16_quantum_computing_rust.md) §3.1：roqoqo（HQS Quantum Simulations 维护）是纯 Rust 量子电路表示库，定位是**可移植的量子程序中间表示（IR）**——明确不包含电路优化器或算法库；其 Python 封装 qoqo 构成"Rust 核心 + Python 绑定"架构，后端生态含 roqoqo-quest（QuEST C 模拟器）、qoqo-qiskit、qoqo-for-braket、qoqo-iqm。A/C/D 均与定位矛盾。

</details>

---

### Q15. 🟡【多选】关于 Rust 在算法竞赛中的定位，下列说法与 [算法竞赛](../11_domain_applications/07_algorithms_competitive_programming.md) 一致的有？（选出所有正确项）

- A. 运行时性能经零成本抽象与 C++ 同级，但编译速度慢于 C++（增量编译缓解）
- B. 标准库提供 `slice::sort`（Timsort）、`BinaryHeap` 等竞赛常用构件
- C. 竞赛模板库生态已与 C++（AC Library 等）同等成熟
- D. VeriContest 基准（946 题）显示排序/搜索类 100% 可形式验证，动态规划约 72%，瓶颈在规约书写成本而非工具

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、D**

**解析**：权威页 §1.1 定位表：性能与 C++ 同级、内存安全编译期保证、编译速度是短板（增量编译缓解）；标准库算法（Timsort `slice::sort`、`BinaryHeap`）齐备。D 出自 §1.2 VeriContest（Rust + Verus，946 道 LeetCode/Codeforces 题）：排序搜索 100% 可验证、图算法约 85%、动态规划约 72%、字符串约 68%，关键洞察是瓶颈在**规约书写成本**（竞赛场景验证开销约为编码 2–5 倍）。C 错——权威页明确 Rust 竞赛模板库较少、社区仍在成长。

</details>

---

> **变更记录**: 2026-07-13 新建（W3-b：L6 领域应用 quiz 补缺，15 题：单选 4 / 代码阅读 4 / 多选 4 / 判断 3；难度 🟢3 / 🟡7 / 🔴5；覆盖区块链/Wasm/游戏 ECS/ML/安全关键 AUTOSAR/量子/算法竞赛）。
> **内容分级**: [综述级]
