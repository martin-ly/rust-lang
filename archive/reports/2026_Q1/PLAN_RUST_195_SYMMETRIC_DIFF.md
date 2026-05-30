# Rust 1.95 × 本项目 对称差分析与认知友好型推进计划

> **编制依据**：
> Rust 1.95.0 Release Notes (2026-04-16)、
> Rust Reference、TRPL、The Rustonomicon、Async Book、
> 各依赖库官方文档 (tokio 1.52, axum 0.8.9, hyper 1.9, rustls 0.23, quinn 0.11, libp2p 0.54.1, crossbeam 0.8.4, rayon 1.12)
> **分析维度**：语言特性 / 标准库 API / 开源生态特性 / 工程实践
> **认知原则**：由核心到外围、由语言到生态、由概念到工程、避免过度重复

---

## 一、对称差全景图

### 1.1 项目已覆盖 ↔ Rust 1.95 已稳定

| Rust 1.95 特性 | 项目覆盖 crate | 状态 |
|---|---|---|
| `if let` guards | c03, c04, c06, c07, c08, c09, c10 | ✅ 过度覆盖（8 个 crate 重复） |
| `Atomic*::update/try_update` | c05, c07, c08, c09, c10 | ✅ 过度覆盖（5 个 crate） |
| `cfg_select!` | c04, c07, c09, c10, c11, c13 | ✅ 覆盖良好 |
| `core::hint::cold_path` | c05, c07, c08, c09, c10 | ✅ 过度覆盖 |
| `core::range::RangeInclusive` | c02, c08 | ⚠️ c08 路径写错（`std::range`） |
| `bool::TryFrom<{integer}>` | c03, c04 | ✅ 恰当 |
| `ControlFlow::is_break/is_continue` (const) | c03, c06 | ✅ 恰当 |
| `MaybeUninit<[T;N]>` / `Cell<[T;N]>` 转换 | c01 | ✅ 恰当 |
| `*const/*mut T::as_ref_unchecked` | c13 | ✅ 恰当 |
| PowerPC inline asm | c13 | ✅ 恰当 |

### 1.2 Rust 1.95 有 → 项目完全缺失（核心缺口）

| 缺失特性 | 所属类别 | 认知重要性 | 建议归属 crate |
|---|---|---|---|
| `Vec::push_mut` / `Vec::insert_mut` | 集合 API | ⭐⭐⭐ 高 | c02_type_system 或 c08_algorithms |
| `VecDeque::push_front_mut` / `push_back_mut` / `insert_mut` | 集合 API | ⭐⭐⭐ 高 | c02_type_system |
| `LinkedList::push_front_mut` / `push_back_mut` | 集合 API | ⭐⭐ 中 | c02_type_system |
| `Layout::dangling_ptr` / `repeat` / `repeat_packed` / `extend_packed` | 内存布局 | ⭐⭐⭐ 高 | c01_ownership_borrow_scope / c13_embedded |
| `assert_matches!` / `debug_assert_matches!` | 测试宏 | ⭐⭐⭐ 高 | **新建 common 测试工具** 或各 crate 测试 |
| `fmt::from_fn` (const 上下文) | 格式化 | ⭐⭐ 中 | c03_control_fn |
| `irrefutable_let_patterns` lint 变更 | 语言语义 | ⭐⭐ 中 | c03_control_fn |
| 路径段关键字重命名导入 | 模块系统 | ⭐ 低 | c11_macro_system |
| const-eval padding 一致性 | 常量求值 | ⭐⭐ 中 | c13_embedded |
| `--remap-path-scope` | 编译器 | ⭐ 低 | CI/.cargo/config |

### 1.3 项目有 → 语言/生态暂无对应（教学自创/超前）

| 项目内容 | 说明 | 处理建议 |
|---|---|---|
| 大量设计模式手动实现 | c09 中 GOF 模式全部手写 | ✅ 保留，这是教学价值所在 |
| 算法/LeetCode 题解 | c08 中数百道题解 | ✅ 保留 |
| ML 算法手写实现 | c08 中 k-means、决策树等 | ⚠️ 需标注为教学实现，非生产级 |
| libp2p 0.54 `build_memory_swarm` 返回 Err | MemoryTransport 限制 | ⚠️ 技术债务，可补文档说明 |
| c12_wasm rust_195_features.rs 为空 | 仅文档字符串 | ❌ **必须填补** |

### 1.4 开源生态特性对称差

| 库 | 版本 | 项目中使用深度 | 生态新特性未覆盖 |
|---|---|---|---|
| tokio | 1.52 | ⭐⭐⭐ 深 | `task::Builder`、TaskTracker、io_uring 集成细节 |
| axum | 0.8.9 | ⭐⭐ 中 | State 改进、Error 处理新模式、嵌套路由 |
| hyper | 1.9 | ⭐⭐ 中 | HTTP/2 adaptive flow control、graceful shutdown v2 |
| rustls | 0.23.40 | ⭐⭐ 中 | FIPS 合规模式、post-quantum KEM |
| quinn | 0.11 | ⭐⭐ 中 | Datagram ( unreliable )、0-RTT、connection migration |
| libp2p | 0.54.1 | ⭐⭐⭐ 深 | WebTransport、Relay v2、AutoNAT v2、DCUtR |
| crossbeam | 0.8.4 | ⭐⭐⭐ 深 | 基本覆盖 |
| rayon | 1.12 | ⭐⭐⭐ 深 | 自定义线程池、fork-join 调优 |
| wasm-bindgen | 0.2.120 | ⭐⭐ 中 | Reference types、multi-value returns |

---

## 二、认知友好型推进计划

> **组织原则**：按"语言核心 → 标准库 → 生态对齐 → 工程验证"四层递进，每层先补缺口再优化重复。

---

### 第一层：语言核心补全（Foundation）

**认知目标**：确保 Rust 1.95 所有**语言级别**变更在项目中都有对应教学锚点。

#### 任务 1.1：修复 c08 `std::range` 路径错误

- **位置**：`crates/c08_algorithms/src/rust_195_features.rs`
- **问题**：使用了不存在的 `std::range::RangeInclusive`，应为 `core::range::RangeInclusive`
- **认知理由**：错误的路径会在学习者脑中建立错误的神经回路，必须第一时间纠正。
- **完成标准**：`cargo check --package c08_algorithms` 零错误，`RangeInclusive` 使用 `core::range` 路径

#### 任务 1.2：填补 c12_wasm 的 1.95 特性模块

- **位置**：`crates/c12_wasm/src/rust_195_features.rs`
- **现状**：仅有文档字符串，无任何可执行代码
- **内容设计**：
  - `cfg_select!`：WASI p1 vs p2 目标选择
  - `bool::TryFrom`：FFI 边界整数到 bool 的安全转换
  - `core::hint::cold_path`：WASM 异常路径优化
  - `if let` guards：wasm-bindgen 结果处理
- **认知理由**：wasm 是现代 Rust 的重要输出目标，学习者需要知道新特性在 WASM 环境下的表现。
- **完成标准**：模块内有 ≥4 个可运行的独立示例 + 配套测试

#### 任务 1.3：控制重复覆盖（建议性）

- **现状**：`if let` guards 在 8 个 crate 中重复出现，`Atomic::update` 在 5 个 crate 中重复
- **处理原则**：**不删除已有内容**（各 crate 的示例有其场景上下文价值），但在后续新特性补充时优先选择**未覆盖过该特性的 crate**
- **完成标准**：在后续任务中自然稀释重复率，无需专门清理

---

### 第二层：标准库新 API 补全（Standard Library）

**认知目标**：让学习者知道 1.95 标准库"新增了什么趁手的工具"。

#### 任务 2.1：Collection Mutable Methods 专题

- **位置**：`crates/c02_type_system/src/rust_195_features.rs`（类型系统 crate 最合适，因涉及集合类型内部表示）
- **新增内容**：
  - `Vec::push_mut` / `Vec::insert_mut`：获得新元素的 `&mut T` 引用（避免二次查找）
  - `VecDeque::push_front_mut` / `push_back_mut` / `insert_mut`：双端队列的 mutable 访问
  - `LinkedList::push_front_mut` / `push_back_mut`：链表节点的 mutable 访问
- **认知理由**：这些 API 解决的是"插入后还想修改"的真实痛点。学习者在手写数据结构时会遇到同样问题，标准库的新方法展示了最佳实践。
- **完成标准**：每个方法有独立示例 + 与旧模式的对比（"之前需要...现在只需..."）+ 测试

#### 任务 2.2：`Layout` 内存布局 Helpers 专题

- **位置**：`crates/c01_ownership_borrow_scope/src/rust_195_features.rs`（所有权与内存）或 `crates/c13_embedded/src/rust_195_features.rs`
- **新增内容**：
  - `Layout::dangling_ptr`：创建悬空但对齐的指针（用于占位）
  - `Layout::repeat` / `repeat_packed` / `extend_packed`：数组/结构体的内存布局计算
- **认知理由**：内存布局是 Rust 区别于高级语言的核心能力。`Layout` API 是从"用 Rust"到"懂 Rust"的分水岭。
- **完成标准**：示例展示手动分配内存时的布局计算 + 与 `std::alloc::alloc` 的配合使用 + 测试

#### 任务 2.3：`assert_matches!` / `debug_assert_matches!` 宏

- **位置**：各 crate 的测试模块中推广使用，或在 `common` crate 中新增测试工具示例
- **新增内容**：
  - 用 `assert_matches!` 替代 `assert!(matches!(...))` 的冗长写法
  - 在现有测试中找到 3-5 处可用 `assert_matches!` 简化的例子并重构
- **认知理由**：测试代码的可读性直接影响学习者对"Rust 风格"的理解。新宏是官方推荐的惯用法。
- **完成标准**：至少 5 个 crate 的测试中使用 `assert_matches!`，`cargo test --workspace` 通过

---

### 第三层：生态库特性对齐（Ecosystem Alignment）

**认知目标**：项目使用的开源库与官方最新能力保持同步，避免学习者学到的是"过时的用法"。

#### 任务 3.1：quinn 0.11 高级特性演示

- **位置**：`crates/c10_networks/src/quic_advanced.rs`
- **新增内容**：
  - **Datagram (unreliable)**：QUIC 不可靠数据报（适合游戏状态同步、实时音视频）
  - **0-RTT**：会话恢复时的零往返延迟
  - **Connection Migration**：连接迁移（WiFi ↔ 蜂窝切换）
- **认知理由**：quinn 0.11 不仅是"能跑 echo"，它是生产级 QUIC 实现。学习者需要知道 QUIC 相比 TCP 的核心优势在哪里。
- **完成标准**：每个特性有概念说明 + 最小代码骨架（因需要实际网络环境，测试可 mock）

#### 任务 3.2：libp2p 未覆盖模块调研与补充

- **位置**：`crates/c10_networks/src/libp2p_advanced.rs`
- **新增内容**：
  - **Relay 协议**：NAT 穿透的中继机制（与现有 NAT traversal 章节呼应）
  - **AutoNAT**：自动检测自身是否可从公网访问
  - **DCUtR**：直接连接升级通过中继（Direct Connection Upgrade through Relay）
- **认知理由**：libp2p 的完整价值在于其"拨号任何设备"的能力。仅演示 TCP+Kademlia 会让学习者误以为 P2P 就是 DHT。
- **完成标准**：每个协议有行为说明 + `libp2p::relay` / `libp2p::autonat` 的代码骨架

#### 任务 3.3：tokio 1.52 新特性补充

- **位置**：`crates/c06_async/src/` 或 `crates/c05_threads/src/`
- **新增内容**：
  - `task::Builder`：自定义 task 名称、属性（调试和监控价值）
  - `tokio::task::JoinSet::join_next_with_id`：带 ID 的任务管理
- **认知理由**：异步编程的调试和可观测性是大规模系统的关键。tokio 的新 API 直接服务于这一需求。
- **完成标准**：示例展示命名 task 在 `tokio-console` 中的效果 + 测试

---

### 第四层：工程验证与闭环（Engineering Validation）

**认知目标**：所有新增内容必须能编译、有测试、不破坏现有 CI。

#### 任务 4.1：Windows CI pcap 豁免

- **位置**：`.github/workflows/ci.yml`、`.github/workflows/pr-checks.yml`
- **修改**：Windows runner 的测试步骤使用 `--features` 白名单替代 `--all-features`，排除 `sniff`/`pcap`
- **认知理由**：工程知识包括"知道什么在哪些平台可行"。明确处理平台差异是专业 Rust 开发者的必备认知。
- **完成标准**：CI 在 Windows 上 green

#### 任务 4.2：依赖版本审计

- **位置**：`Cargo.toml` (workspace root)
- **内容**：
  - 确认所有 `workspace.dependencies` 版本与当前 Rust 1.97 nightly 兼容
  - 标记已知有兼容性风险的依赖（如 `tokio-uring` 锁定 io-uring 0.6）
  - 对 cargo machete 报告的高置信度未使用依赖进行清理（c01 serde/serde_json 等）
- **认知理由**：依赖管理是 Rust 工程能力的隐形支柱。学习者往往只关注代码而忽视供应链。
- **完成标准**：`cargo machete` 零高置信度误报，`cargo tree --duplicates` 无意外重复

#### 任务 4.3：全矩阵回归验证

- **命令**：

  ```bash
  cargo check --workspace --all-features
  cargo test --workspace
  cargo clippy --workspace --all-features -- -D warnings
  cargo doc --workspace --no-deps --all-features
  ```

- **完成标准**：全部通过

---

## 三、优先级与批次建议

| 批次 | 任务 | 预估工作量 | 认知收益 |
|---|---|---|---|
| **P0（立即）** | 1.1 修复 c08 路径错误 | 5 min | 消除错误认知 |
| **P0（立即）** | 1.2 填补 c12_wasm | 2-3 h | 消除最大空白 |
| **P1（本周）** | 2.1 Collection mut methods | 3-4 h | 标准库核心新增 |
| **P1（本周）** | 2.2 Layout helpers | 2-3 h | 内存布局深度 |
| **P1（本周）** | 2.3 assert_matches! 推广 | 1-2 h | 测试惯用法更新 |
| **P2（下周）** | 3.1 quinn 高级特性 | 4-5 h | 网络生态前沿 |
| **P2（下周）** | 3.2 libp2p 扩展 | 3-4 h | P2P 完整图景 |
| **P2（下周）** | 3.3 tokio 新特性 | 2-3 h | 异步可观测性 |
| **P3（持续）** | 4.1 CI Windows 修复 | 1 h | 工程健壮性 |
| **P3（持续）** | 4.2 依赖审计清理 | 2-3 h | 供应链健康 |
| **P3（持续）** | 4.3 回归验证 | 每轮 10 min | 质量保证 |

---

## 四、认知地图：学习者视角的 Rust 1.95

```text
Rust 1.95 新能力
├── 语言层（怎么写更优雅）
│   ├── if let guards ← 已充分覆盖（8 crate）
│   ├── cfg_select!   ← 已覆盖（6 crate）
│   └── 关键字导入重命名 / lint 变更 ← 待补
├── 标准库层（有什么新工具）
│   ├── Atomic::update/try_update ← 已覆盖（5 crate）
│   ├── core::range::RangeInclusive ← 已覆盖（2 crate，但有路径错误）
│   ├── core::hint::cold_path ← 已覆盖（5 crate）
│   ├── bool::TryFrom ← 已覆盖（2 crate）
│   ├── MaybeUninit/Cell 转换 ← 已覆盖（1 crate）
│   ├── 指针 as_ref_unchecked ← 已覆盖（1 crate）
│   ├── Vec/VecDeque/LinkedList mut methods ← ❌ 完全缺失
│   ├── Layout helpers ← ❌ 完全缺失
│   └── assert_matches! ← ❌ 完全缺失
├── 生态层（库的最新能力）
│   ├── tokio task::Builder ← 未覆盖
│   ├── quinn datagram/0-RTT/migration ← 未覆盖
│   ├── libp2p Relay/AutoNAT/DCUtR ← 未覆盖
│   └── axum/hyper/rustls 新特性 ← 未系统覆盖
└── 工程层（怎么用得靠谱）
    ├── CI 跨平台一致性 ← 待修复
    ├── 依赖清理 ← 待执行
    └── 测试覆盖率 ← 持续提升
```

---

## 五、风险与注意事项

1. **c12_wasm 的特殊性**：wasm32 目标下部分 1.95 API 可能不可用（如 `core::hint::cold_path` 的语义可能与 native 不同），需用 `#[cfg(target_arch = "wasm32")]` 做适当条件编译。
2. **quinn/libp2p 高级特性的测试难度**：涉及实际网络交互的代码难以在单元测试中覆盖，建议以"概念骨架 + 文档说明"为主，辅以 mock 测试。
3. **避免过度工程**：`Layout::repeat` 等 API 偏底层，示例应保持教学简洁，不引入完整的分配器实现。
4. **unsafe_code = "forbid"**：`Layout` 示例中如需使用 `std::alloc::alloc`，需用 `#[allow(unsafe_code)]` 局部豁免并附安全说明。
