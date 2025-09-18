# 概览：区块链（c15_blockchain）

本模块覆盖区块、交易、共识、网络、智能合约与密码学等核心要素，配合教学示例与性能视角。

---

## 目录导航

- 基础与视图
  - [define.md](./define.md)
  - [reading_list.md](./reading_list.md)
  - 视图：`view01.md` … `view19.md`

- 课程与版本对齐
  - [university_curriculum.md](./university_curriculum.md)
  - [rust_189_features_analysis.md](./rust_189_features_analysis.md)
  - `PROJECT_COMPLETION_REPORT_2025.md`

- 源码与示例
  - `src/{cryptography,network,smart_contract,types}.rs`
  - `examples/{basic_blockchain.rs,rust_189_demo.rs}`

---

## 快速开始

1) 阅读 `define.md` 与 `view*`
2) 运行 `examples/basic_blockchain.rs`
3) 结合 `src/cryptography.rs` 理解签名与验签流程

---

## 待完善

- 增补共识算法对比与性能基准
- 与 `c20_distributed` 的分布式一致性互链

### 共识算法对比与性能基准（补全）

- 共识类型与适用性
  - PoW：开放、抗女巫但能耗高，确认延迟长，吞吐低
  - PoS（含 BFT 变体）：能源友好，经济安全性依赖质押与惩罚机制
  - PBFT/HotStuff：许可链/联盟链常用，强最终性，吞吐中高，网络放大需优化
  - Raft：工程实现简单，适合小规模许可网络（与 `c20_distributed` 中一致性内容衔接）

- 关键指标
  - 吞吐（TPS/吞吐字节数）、确认延迟/最终性时间、重组率/分叉深度
  - 节点规模的可扩展性（N→延迟/带宽变化）、网络放大/消息复杂度
  - 资源消耗：CPU/内存/存储/网络；能耗（PoW 特别关注）

- 基准方法建议
  - 统一驱动：固定交易大小与校验开销，设定出块/轮次参数
  - 可靠计时：按提交到“可见最终性”的端到端延迟统计 P50/P95/P99
  - 回放与干扰：注入丢包/抖动/延迟，评估鲁棒性与恢复时间
  - 对齐 `c20_distributed`：共用负载发生器与延迟探针，便于横向对比

- 最小基准骨架（Criterion 示例）

```rust
use criterion::{criterion_group, criterion_main, Criterion, black_box};

fn bench_pbft(c: &mut Criterion) {
    c.bench_function("pbft_1k_txn", |b| {
        b.iter(|| {
            // 伪代码：驱动 N 节点、提交固定大小交易并等待最终性
            let tps = simulate_pbft(black_box(1000));
            black_box(tps)
        })
    });
}

criterion_group!(benches, bench_pbft);
criterion_main!(benches);
```

- 实验建议
  - 节点规模：{4, 7, 13, 31}
  - 网络模型：{无损、5% 丢包、50ms 延迟、带宽限速}
  - 交易负载：{1KB、4KB、16KB}；签名算法：{Ed25519、secp256k1}
  - 报告：提供配置哈希、版本指纹与统计脚本，确保可复现实验

- 进一步阅读与实现
  - 结合 `formal_rust/language/15_blockchain` 的密码学与网络章节
  - 与 `c20_distributed` 的 Raft/一致性测试矩阵共享探针与可观测性
