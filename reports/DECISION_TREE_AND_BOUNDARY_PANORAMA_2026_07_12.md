# 决策树机器可读化与边界全景页建设报告

> **日期**: 2026-07-12
> **范围**: 任务 A（决策树机器可读化 + T4 定量提升）· 任务 B（async/unsafe 边界全景页）
> **基线问题**: T4 判定定量占比 09 atlas 仅 23.8%；KG v3 `decision_trees` 仅 3 条 `{concept, tree}` 指针 stub 不可遍历；缺少领域级边界全景页

---

## 一、任务 A：决策树机器可读化

### A.1 `concept/00_meta/knowledge_topology/decision_trees.yaml`（新建）

- **规模**: 15 棵树 / 250 节点 / 266 边 / 46 个判定节点（全部含定量阈值）。
- **覆盖**:
  - 09 atlas 6 棵：`J-BORROW-01`（§3.1 借用冲突）、`J-LIFE-02`（§3.2 生命周期）、`J-TYPE-03`（§3.3 类型不匹配）、`J-PANIC-04`（§3.4 运行时 panic）、`J-UNSAFE-05`（§3.5 unsafe）、`J-CLOSED-06`（§N 闭环总图）。
  - decision_forest 9 棵：`DF-OWN-01` 所有权、`DF-BORROW-02` 借用、`DF-LIFE-03` 生命周期、`DF-TRAIT-04` Trait、`DF-GENERIC-05` 泛型、`DF-CONC-06` 并发、`DF-ASYNC-07` 异步、`DF-UNSAFE-08` Unsafe、`DF-CROSS-09` 交叉一致性（§十）。
- **节点结构**: `id` / `type ∈ {decision, conclusion, condition}`（判定/结论/条件）/ 判定条件文本 `condition` / `quantitative` + `threshold` 定量阈值；森林树保留核心路径（D → P* → R* → C* → L*）与边界节点 B*。
- **边结构**: `from` / `to` / `label ∈ {是, 否, 条件:..., 入口, 修复, 验证, ...}`。
- **覆盖概念**: 每棵树 `covered_concepts` 引用 KG v3 entities 的 `@id`（如 `ex:Borrowing`、`ex:MiriRustUndefinedBehaviorDetector`），全部经校验存在。
- **来源锚点**: 每棵树 `source.{file, anchor}` 指向原 Markdown 小节；脚本校验 `source.file` 存在。

### A.2 `scripts/check_decision_trees.py`（新建，已登记 scripts/README.md）

校验项：

| # | 校验 | 级别 |
|:---:|:---|:---|
| S1 | 结构完整性：必填字段、节点 id 唯一、type 合法、decision 必有 condition、quantitative 必有 threshold、边引用已声明节点、source.file 存在 | 错误（始终 exit 1） |
| S2 | 无死端：每个 decision 节点 ≥1 条出边；无出边叶子必须是 conclusion | 质量（`--strict` 时死端>0 ⟹ exit 1） |
| S3 | `covered_concepts` 在 KG v3（`concept/00_meta/kg_data_v3.json`）中存在 | 质量（`--strict` 时缺失>0 ⟹ exit 1） |
| S4 | 判定定量占比统计，基线 ≥50% | 质量（`--strict` 时 <50% ⟹ exit 1） |

**运行结果**（`--strict`，exit 0）:

```text
trees=15 nodes=250 edges=266
decisions=46 quantitative=46 quant_rate=100.0% (基线 ≥50%)
dead_ends=0 unknown_concepts=0
[decision-trees] PASS
```

### A.3 T4 提升：09 atlas 判定节点定量化

§3.1–§3.5 全部 21 个菱形判定节点补充了可辩护的定量条件（mermaid 标签改为带引号形式避免特殊字符解析问题）：

| 判定树 | 定量条件示例 |
|:---|:---|
| §3.1 借用冲突 | 活跃别名数 ≥2；借用活跃区间重叠 ≥1 行；迭代期增删 ≥1 次 |
| §3.2 生命周期 | 显式生命周期参数数 = 0；作用域结束行 < 引用使用行；跨 await 点数 ≥1；HRTB/dyn 出现 ≥1 次 |
| §3.3 类型不匹配 | trait bound 报错 ≥1 条；引用层级差 ≥1 层；错误类型数 ≥2 种 |
| §3.4 运行时 panic | unwrap panic ≥1 次；i ≥ len；锁等待环 ≥2；跨 FFI 调用 ≥1 次 |
| §3.5 unsafe | Miri UB 报错 ≥1 条；裸指针解引用 ≥1 次；safe API 依赖 unsafe 不变式 ≥1 个 |

**效果**（`python scripts/check_topology_quality.py --strict`，exit 0）：

| 指标 | 改造前 | 改造后 |
|:---|:---:|:---:|
| 09 atlas 判定定量占比 | **23.8%**（5/21） | **100%**（21/21） |
| 聚合 T4（03+09） | 57.8%（26/45） | **93.3%**（42/45） |
| T3 根因死端 | 0 | 0（未引入回归） |
| T3 跳出叶子率（聚合） | 16.6% | 16.5%（<20% 阈值，未回归） |

> 遗留观察（非本次范围）：09 atlas 单文件跳出叶子率 23.3%（`[[...]]` 导航节点为设计使然），聚合口径远低于 20% 阻断线；01 atlas T1 套话率 1.1%、07 atlas T2 最高频 ⟹ 83.3% 均达标。

09 atlas §一 已追加"机器可读层"说明块，链接 `decision_trees.yaml` 与校验脚本。

---

## 二、任务 B：边界全景页

### B.1 `concept/03_advanced/01_async/38_async_boundary_panorama.md`（新建，448 行）

仿 `04_safety_boundaries.md` 风格与深度：权威定义（Async Book/Tokio docs/Wikipedia）→ 认知路径 6 步 → 边界总览图 → 六类边界 → 失效模式总表 → 边界判定总图（9/9 判定节点含定量阈值）→ 分工与交叉引用 → 演进方向。

六类边界（每节 = 边界陈述 + 反例 + 定量判定条件表）：

1. **await 点语义边界** — 跨 await 活跃引用/变量进状态机字段的不对称性
2. **取消安全边界** — drop 即取消；系统化内容链 `37_async_cancellation_safety.md`
3. **Pin/自引用边界** — Unpin/!Unpin 分界、`get_unchecked_mut` 契约交接
4. **Send 跨 await 边界** — work-stealing 准入；"跨 await 活跃"的精确程序点判定
5. **Executor 与运行时边界** — poll/wake 双边契约、阻塞执行器、上下文缺失
6. **async trait/dyn 兼容边界** — RPITIT 非对象安全、async_trait 装箱代价

### B.2 `concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md`（新建，416 行）

编号确认不冲突（目录现有 29/30/31/35，32 空缺）。结构同 B.1，五类边界：

1. **UB 分类学边界** — 核心层/依赖层/非 UB 三层；开放式清单语义
2. **Stacked/Tree Borrows 模型边界** — 栈/树模型适用范围、provenance、模型演进依赖
3. **Miri 可检测 vs 不可检测边界** — 未覆盖路径/SIMD·asm·真实 FFI/非确定性采样；Kani 补位
4. **安全抽象契约边界** — validity（机器级）vs safety（库级）不变量的层次错位
5. **FFI 布局契约边界** — repr(C)/枚举判别值/allocator 配对/unwind 越界

**分工声明**: 概念推导留 `03_unsafe.md`（五类 unsafe 操作、unsafe fn/trait、SAFETY 规范），边界全景在本页；页首与 §十一 双重声明。

### B.3 注册与交叉链接

- `concept/SUMMARY.md`: 注册两条（async 38 紧随 37；unsafe 32 紧随 03_unsafe）。
- 双向交叉链接：
  - `04_safety_boundaries.md` §九 交叉引用表 +2 行（→ 两全景页，标注"本全景在 async/unsafe 域的纵深"）；
  - `03_unsafe.md` 相关概念链接 +1 行（→ 32，注明分工）；
  - `02_async.md` 相关概念链接 +1 行（→ 38，注明分工）；
  - 两新页内部互链 + 回链上述三页 + `37_async_cancellation_safety.md`、`06_pin_unpin.md`、`39_future_and_executor_mechanisms.md`、`31_miri.md`、`32_kani.md` 等。
- 元数据符合 AGENTS.md §4.2：`**EN**` + `**Summary**`（英文）、Rust 版本 1.97.0+ (Edition 2024)、Bloom 层级、权威来源声明。

---

## 三、验证结果

| 质量门 | 命令 | 结果 |
|:---|:---|:---:|
| 拓扑质量（T4 达标） | `python scripts/check_topology_quality.py --strict` | ✅ exit 0（聚合 T4 93.3%，09 atlas 100%） |
| 决策树校验 | `python scripts/check_decision_trees.py --strict` | ✅ exit 0（15 树/0 死端/0 缺失概念/定量 100%） |
| 模板套话 | `python scripts/check_template_cliches.py --strict` | ✅ exit 0（未发现命中） |
| Mermaid 语法 | `python scripts/check_mermaid_syntax.py` | ✅ 无关键语法问题 |
| 双语标注 | `python scripts/add_bilingual_annotations.py --mode check-only` | ✅ exit 0（缺 EN/Summary = 0） |
| 新页链接 | 相对链接解析脚本（2 新页 + 4 编辑文件） | ✅ 新增链接 0 死链 |

> 备注：`03_unsafe.md`/`02_async.md` 中各有 3 条**既有**目录式链接（`../../crates/c06_async`、`../02_intermediate` 等）与 1 处散文伪阳性（`[Type](raw_ptr, cx)`）在本次链接扫描中显示为不可解析——均为本次改动前已存在，非本次引入，未在任务范围内修复。

---

## 四、产出文件清单

| 操作 | 文件 |
|:---:|:---|
| 新建 | `concept/00_meta/knowledge_topology/decision_trees.yaml`（15 树/250 节点/266 边） |
| 新建 | `scripts/check_decision_trees.py`（已登记 `scripts/README.md`） |
| 新建 | `concept/03_advanced/01_async/38_async_boundary_panorama.md`（448 行） |
| 新建 | `concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md`（416 行） |
| 修改 | `concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md`（21 判定节点定量化 + 机器可读层说明） |
| 修改 | `scripts/README.md`（注册 check_decision_trees.py） |
| 修改 | `concept/SUMMARY.md`（注册 2 新页） |
| 修改 | `concept/05_comparative/03_domain_comparisons/04_safety_boundaries.md`（+2 交叉引用行） |
| 修改 | `concept/03_advanced/02_unsafe/03_unsafe.md`（+1 交叉引用行） |
| 修改 | `concept/03_advanced/01_async/02_async.md`（+1 交叉引用行） |

未做 git commit（按任务要求）。
