# 语义关系实例化报告（relatedTo / ⟹ 反塌缩）

**日期**: 2026-07-12  **范围**: KG v3（`concept/00_meta/kg_data_v3.json`）+ atlas 07（`concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md`）
**执行脚本**: `scripts/type_kg_core_edges.py`（新增）、`scripts/extract_concept_topology.py`（修复）、`scripts/generate_knowledge_topology_atlas.py`（规则升级）
**验证**: `check_topology_quality.py` T2/T5/T6 全过；`check_kg_shapes.py` K1–K7 全过；`semantic_health.py` 64.5 → 76.8

---

## 1. 问题基线

| 位置 | 塌缩表现 |
|---|---|
| KG v3 | 5797 条边中 relatedTo 4446 条（76.7%）；schema 9 种关系中 mutexWith/refines/counterExample/equivalentTo/instanceOf/appliesTo **零实例化** |
| atlas 07 | 246 条层内关系中 ⟹ 244 条（99.2%，T2 FAIL，阈值 <95%） |
| atlas 02 | T5 单元格泄漏 3 处（`> > [元层` / `> > [综述级`） |
| atlas 01/02/08 | T6 占位字样 6 处 |

## 2. 关系推断规则（两条战线共用一套语义）

| 规则 | 关系 | atlas 符号 | 依据来源 |
|---|---|:---:|---|
| R1 策展互斥 | mutexWith | ⊥ | 权威页原句（文件:行号），见 §5 |
| R2 策展反例 | counterExample | —（KG only） | A 页"反例"章节反驳 B 的朴素假设 |
| R3 策展精化 | refines | ⊑ | A 为 B 的进阶/模式/机制展开（标题/正文声明） |
| R4 前置元数据 | dependsOn | → | 目标出现在源页 `前置概念/前置依赖` 元数据 |
| R5 后置元数据 | entails | ⟹ | 目标出现在源页 `后置概念/后置延伸` 元数据 |
| R6 对比页面 | 对比/等价 | ⇔ | 一端名称含 vs/对比 |
| R7 互参 | —（atlas only） | ↔ | 互为后置概念 |
| 默认 | entails | ⟹ | 后置概念引用（蕴含/导向） |

atlas 侧规则实现在 `generate_knowledge_topology_atlas.py::infer_relation`，每行带"依据"列；
KG 侧实现在 `type_kg_core_edges.py`，每条改动写入 `ex:evidence` / `ex:rule` / `ex:reviewed=true`。
两侧 `CURATED_MUTEX` 策展对同源一致。

## 3. atlas 07 T2 修复结果

| 指标 | 前 | 后 |
|---|---:|---:|
| 关系行数 | 246 | 463（多行 blockquote 元数据修复后抽取更完整，见 §6） |
| ⟹ 占比（T2 计口径） | 99.2% | **83.3%（pass）** |
| → dependsOn | 2 | 6 |
| ⊑ refines | 0 | 44 |
| ⊥ mutexWith | 0 | 4（全部策展，附引文） |
| ⇔ 对比 | 0 | 19 |
| ↔ 互参 | 0 | 36 |

非 ⟹ 关系共 109 条（23.5%），每条均有"依据"列说明（策展引文 / 元数据 / 名称信号 / 互参），人工可辩护。

## 4. KG 核心边类型化结果

核心子集：L1–L3 九大主题（ownership/borrowing/lifetimes/traits/generics/async/unsafe/error_handling/concurrency 及近邻）**55 个实体**，子集内边 260 → 272 条。

| 谓词 | 核心子集前 | 核心子集后 | 全局前 | 全局后 |
|:---|---:|---:|---:|---:|
| relatedTo | 145（55.8%） | **113（41.5%）** | 4446（76.7%） | **4414（76.0%）** |
| dependsOn | 72 | 84 | 688 | 700 |
| entails | 43 | 51 | 663 | 671 |
| refines | 0 | **12** | 0 | **12** |
| counterExample | 0 | **5** | 0 | **5** |
| mutexWith | 0 | **5** | 0 | **5** |

改动 42 条（R1×5 / R2×5 / R3×12 / R4×12 / R5×8），明细与逐条依据见
`reports/KG_CORE_EDGE_TYPING_2026_07_12.md`（+ `.json`）。
mutexWith / refines / counterExample 三类零实例化关系均达到 ≥5 实例目标。

## 5. 策展关系与依据（R1/R2，人工可辩护核心）

**mutexWith（5）**——对称，按列出方向落边：

1. MoveSemantics ⊥ Borrowing — `03_lifetimes.md:942`"所有权转移（move）与借用是互斥的…借用释放前不能转移其所有权"
2. PinAndUnpin ⊥ MoveSemantics — `06_pin_unpin.md:735`"Pin 通过禁止移动（对 !Unpin 类型）来解决这个问题"
3. Unions ⊥ MemoryManagement — `35_unions.md:105/250`"联合体默认不会自动 drop 字段"（与 RAII 自动析构互斥）
4. PanicAndAbort ⊥ ErrorHandling — `13_panic_and_abort.md:5/91` 不可恢复（panic/abort）与可恢复（Result）同一错误现场二选一
5. TypeLevelProgramming ⊥ RTTIAndDynamicTypeIdentification — `25_rtti_and_dynamic_typing.md:203`"RTTI 是静态类型系统向运行时的有限泄漏"（编译期 vs 运行期互斥）

**counterExample（5）**——A 的反例章节反驳 B 的朴素假设：

1. InteriorMutability → Borrowing — `02_borrowing.md:781`"AXM: 读写互斥 … UnsafeCell 突破"
2. SafeAndEffectiveUnsafeRust → Lifetimes — `03_unsafe.md:1125`"8.3 反例：悬垂裸指针（UB）"
3. SafeAndEffectiveUnsafeRust → TypeConversions — `03_unsafe.md:1140`"8.4 反例：transmute 滥用（UB）"
4. SafeAndEffectiveUnsafeRust → MemoryManagement — `03_unsafe.md:1422`"反例: Use-after-free（Miri 会报错）"
5. LockingPrimitives → Concurrency — `16_lock_free.md:409→422` 命题"无锁总是优于锁"被证伪

**refines（12）**：LifetimesAdvanced→Lifetimes、advanced_traits→Traits、AsyncAdvanced→AsyncProgramming、
error_handling_deep_dive→error_handling、unsafe_patterns→unsafe、concurrency_patterns→Concurrency、
CowAndBorrowed→Borrowing、nll_and_polonius→Borrowing、FutureAndExecutorMechanisms→AsyncProgramming、
SerdePatterns→Traits、MemoryModel→unsafe、AsyncClosures→AsyncProgramming（依据见 KG_CORE_EDGE_TYPING 报告）。

## 6. T5/T6 修复明细

**T5（02 atlas 单元格泄漏 3 处 → 0）**：根因是 `extract_concept_topology.py` 用跨行正则直接抽
blockquote 元数据，遇到多行写法（`> **内容分级**:` 换行后 `> [元层]`）把续行符 `>` 抽成脏数据。
修复：新增 `normalize_blockquote_header()`，先把头部 blockquote 规整为"每字段一行"再逐字段抽取
（顺带修复前置/后置概念多行抽取丢失问题——这是 atlas 07 关系行 246→463 的主因）；
并修正 `career_landscape.md` 的多行 `内容分级` 元数据为单行。

**T6（占位字样 6 处 → 0）**：

- `placeholder_generic.md` 行（01/02/08 共 4 处）：该页是通用占位 stub，不是概念节点 →
  `extract_concept_topology.py` 的 `EXCLUDE_DIRS` 增加 `placeholders`，从全部 atlas 排除；
- `rust_1_97_stabilized.md` 陈旧行（01/02 共 2 处）：源文件已填充为正式内容（标题/分级早已更新），
  atlas 基于过时 raw json → 重新生成后消失。

**附带修复**（再生过程中发现并根除的生成器 bug）：

- `06_inter_layer_mapping_atlas.md` 三条死链（`../inter_layer_map.md` 等）→ 修正为
  `../04_navigation/…` 与同目录 `kg_ontology_v2.md`（原为提交前手工修补，未回写生成器）；
- 01 atlas 定义列嵌入 Summary 中的"📎 交叉引用"尾注（相对链接变死链）→ 生成时剥离；
- `write_remaining_stubs()` 防覆盖护栏：03/04/05/09 已有人工策展 mermaid 内容时跳过，
  避免再生误删（此前 09 的 7 个 mermaid 判定树处于被覆盖风险中）；
- T1 定义套话率 7.0% → 1.1%（同次再生的连带收益）。

## 7. 验证结果

```
check_topology_quality.py : T1 1.1% pass · T2 ⟹ 83.3% pass · T3 16.6% pass
                            T4 57.8% pass · T5 0 pass · T6 0 pass
check_kg_shapes.py        : K1=0 K2=0 K3=0 K4=0 K5=0 K6=0 K7=0（K1b 缺 bloomLevel 55，信息项）
semantic_health.py        : 总分 64.5 → 76.8（topology 41.2 → 90.6，kg 90，dedup 84.6，meta 49.2 待治理）
```

atlas 全目录相对链接死链自检：0。

## 8. 遗留与后续

1. KG 全局 relatedTo 仍占 76.0%——本次仅类型化 L1–L3 核心子集（55 实体）；L4–L7 与跨层边可用
   同一脚本扩展 `CORE_TOPICS` 增量治理（R4/R5 元数据规则零策展成本）。
2. equivalentTo/instanceOf/appliesTo 仍零实例化——核心子集内未找到人工可辩护的实例，
   未强行标注（等价需双向语义声明，实例/适用需类型-个体层级，当前实体粒度不支持）。
3. atlas 07 的 ⊑ 行含名称启发式（"机制/模式/进阶"+同目录），依据列已透明标注；
   已知排除项："模式匹配"（控制流概念，非设计模式精化）。
4. 09 atlas 的 T3 跳出叶子率 23.5% / T4 定量占比 23.8% 为既有问题，不在本次范围。
5. 注意：会话期间 `kg_data_v3.json` 被外部进程并发修改过（新增 `ex:layer`/`ex:domain`、
   relation_count 5799→5797）；本脚本基于修改后的文件加载并全量保留，无数据丢失，
   写回时已同步 `metadata.relation_count` = 5807。
