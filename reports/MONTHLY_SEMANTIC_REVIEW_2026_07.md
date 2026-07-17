# 月度语义评审报告（2026-07）

**Review period**: 2026-07
**Reviewer**: Kimi Code CLI
**Scope**: `concept/` 权威页漂移、边界语义、stub 纯度、KG 关系质量、版本语义注入覆盖

---

## 1. 执行摘要

本月度评审覆盖 2026-07 语义模型对齐 sprint 完成后的全库状态。所有 23 个阻断质量门与 5 个语义观察门均通过，KG 关系质量达到核心 generic_ratio=0.00%，content overlap 可处理项为 0，跨层引用一致。

## 2. 核心概念定义漂移检查

抽查 10 个 L1–L4 核心 `concept/` 页：

| # | Page path | Definition checked | Drift found? | Action item |
|---|-----------|--------------------|--------------|-------------|
| 1 | `concept/01_foundation/02_type_system/01_type_system.md` | 类型系统核心定义 | No | — |
| 2 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 所有权三规则 | No | — |
| 3 | `concept/02_intermediate/00_traits/01_traits.md` | trait 语义 | No | — |
| 4 | `concept/02_intermediate/01_generics/01_generics.md` | 泛型与约束 | No | — |
| 5 | `concept/03_advanced/01_async/01_async.md` | async/await 状态机 | No | — |
| 6 | `concept/03_advanced/02_unsafe/01_unsafe.md` | unsafe 边界 | No | — |
| 7 | `concept/03_advanced/00_concurrency/03_concurrency_patterns.md` | 并发模式 | No | — |
| 8 | `concept/04_formal/00_type_theory/10_dependent_refinement_types.md` | 依赖/细化类型 | No | — |
| 9 | `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md` | 代数效应 | No | — |
| 10 | `concept/03_advanced/01_async/15_state_machine_semantics.md` | 状态机语义（本月新建） | No | — |

**结论**：抽查页面定义清晰、无循环定义、Rust 版本标注与 1.97.0 stable / nightly 标记一致，反例节存在且代码块标注未腐烂。

## 3. 边界精度评审

运行：

```bash
python scripts/check_cross_domain_coverage.py --strict
```

结果：**16/16 关键交叉语义域覆盖**，观察门通过。

已覆盖主题包括：let chains、unsafe extern blocks、async+unsafe、FFI+async、no_std+async、const generics+trait objects、GAT+async、Send/Sync boundaries、Pin projection、allocator_api、match ergonomics、temporary scope、const trait impl、RTN/RPITIT/TAIT、async fn / Future、unsafe op in unsafe fn。

## 4. Stub 纯度评审

运行：

```bash
python scripts/check_stub_purity.py --strict
```

结果：

- 伪 stub：0
- 空壳页：0
- 高重复正文：0

**结论**：`knowledge/` / `docs/` / `content/` / `crates/*/docs/` 中声明为 stub/redirect 的文件保持纯净。

## 5. KG 关系质量评审

运行：

```bash
python scripts/check_kg_shapes.py --strict
python scripts/check_kg_relation_precision.py --strict
```

结果：

- `kg_data_v3.json`：**540 entities / 8410 relations**
- `KG SHACL`: K1–K7 全 0
- `KG Relation Precision`: global **0.00%**, core **0.00%**
- `ex:relatedTo` 剩余 **834** 条（约 9.9%），主要为同层跨目录弱语义关联
- 关系表示一致性：`@type` 与 `ex:predicate` 完全同步，mismatch=0

当前谓词分布：

| 谓词 | 数量 |
|---|---:|
| `ex:hasPart` | 3696 |
| `ex:dependsOn` | 1677 |
| `ex:entails` | 1223 |
| `ex:relatedTo` | 834 |
| `ex:partOf` | 430 |
| `ex:refines` | 429 |
| `ex:appliesTo` | 121 |

**KG 刷新流水线（AGENTS.md §7）**：

1. `python scripts/generate_kg_index.py`
2. `python scripts/generate_kg_v3.py`
3. `python scripts/apply_kg_semantic_predicates.py --all-batches --apply`
4. `python scripts/fallback_kg_generic_to_related.py --apply`
5. `python scripts/compress_kg_relatedto.py --apply`
6. `python scripts/check_kg_shapes.py --strict`
7. `python scripts/check_kg_relation_precision.py --strict`

本月新增 `scripts/compress_kg_relatedto.py`，将 relatedTo 从 ~6800 压缩至 1003。

## 6. 版本语义注入覆盖

运行：

```bash
python scripts/check_version_semantic_injection.py --strict
```

结果：**Rust 1.90–1.97 共 74 个稳定特性，100% 映射**到 `concept/` 权威页。

## 7. 质量门汇总

最终全质量门运行：

```bash
bash scripts/run_quality_gates.sh
```

**日志**: `tmp/quality_gates_final_v11_web_updates_2026_07_16.log`
**结果**: ✅ **All 23 blocking + 5 semantic observe gates passed**

| 门 | 状态 | 关键指标 |
|---|---|---|
| Cargo check / test / clippy / audit / vet | ✅ | 全通过 |
| mdbook build | ✅ | 通过 |
| KB Auditor link check | ✅ | 死链 0，跨层问题 0 |
| Content Overlap v2 | ✅ | MERGE+DOCS_INTERNAL=0 |
| Bilingual annotations | ✅ | 通过 |
| Mermaid syntax | ✅ | 通过 |
| Topology quality | ✅ | 通过 |
| KG SHACL | ✅ | K1–K7=0 |
| Canonical uniqueness | ✅ | 通过 |
| Concept consistency | ✅ | 0 错误 |
| Naming convention | ✅ | ERROR=0 |
| Quiz system | ✅ | 22/22，324/324 |
| Metadata consistency | ✅ | D1–D5=0 |
| Concept code blocks | ✅ | rot=0 |
| Mindmap coverage | ✅ | mindmap 99.8%，反例 97.0% |
| Semantic health | ✅ | 99.3 grade=OK |
| Authority coverage | ✅ | any=100%，core gaps=0 |
| Examples compile | ✅ | 11+3+2 全通过 |

## 8. 发现与待办

1. **KG 关系表示一致性 bug 已修复**：`compress_kg_relatedto.py` 与 `fallback_kg_generic_to_related.py` 此前只更新 `@type` 而未同步 `ex:predicate`，导致 5838 条关系二者不一致；已修复并重新跑通 KG 流水线，`@type` 与 `ex:predicate` 现在完全一致。
2. **新增 meta 组织者启发式（H14/H15）**：`00_meta/00_framework` 与 `00_meta/knowledge_topology` 页面与其余 00_meta 子系统页面之间的关系按 `hasPart` / `partOf` 压缩，使 `ex:relatedTo` 从 1003 条降至 916 条。
3. **新增根导航启发式（H0）**：`SUMMARY.md` / `README.md` 作为全书根导航，其所有出边统一压缩为 `ex:hasPart`；进一步扩展 H0 到所有子目录的 `README.md`，使 `ex:relatedTo` 从 916 条降至 **834 条**。
4. **剩余 834 条 `ex:relatedTo`**：主要为同层跨目录概念页之间的弱语义关联（`06_ecosystem`、`01_foundation`、`03_advanced` 等同层跨子域），已无法通过安全启发式自动压缩，需未来通过 atlas 符号或人工策展继续迁移到更强谓词。
5. **生态跟踪**：wgpu 25.x、openraft 0.10 alpha 线已在对应 concept/ 页更新；后续需在新版本发布时回查。
6. **workflow/statecharts**：`15_state_machine_semantics.md`（L3-L4）与 `17_workflow_theory.md`（L6）职责划分已建立，无需额外拆分。

## 9. 结论

2026-07 月度语义评审结论：**知识库语义健康，所有阻断门与观察门通过，无漂移、无死链、无伪 stub、无通用谓词残留**。下月重点建议：监控 Rust 1.98.0 stable 发布（预计 2026-08-20）并核对 `rust_1_98_stabilized.md`。

---

*报告生成: 2026-07-16*
*对应 sprint 报告: `reports/SEMANTIC_MODEL_ALIGNMENT_PROGRESS_2026_07_16.md`*
