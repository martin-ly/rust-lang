#!/usr/bin/env python3
"""update_quiz_registry.py — 测验注册表统计重算（W3-b）

从实际文件重算 `concept/00_meta/quiz_registry.yaml` 的全部机器可校验字段：
  - standalone_quizzes：题数 / 元测验数 / 题型构成 / 难度分布 / 双向链接状态
    （path / layer / topic / concept_pages 以现有注册表 + 下方 SEED 为准，不重算）
  - embedded_quizzes：页数 / 块数 / 逐页清单（concept/ 下含 `### 测验 N` 块的非独立 quiz 页）

复用 scripts/check_quiz_system.py 的分析逻辑，保证注册表与检查器口径一致。

用法：
  python scripts/update_quiz_registry.py
"""
from __future__ import annotations

import importlib.util
import pathlib
import sys

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "concept" / "00_meta" / "quiz_registry.yaml"

spec = importlib.util.spec_from_file_location(
    "check_quiz_system", ROOT / "scripts" / "check_quiz_system.py"
)
cqs = importlib.util.module_from_spec(spec)
sys.modules["check_quiz_system"] = cqs
spec.loader.exec_module(cqs)

# W3-b 新增独立 quiz 的种子条目（path/layer/topic/concept_pages 人工定义，
# 其余字段由本脚本从文件重算）。
SEED = [
    {
        "path": "concept/00_meta/05_quizzes/01_quiz_meta_framework.md",
        "layer": "L0",
        "topic": "元层框架与知识体系架构（L0–L7 分层、Bloom 映射、A/S/P 标记、canonical 规则）",
        "concept_pages": [
            "concept/00_meta/README.md",
            "concept/00_meta/00_framework/bloom_taxonomy.md",
            "concept/00_meta/03_audit/02_asp_marking_guide.md",
            "concept/00_meta/00_framework/methodology.md",
        ],
    },
    {
        "path": "concept/07_future/05_quizzes/01_quiz_version_and_preview.md",
        "layer": "L7",
        "topic": "版本演进、Edition 机制与前沿特性（发布火车、1.90–1.97 稳定特性、preview 状态）",
        "concept_pages": [
            "concept/07_future/00_version_tracking/02_editions.md",
            "concept/07_future/00_version_tracking/03_rust_release_process.md",
            "concept/07_future/00_version_tracking/rust_1_97_stabilized.md",
        ],
    },
    {
        "path": "concept/06_ecosystem/13_quizzes/01_quiz_networking_async_ecosystem.md",
        "layer": "L6",
        "topic": "网络与异步生态（Web 框架、Tokio/Glommio 运行时、QUIC/HTTP-3、eBPF）",
        "concept_pages": [
            "concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md",
            "concept/06_ecosystem/04_web_and_networking/07_network_protocols.md",
            "concept/06_ecosystem/04_web_and_networking/05_glommio_and_thread_per_core.md",
        ],
    },
    {
        "path": "concept/06_ecosystem/13_quizzes/02_quiz_database_storage.md",
        "layer": "L6",
        "topic": "数据库与存储生态（SQLx/Diesel/SeaORM/Toasty、TiKV/Materialize/Meilisearch/SurrealDB）",
        "concept_pages": [
            "concept/06_ecosystem/06_data_and_distributed/02_database_access.md",
            "concept/06_ecosystem/06_data_and_distributed/04_database_systems.md",
        ],
    },
    {
        "path": "concept/06_ecosystem/13_quizzes/03_quiz_security_testing.md",
        "layer": "L6",
        "topic": "安全与测试生态（Kerckhoffs 原则、crypto 原语、cargo vet/audit、分层测试）",
        "concept_pages": [
            "concept/06_ecosystem/07_security_and_cryptography/01_security_practices.md",
            "concept/06_ecosystem/07_security_and_cryptography/02_security_cryptography.md",
            "concept/06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md",
            "concept/06_ecosystem/09_testing_and_quality/01_testing_strategies.md",
        ],
    },
]


def main() -> int:
    registry = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    quizzes = registry.get("standalone_quizzes", [])
    known = {q["path"] for q in quizzes}
    for seed in SEED:
        if seed["path"] not in known:
            quizzes.append(dict(seed))
            print(f"+ seed: {seed['path']}")

    # 重算独立 quiz 字段
    for q in quizzes:
        path = ROOT / q["path"]
        if not path.exists():
            print(f"! missing: {q['path']}", file=sys.stderr)
            continue
        a = cqs.analyze_quiz(path)
        q["questions"] = a["questions"]
        q["meta_questions"] = a["meta"]
        q["question_types"] = sorted(a["types"])
        q["difficulty"] = a["diff"]
        qtext = path.read_text(encoding="utf-8")
        cps = [ROOT / cp for cp in q.get("concept_pages", [])]
        q["quiz_to_concept"] = any(
            cp.exists() and cqs.has_link_to(qtext, path, cp) for cp in cps
        )
        q["concept_to_quiz_backlink"] = any(
            cp.exists()
            and cqs.has_link_to(cp.read_text(encoding="utf-8"), cp, path)
            for cp in cps
        )

    # 重算嵌入式测验统计
    quiz_set = {q["path"] for q in quizzes}
    items, total = [], 0
    for p in sorted((ROOT / "concept").rglob("*.md")):
        rel = p.as_posix().split("rust-lang/", 1)[-1]
        if rel in quiz_set:
            continue
        n = len(cqs.EMBED_HEAD.findall(p.read_text(encoding="utf-8", errors="replace")))
        if n:
            items.append({"path": rel, "blocks": n})
            total += n
    registry["embedded_quizzes"] = {
        "description": "concept/ 页面内嵌入式测验（### 测验 N + <details> 答题块），按页聚合",
        "pages": len(items),
        "total_blocks": total,
        "items": items,
    }
    registry["generated"] = "2026-07-12"

    REGISTRY.write_text(
        yaml.safe_dump(registry, allow_unicode=True, sort_keys=False, width=120),
        encoding="utf-8",
    )
    print(f"standalone: {len(quizzes)} 个；embedded: {len(items)} 页 / {total} 块")
    backlinks = sum(1 for q in quizzes if q.get("concept_to_quiz_backlink"))
    print(f"concept→quiz 回链: {backlinks}/{len(quizzes)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
