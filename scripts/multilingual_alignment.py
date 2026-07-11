#!/usr/bin/env python3
"""
多语言 KG 对齐漂移检测（P2-2 / i18n-6）

读取 concept/00_meta/kg_data_v3.json 中的中英 skos:prefLabel 对，
使用 sentence-transformers 计算跨语言语义相似度，对低于阈值的术语对生成审校清单。

优先使用 LaBSE/XLM-R 类模型；若本地未缓存，则回退到已缓存的 all-MiniLM-L6-v2
并提示用户。可通过环境变量覆盖模型：

    ALIGNMENT_MODEL=sentence-transformers/LaBSE python scripts/multilingual_alignment.py

用法：
    cd e:\_src\rust-lang
    tools/kg_rag/.venv/Scripts/python scripts/multilingual_alignment.py
"""
from __future__ import annotations

import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

# Re-use the kg_rag project venv when dependencies are missing.
ROOT = Path(__file__).resolve().parent.parent
VENV_PYTHON = ROOT / "tools" / "kg_rag" / ".venv" / "Scripts" / "python.exe"


def _ensure_venv() -> None:
    try:
        import sentence_transformers  # noqa: F401
    except ImportError:
        if VENV_PYTHON.exists() and sys.executable != str(VENV_PYTHON):
            os.execv(str(VENV_PYTHON), [str(VENV_PYTHON)] + sys.argv)
        print(
            "ERROR: missing dependencies. Install with:\n"
            "  cd tools/kg_rag && .venv/Scripts/pip install -r requirements.txt",
            file=sys.stderr,
        )
        sys.exit(1)


_ensure_venv()

from sentence_transformers import SentenceTransformer  # noqa: E402
from huggingface_hub import try_to_load_from_cache  # noqa: E402
import numpy as np  # noqa: E402

KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
REPORT_PATH = ROOT / "reports" / "MULTILINGUAL_ALIGNMENT_DRIFT_2026_07_12.md"

# Preferred cross-lingual models in order. The first one locally cached is used.
PREFERRED_MODELS = [
    "sentence-transformers/LaBSE",
    "sentence-transformers/paraphrase-multilingual-MiniLM-L12-v2",
    "sentence-transformers/paraphrase-multilingual-mpnet-base-v2",
]
FALLBACK_MODEL = "sentence-transformers/all-MiniLM-L6-v2"
THRESHOLD = 0.7


def _is_cached(repo_id: str) -> bool:
    """Check whether a sentence-transformers model has its weights cached."""
    try:
        for weights_file in ("model.safetensors", "pytorch_model.bin"):
            if try_to_load_from_cache(repo_id=repo_id, filename=weights_file) is not None:
                return True
        return False
    except Exception:
        return False


def choose_model(env_model: str | None) -> tuple[str, bool]:
    """Return (model_name, is_cross_lingual)."""
    if env_model:
        return env_model, "multilingual" in env_model.lower() or "LaBSE" in env_model
    for model in PREFERRED_MODELS:
        if _is_cached(model):
            return model, True
    return FALLBACK_MODEL, False


def load_kg(path: Path) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def iter_entities(kg: dict[str, Any]) -> list[dict[str, Any]]:
    """Flatten entities (v3 flat list; legacy v2 grouped dict also accepted)."""
    raw = kg.get("entities", [])
    entities: list[dict[str, Any]] = []
    if isinstance(raw, list):
        for item in raw:
            item.setdefault("_category", item.get("@type", "unknown"))
            entities.append(item)
    else:
        for category, items in raw.items():
            for item in items:
                item["_category"] = category
                entities.append(item)
    return entities


def get_lang_value(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def normalise(vec: np.ndarray) -> np.ndarray:
    norm = np.linalg.norm(vec, axis=1, keepdims=True)
    norm[norm == 0] = 1.0
    return vec / norm


def main() -> int:
    env_model = os.environ.get("ALIGNMENT_MODEL")
    model_name, is_cross_lingual = choose_model(env_model)

    print(f"[multilingual_alignment] Loading KG from {KG_PATH}", file=sys.stderr)
    kg = load_kg(KG_PATH)
    entities = iter_entities(kg)

    pairs: list[tuple[dict[str, Any], str, str]] = []
    missing: list[tuple[dict[str, Any], str]] = []
    for entity in entities:
        en = get_lang_value(entity.get("skos:prefLabel", []), "en")
        zh = get_lang_value(entity.get("skos:prefLabel", []), "zh")
        if en and zh:
            pairs.append((entity, en, zh))
        else:
            missing.append((entity, "en" if not en else "zh"))

    print(f"[multilingual_alignment] Loading model {model_name} ...", file=sys.stderr)
    if not is_cross_lingual:
        print(
            "[multilingual_alignment] WARNING: preferred multilingual models are not cached; "
            f"falling back to {model_name}. Set ALIGNMENT_MODEL to LaBSE/XLM-R for true cross-lingual scores.",
            file=sys.stderr,
        )
    model = SentenceTransformer(model_name)

    en_texts = [p[1] for p in pairs]
    zh_texts = [p[2] for p in pairs]

    print(f"[multilingual_alignment] Encoding {len(pairs)} label pairs ...", file=sys.stderr)
    en_embed = normalise(model.encode(en_texts, convert_to_numpy=True, show_progress_bar=False))
    zh_embed = normalise(model.encode(zh_texts, convert_to_numpy=True, show_progress_bar=False))
    sims = np.sum(en_embed * zh_embed, axis=1)

    drifts: list[dict[str, Any]] = []
    for (entity, en, zh), sim in zip(pairs, sims):
        record = {
            "id": entity["@id"],
            "short_id": short_id(entity["@id"]),
            "category": entity.get("_category", "unknown"),
            "en": en,
            "zh": zh,
            "similarity": round(float(sim), 4),
        }
        if sim < THRESHOLD:
            drifts.append(record)

    avg_sim = float(np.mean(sims)) if len(sims) else 0.0
    min_sim = float(np.min(sims)) if len(sims) else 0.0
    max_sim = float(np.max(sims)) if len(sims) else 0.0

    cross_lingual_note = (
        "✅ 当前使用的是真正的跨语言模型。"
        if is_cross_lingual
        else "⚠️ 当前使用的模型未针对中英跨语言训练，分数仅作参考；"
          "建议设置 `ALIGNMENT_MODEL=sentence-transformers/LaBSE` 重新运行。"
    )

    report = [
        "# 多语言术语对齐漂移检测报告",
        "",
        f"- 生成时间：{datetime.now().isoformat(timespec='seconds')}",
        f"- 知识图谱：{KG_PATH}",
        f"- 对齐模型：`{model_name}`",
        f"- 漂移阈值：{THRESHOLD}",
        f"- {cross_lingual_note}",
        "",
        "## 摘要",
        "",
        f"- 总术语对数：**{len(pairs)}**",
        f"- 缺少英文或中文标签：**{len(missing)}**",
        f"- 低于阈值的漂移对数：**{len(drifts)}**",
        f"- 平均相似度：**{avg_sim:.4f}**",
        f"- 最低相似度：**{min_sim:.4f}**",
        f"- 最高相似度：**{max_sim:.4f}**",
        "",
        "## 漂移术语对（需人工审校）",
        "",
    ]

    if drifts:
        report.append("| 实体 ID | 类别 | 英文标签 | 中文标签 | 相似度 | 建议操作 |")
        report.append("| --- | --- | --- | --- | --- | --- |")
        for d in sorted(drifts, key=lambda x: x["similarity"]):
            suggestion = "检查翻译一致性" if d["similarity"] < 0.5 else "复核术语对应关系"
            report.append(
                f"| {d['short_id']} | {d['category']} | {d['en']} | {d['zh']} | "
                f"{d['similarity']:.4f} | {suggestion} |"
            )
    else:
        report.append("✅ 未发现低于阈值的漂移术语对。")

    if missing:
        report.extend([
            "",
            "## 缺少标签的实体",
            "",
            "| 实体 ID | 类别 | 缺少语言 |",
            "| --- | --- | --- |",
        ])
        for entity, lang in missing:
            report.append(
                f"| {short_id(entity['@id'])} | {entity.get('_category', 'unknown')} | {lang} |"
            )

    report.extend([
        "",
        "## 统计方法",
        "",
        "1. 使用 sentence-transformers 分别编码每对实体的英文和中文 `skos:prefLabel`。",
        "2. 对 embedding 做 L2 归一化，计算余弦相似度。",
        "3. 相似度低于阈值 `0.7` 的术语对标记为漂移，需人工审校。",
        "4. 推荐模型：`sentence-transformers/LaBSE` 或 XLM-R 系列。",
        "",
    ])

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, "w", encoding="utf-8") as f:
        f.write("\n".join(report))

    print(f"[multilingual_alignment] Report written to {REPORT_PATH}", file=sys.stderr)
    print(f"[multilingual_alignment] Drift count: {len(drifts)} / {len(pairs)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
