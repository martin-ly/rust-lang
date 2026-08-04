#!/usr/bin/env python3
"""Fine-tune an embedding model on the Rust concept knowledge graph.

Supports two modes:

1. **Full SentenceTransformer fine-tuning** (default) with contrastive learning
   (``MultipleNegativesRankingLoss``).  This updates the whole transformer and
   works with only ``sentence-transformers`` installed.

2. **LoRA fine-tuning** (``--lora``) via PEFT.  This keeps the base model frozen
   and trains low-rank adapters, drastically reducing memory use and producing
   a small adapter checkpoint that can be merged later.

The training data is built automatically from ``kg_data_v3.json``:

* Each entity's English label + scope note is an ``anchor``.
* Related entities connected by semantic predicates
  (``dependsOn``, ``refines``, ``entails``, ``equivalentTo``, ``partOf``,
  ``hasPart``) are used as ``positive`` pairs.
* Simple rule-based paraphrases (word deletion, synonym insertion, bracket
  stripping) augment the anchor corpus.

Reproducible run (requires ``tools/kg_rag/.venv``):

    cd tools/kg_rag
    .venv/Scripts/pip install -r requirements.txt
    .venv/Scripts/python fine_tune_embedding.py \
        --epochs 3 --batch-size 16 --output-dir .cache/fine_tuned_model

LoRA example:

    .venv/Scripts/python fine_tune_embedding.py --lora \
        --lora-r 8 --lora-alpha 32 --epochs 5 \
        --output-dir .cache/fine_tuned_lora

The script writes:

* ``{output_dir}/`` — the fine-tuned model (or LoRA adapter + base model)
* ``{output_dir}/training_metadata.json`` — hyper-parameters, dataset stats,
  and reproducibility seed
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
from pathlib import Path
from typing import Any

# Re-execute inside the project venv when dependencies are missing.
ROOT = Path(__file__).resolve().parent
REPO_ROOT = ROOT.parents[1]
KG_PATH = REPO_ROOT / "concept" / "00_meta" / "kg_data_v3.json"
VENV_PYTHON = ROOT / ".venv" / "Scripts" / "python.exe"


def _ensure_deps() -> None:
    try:
        import sentence_transformers  # noqa: F401
        import torch  # noqa: F401
    except ImportError:
        if VENV_PYTHON.exists() and sys.executable != str(VENV_PYTHON):
            os.execv(str(VENV_PYTHON), [str(VENV_PYTHON)] + sys.argv)
        print(
            "ERROR: missing dependencies. Run:\n"
            "  cd tools/kg_rag && .venv/Scripts/pip install -r requirements.txt",
            file=sys.stderr,
        )
        sys.exit(1)


_ensure_deps()

import torch  # noqa: E402
from sentence_transformers import (  # noqa: E402
    InputExample,
    SentenceTransformer,
    losses,
)
from torch.utils.data import DataLoader  # noqa: E402

from kg_core import iter_entities, load_kg  # noqa: E402

SEMANTIC_PREDICATES = {
    "ex:dependsOn",
    "ex:refines",
    "ex:entails",
    "ex:equivalentTo",
    "ex:partOf",
    "ex:hasPart",
}


def get_lang(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def entity_text(entity: dict[str, Any]) -> str:
    parts: list[str] = []
    label = get_lang(entity.get("skos:prefLabel", []), "en")
    if label:
        parts.append(label)
    for key in ("skos:scopeNote", "skos:definition"):
        values = entity.get(key, [])
        en = get_lang(values, "en")
        if en:
            parts.append(en)
            break
    return " ".join(parts)


def paraphrase(text: str, rng: random.Random) -> str:
    """Return a simple rule-based paraphrase of a concept description."""
    variants = [text]
    # Strip parenthetical phrases.
    stripped = re.sub(r"\s*\([^)]*\)", "", text).strip()
    if stripped and stripped != text:
        variants.append(stripped)
    # Drop a random adjective-like token (heuristic: token before a noun).
    tokens = text.split()
    if len(tokens) > 4:
        drop_idx = rng.randint(1, len(tokens) - 2)
        variants.append(" ".join(tokens[:drop_idx] + tokens[drop_idx + 1 :]))
    # Prefix with "rust".
    variants.append(f"rust {text}")
    # Lowercase variant.
    variants.append(text.lower())
    return rng.choice(variants)


def build_training_pairs(kg: dict[str, Any], rng: random.Random) -> list[tuple[str, str]]:
    """Build (anchor, positive) pairs from entity texts and KG relations."""
    entities = iter_entities(kg)
    by_id = {e["@id"]: e for e in entities}
    pairs: list[tuple[str, str]] = []

    for entity in by_id.values():
        anchor = entity_text(entity)
        if not anchor:
            continue
        # Relation-based positives.
        for rel in kg.get("relations", []):
            if rel.get("ex:subject") != entity.get("@id"):
                continue
            pred = rel.get("ex:predicate", "")
            if pred not in SEMANTIC_PREDICATES:
                continue
            obj_id = rel.get("ex:object")
            obj = by_id.get(obj_id)
            if not obj:
                continue
            positive = entity_text(obj)
            if positive:
                pairs.append((anchor, positive))

        # Self-augmented positives: anchor paraphrased against itself.
        if len(anchor) > 20:
            pairs.append((anchor, paraphrase(anchor, rng)))

    rng.shuffle(pairs)
    return pairs


def apply_lora(model: SentenceTransformer, r: int, alpha: int, dropout: float) -> SentenceTransformer:
    """Wrap the transformer module with PEFT LoRA adapters if available."""
    try:
        from peft import LoraConfig, get_peft_model  # type: ignore
    except ImportError as exc:
        raise RuntimeError(
            "LoRA requested but 'peft' is not installed. "
            "Install it with: pip install peft"
        ) from exc

    # The underlying transformer is accessible as model[0].auto_model.
    base = model[0].auto_model
    config = LoraConfig(
        r=r,
        lora_alpha=alpha,
        target_modules=["query", "key", "value"],
        lora_dropout=dropout,
        bias="none",
        task_type="FEATURE_EXTRACTION",
    )
    lora_model = get_peft_model(base, config)
    model[0].auto_model = lora_model
    return model


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Fine-tune an embedding model on the Rust KG.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--kg", type=Path, default=KG_PATH, help="Path to kg_data_v3.json")
    parser.add_argument(
        "--base-model",
        default="all-MiniLM-L6-v2",
        help="Base sentence-transformer model (default: all-MiniLM-L6-v2)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=ROOT / ".cache" / "fine_tuned_model",
        help="Directory to save the fine-tuned model",
    )
    parser.add_argument("--epochs", type=int, default=3, help="Training epochs")
    parser.add_argument("--batch-size", type=int, default=16, help="Batch size")
    parser.add_argument("--lr", type=float, default=2e-5, help="Learning rate")
    parser.add_argument("--seed", type=int, default=20260804, help="Random seed")
    parser.add_argument(
        "--max-pairs",
        type=int,
        default=100000,
        help="Maximum number of training pairs to use",
    )
    parser.add_argument(
        "--lora",
        action="store_true",
        help="Use PEFT LoRA instead of full fine-tuning",
    )
    parser.add_argument("--lora-r", type=int, default=8, help="LoRA rank")
    parser.add_argument("--lora-alpha", type=int, default=32, help="LoRA alpha")
    parser.add_argument("--lora-dropout", type=float, default=0.05, help="LoRA dropout")
    parser.add_argument(
        "--device",
        default=None,
        help="PyTorch device (default: auto)",
    )
    parser.add_argument(
        "--warmup-steps",
        type=int,
        default=100,
        help="Warmup steps for the learning-rate scheduler",
    )
    args = parser.parse_args(argv)

    rng = random.Random(args.seed)
    torch.manual_seed(args.seed)

    kg = load_kg(args.kg)
    pairs = build_training_pairs(kg, rng)
    if args.max_pairs and len(pairs) > args.max_pairs:
        pairs = pairs[: args.max_pairs]

    if not pairs:
        print("ERROR: no training pairs generated from KG.", file=sys.stderr)
        return 1

    print(f"[fine_tune_embedding] generated {len(pairs)} training pairs", file=sys.stderr)

    device = args.device or ("cuda" if torch.cuda.is_available() else "cpu")
    print(f"[fine_tune_embedding] loading base model {args.base_model} on {device}", file=sys.stderr)
    model = SentenceTransformer(args.base_model, device=device)

    if args.lora:
        model = apply_lora(
            model,
            r=args.lora_r,
            alpha=args.lora_alpha,
            dropout=args.lora_dropout,
        )
        print("[fine_tune_embedding] LoRA adapters attached", file=sys.stderr)

    train_examples = [InputExample(texts=[a, p]) for a, p in pairs]
    train_dataloader = DataLoader(
        train_examples,
        shuffle=True,
        batch_size=args.batch_size,
    )
    train_loss = losses.MultipleNegativesRankingLoss(model)

    args.output_dir.mkdir(parents=True, exist_ok=True)

    # SentenceTransformer fit call.
    model.fit(
        train_objectives=[(train_dataloader, train_loss)],
        epochs=args.epochs,
        warmup_steps=args.warmup_steps,
        optimizer_params={"lr": args.lr},
        show_progress_bar=True,
        output_path=str(args.output_dir),
    )

    metadata = {
        "base_model": args.base_model,
        "output_dir": str(args.output_dir),
        "training_pairs": len(pairs),
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "seed": args.seed,
        "device": device,
        "lora": args.lora,
        "lora_r": args.lora_r if args.lora else None,
        "lora_alpha": args.lora_alpha if args.lora else None,
        "lora_dropout": args.lora_dropout if args.lora else None,
    }
    (args.output_dir / "training_metadata.json").write_text(
        json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    print(f"[fine_tune_embedding] model saved to {args.output_dir}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
