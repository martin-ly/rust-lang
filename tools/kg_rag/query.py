#!/usr/bin/env python3
"""CLI entry point for KG-RAG hybrid search.

Example:
    python tools/kg_rag/query.py --query "how does ownership relate to borrowing" --top-k 5
"""
from kg_rag import main

if __name__ == "__main__":
    raise SystemExit(main())
