#!/usr/bin/env python3
"""
归档迁移脚本：Archive migration helper.

Moves legacy dirs into archive/ and rewrites Markdown links that pointed to them.
Moves:
  docs/archive/                       -> archive/docs/
  docs/rust-ownership-decidability/   -> archive/rust-ownership-decidability/
"""

import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# source dir (relative to root) -> destination dir (relative to root)
MOVES = {
    "docs/archive": "archive/docs",
    "docs/rust-ownership-decidability": "archive/rust-ownership-decidability",
}

# Moves whose directory depth changes (source deeper than destination).
# Links from inside these dirs to outside targets must be rewritten.
DEPTH_CHANGING_SOURCES = ["docs/rust-ownership-decidability"]

LINK_RE = re.compile(r"\[(?P<text>[^\]]*)\]\((?P<path>[^)\s]+)\)")


def _norm(p: Path) -> Path:
    return p.resolve()


def original_path(cur: Path) -> Path:
    """Given a file's current path (before or after move), return its pre-move path."""
    cur_abs = _norm(cur)
    root_abs = _norm(REPO_ROOT)
    for src_rel, dst_rel in MOVES.items():
        dst_abs = root_abs / dst_rel
        try:
            rel = cur_abs.relative_to(dst_abs)
            return root_abs / src_rel / rel
        except ValueError:
            pass
    return cur_abs


def new_path(cur: Path) -> Path:
    """Given a file's current path (before or after move), return its post-move path."""
    cur_abs = _norm(cur)
    root_abs = _norm(REPO_ROOT)
    for src_rel, dst_rel in MOVES.items():
        src_abs = root_abs / src_rel
        try:
            rel = cur_abs.relative_to(src_abs)
            return root_abs / dst_rel / rel
        except ValueError:
            pass
    return cur_abs


def is_under(p: Path, dir_rel: str) -> bool:
    try:
        _norm(p).relative_to(_norm(REPO_ROOT) / dir_rel)
        return True
    except ValueError:
        return False


def resolve_link(source_file: Path, link_path: str) -> Path | None:
    """Resolve a markdown link path relative to the source file."""
    if link_path.startswith("http://") or link_path.startswith("https://"):
        return None
    if link_path.startswith("/"):
        target = (_norm(REPO_ROOT) / link_path.lstrip("/"))
    else:
        target = (source_file.parent / link_path).resolve()
    try:
        target.relative_to(_norm(REPO_ROOT))
    except ValueError:
        return None
    return target


def rewrite_links_in_file(cur: Path) -> bool:
    """Rewrite links in the file at its current (pre or post move) path."""
    orig_source = original_path(cur)
    new_source = new_path(cur)

    original = cur.read_text(encoding="utf-8")
    changed = False

    def repl(m: re.Match) -> str:
        nonlocal changed
        text = m.group("text")
        raw_path = m.group("path")
        if "#" in raw_path:
            path_part, frag = raw_path.split("#", 1)
            anchor = "#" + frag
        else:
            path_part = raw_path
            anchor = ""

        old_target = resolve_link(orig_source, path_part)
        if old_target is None:
            return m.group(0)

        needs_rewrite = False
        # Target is being moved.
        for src_rel in MOVES:
            if is_under(old_target, src_rel):
                needs_rewrite = True
                break

        # Source depth changed and target is outside the source tree.
        if not needs_rewrite:
            for src_rel in DEPTH_CHANGING_SOURCES:
                if (
                    is_under(orig_source, src_rel)
                    and not is_under(old_target, src_rel)
                    and old_target.exists()
                ):
                    needs_rewrite = True
                    break

        if not needs_rewrite:
            return m.group(0)

        new_target = new_path(old_target)
        new_rel = os.path.relpath(new_target, new_source.parent)
        new_rel = new_rel.replace(os.sep, "/")

        new_link = f"[{text}]({new_rel}{anchor})"
        changed = True
        return new_link

    new_text = LINK_RE.sub(repl, original)
    if changed:
        cur.write_text(new_text, encoding="utf-8")
    return changed


def main() -> int:
    dry_run = len(sys.argv) > 1 and sys.argv[1] == "--dry-run"

    if dry_run:
        print("DRY RUN: no files will be moved or written")

    md_files = [p for p in REPO_ROOT.rglob("*.md") if not _skip(p)]
    changed_files = []
    for md_file in md_files:
        if dry_run:
            # In dry-run, do not write; just detect if it would change.
            if _would_change(md_file):
                changed_files.append(md_file.relative_to(REPO_ROOT))
        else:
            if rewrite_links_in_file(md_file):
                changed_files.append(md_file.relative_to(REPO_ROOT))

    print(
        f"Link rewriting {'would affect' if dry_run else 'updated'} {len(changed_files)} files"
    )
    for f in changed_files[:30]:
        print(f"  - {f}")
    if len(changed_files) > 30:
        print(f"  ... and {len(changed_files) - 30} more")

    if dry_run:
        return 0

    # Move directories using git mv. Link rewrite is idempotent and move-agnostic,
    # so running it before the move is fine; after the move it would produce the same result.
    for src_rel, dst_rel in MOVES.items():
        src = REPO_ROOT / src_rel
        dst = REPO_ROOT / dst_rel
        if not src.exists():
            print(f"Source does not exist, skipping move: {src_rel}")
            continue
        if dst.exists():
            print(f"Destination already exists: {dst_rel}")
            sys.exit(1)
        print(f"Moving {src_rel} -> {dst_rel}")
        os.system(f'git mv "{src}" "{dst}"')

    return 0


def _would_change(cur: Path) -> bool:
    """Non-destructive version of rewrite_links_in_file."""
    orig_source = original_path(cur)
    new_source = new_path(cur)
    original = cur.read_text(encoding="utf-8")

    def repl(m: re.Match) -> str:
        text = m.group("text")
        raw_path = m.group("path")
        if "#" in raw_path:
            path_part, frag = raw_path.split("#", 1)
            anchor = "#" + frag
        else:
            path_part = raw_path
            anchor = ""

        old_target = resolve_link(orig_source, path_part)
        if old_target is None:
            return m.group(0)

        needs_rewrite = False
        for src_rel in MOVES:
            if is_under(old_target, src_rel):
                needs_rewrite = True
                break
        if not needs_rewrite:
            for src_rel in DEPTH_CHANGING_SOURCES:
                if (
                    is_under(orig_source, src_rel)
                    and not is_under(old_target, src_rel)
                    and old_target.exists()
                ):
                    needs_rewrite = True
                    break
        if not needs_rewrite:
            return m.group(0)

        new_target = new_path(old_target)
        new_rel = os.path.relpath(new_target, new_source.parent).replace(os.sep, "/")
        return f"[{text}]({new_rel}{anchor})"

    new_text = LINK_RE.sub(repl, original)
    return new_text != original


def _skip(p: Path) -> bool:
    try:
        p.relative_to(REPO_ROOT / ".git")
        return True
    except ValueError:
        pass
    try:
        p.relative_to(REPO_ROOT / "target")
        return True
    except ValueError:
        pass
    return False


if __name__ == "__main__":
    sys.exit(main())
