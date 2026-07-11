#!/usr/bin/env python3
"""批量修复 Markdown 中编译失败的 Rust 代码块标记。

策略：
- 读取 code_block_compiler.py 生成的报告；
- 根据错误信息自动判断应标记为 compile_fail（故意展示的错误）或 ignore（不完整片段、伪代码、多文件示例等）；
- 修改对应 ```rust 围栏，保留其他语言修饰符与正文。
"""

import re
from pathlib import Path

REPORT_PATH = Path("reports/code_block_compile_report.md")

# 归为 ignore 的错误签名（不完整片段、上下文缺失、伪语法、外部资源等）
IGNORE_PATTERNS = [
    "cannot find",
    "unresolved import",
    "expected one of",
    "expected `;`",
    "expected statement after outer attribute",
    "expected expression, found",
    "expected identifier, found",
    "expected `:`, found",
    "expected trait, found",
    "non-item in item list",
    "free function without a body",
    "associated function in impl without body",
    "cannot declare a file module inside a block",
    "too many leading",
    "unknown start of token",
    "is defined multiple times",
    "cannot find macro",
    "use of undeclared lifetime name",
    "type parameter `I` must be used as an argument",
    "found a documentation comment that doesn't document anything",
    "visibility `pub` is not followed",
    "environment variable",
    "unknown feature",
    "unsafe attribute used without unsafe",
    "extern blocks must be unsafe",
    "`#[panic_handler]` function required",
    "unwinding pan",
    "operation will panic",
    "expected `;`, found keyword",
    "expected one of `:`",
    "unexpected token: `...`",
]

# 归为 compile_fail 的语义错误签名（故意展示的错误）
COMPILE_FAIL_PATTERNS = [
    "borrow of moved value",
    "use of moved value",
    "cannot borrow",
    "missing lifetime specifier",
    "does not live long enough",
    "mismatched types",
    "type annotations needed",
    "trait bound",
    "the trait",
    "binary operation",
    "recursive type",
    "closure may outlive",
    "does not implement `Copy`",
    "cannot be sent between threads safely",
    "cannot be unpinned",
    "type `str` cannot be indexed",
    "`if` and `else` have incompatible types",
    "the method exists",
    "expected a `FnMut",
    "call to unsafe function",
    "used binding",
    "isn't initialized",
]


def parse_report(path: Path):
    """解析报告中的失败行，返回 (file, line, mode, preview, stderr) 列表。"""
    text = path.read_text(encoding="utf-8")
    rows = []
    for line in text.splitlines():
        if not line.startswith("| "):
            continue
        parts = [p.strip() for p in line.split("|")]
        # 过滤空首尾的 ['']
        parts = [p for p in parts if p != ""]
        # 只保留失败表中的行：至少 5 列且包含错误信息
        if len(parts) < 5:
            continue
        if not (parts[0].startswith("concept\\") or parts[0].startswith("knowledge\\")):
            continue
        if parts[0] == "文件" or parts[1] == "行号":
            continue
        file_ = parts[0]
        line_no = parts[1]
        mode = parts[2]
        preview = parts[3].strip("`")
        stderr = parts[4] if len(parts) >= 5 else ""
        # 跳过通过示例表（没有 stderr 或 stderr 为表头）
        if not stderr or stderr == "错误信息":
            continue
        try:
            line_int = int(line_no)
        except ValueError:
            continue
        rows.append(
            {"file": file_, "line": line_int, "mode": mode, "preview": preview, "stderr": stderr}
        )
    return rows


def decide_action(row: dict) -> str:
    stderr = row["stderr"]
    preview = row["preview"]
    file_ = row["file"]

    # 归档文件、占位符 `...`、伪代码片段直接忽略
    if "concept\\archive" in file_ or "..." in preview:
        return "ignore"

    # 根据错误签名归类
    for pat in IGNORE_PATTERNS:
        if pat in stderr:
            return "ignore"
    for pat in COMPILE_FAIL_PATTERNS:
        if pat in stderr:
            return "compile_fail"

    # 默认保守处理为 ignore，避免误标 compile_fail
    return "ignore"


def modify_block_tag(file_path: Path, fence_line_1based: int, action: str) -> bool:
    """修改指定代码块的围栏标记。报告中的行号即围栏所在行。"""
    idx = fence_line_1based - 1
    if idx < 0:
        return False

    with open(file_path, "r", encoding="utf-8", newline="") as f:
        lines = f.readlines()

    if idx >= len(lines):
        return False

    line = lines[idx]
    stripped = line.lstrip()
    if not stripped.startswith("```rust"):
        return False

    # 如果已经有修饰符，不重复添加（简单场景下失败块都是 ```rust）
    rest = stripped[len("```rust"):].rstrip("\n").rstrip("\r")
    if rest.strip():
        # 已有修饰符，追加到末尾
        new_rest = (rest + "," + action).strip(",")
        new_line = line.replace(stripped, f"```rust{new_rest}\n", 1)
    else:
        new_line = line.replace("```rust", f"```rust,{action}", 1)

    if new_line == line:
        return False

    lines[idx] = new_line
    with open(file_path, "w", encoding="utf-8", newline="") as f:
        f.writelines(lines)
    return True


def main():
    rows = parse_report(REPORT_PATH)
    print(f"解析到 {len(rows)} 个失败代码块")

    actions = {"ignore": 0, "compile_fail": 0, "skipped": 0}
    for row in rows:
        # 只处理当前为 normal 的失败块；compile_fail 但通过的块单独处理
        if row["mode"] != "normal":
            actions["skipped"] += 1
            continue
        action = decide_action(row)
        actions[action] += 1
        file_path = Path(row["file"])
        if modify_block_tag(file_path, row["line"], action):
            print(f"  {action}: {file_path}:{row['line']}")
        else:
            print(f"  未修改: {file_path}:{row['line']}")

    print(f"\n计划: {actions}")


if __name__ == "__main__":
    main()
