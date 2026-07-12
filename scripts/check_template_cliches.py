#!/usr/bin/env python3
"""模板套话 lint：扫描 concept/ 中批量注入风格的通用模板句黑名单。

背景：2026-07 审计发现 59-95 个 concept/ 文件被批量脚本
（已归档的一次性脚本 scripts/archive/one_off_2026/add_backward_reasoning.py / add_backward_l2l3.py 等）注入了仅主题名不同的
通用模板句（反命题决策树、认知路径五步骤、定理套话、过渡套话、反向推理），
已于 2026-07-12 清理（见 reports/TEMPLATE_CLICHE_CLEANUP_2026_07_12.md）。
2026-07-12 下午补充第二波 7 个家族（过渡A-D、反命题A-B、定理D，跨 75-84 文件逐字重复，
清理见 reports/TEMPLATE_BACKFILL_QUALITY_2026_07_12.md）。
本脚本内置该黑名单，防止回归。

用法：
    python scripts/check_template_cliches.py            # 默认 warning，exit 0
    python scripts/check_template_cliches.py --strict   # 发现即 exit 1
    python scripts/check_template_cliches.py --path concept/01_foundation
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# 黑名单：(家族名, 行正则) —— 与清理脚本 tmp/clean_template_cliches.py 同源，
# 经全量变体验证（仅主题槽不同，跨 30-83 个文件逐字重复）。
CLICHE_PATTERNS: list[tuple[str, re.Pattern]] = [
    ("反命题1", re.compile(r'^> \*\*反命题 1\*\*: ".*在所有场景下都适用" ⟹ 不成立。.*$')),
    ("反命题2", re.compile(r'^> \*\*反命题 2\*\*: "忽略 .*的细节也能写出正确代码" ⟹ 不成立。.*$')),
    ("反命题3", re.compile(r'^> \*\*反命题 3\*\*: "其他语言对 .*的处理方式可以直接迁移到 Rust" ⟹ 不成立。.*$')),
    ("定理1", re.compile(r'^> \*\*定理 1\*\* \[Tier 2\]: .*的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。\s*$')),
    ("定理2", re.compile(r'^> \*\*定理 2\*\* \[Tier 2\]: 正确理解 .*的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。\s*$')),
    ("定理3", re.compile(r'^> \*\*定理 3\*\* \[Tier 3\]: 将 .*与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。\s*$')),
    ("过渡1", re.compile(r'^> \*\*过渡\*\*: 从 .*的直观描述转向其形式化定义.*$')),
    ("过渡2", re.compile(r'^> \*\*过渡\*\*: 在建立 .*的核心命题之后，下一步是审视这些命题在边界条件下的稳定性.*$')),
    ("过渡3", re.compile(r'^> \*\*过渡\*\*: 最后，将 .*与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。\s*$')),
    ("反向推理1", re.compile(r'^> \*\*反向推理 1\*\*: 如果程序在 .*相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。\s*$')),
    ("反向推理2", re.compile(r'^> \*\*反向推理 2\*\*: 如果某段代码在运行时（Runtime）表现出非预期行为且与 .*有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。\s*$')),
    ("认知路径引言", re.compile(r'^> \*\*认知路径\*\*: 本节从 ".*"\s*(的核心问题|这一核心问题)出发，依次建立.*之间的联系。\s*$')),
    ("步骤1", re.compile(r'^1\. \*\*问题识别\*\*: 为什么 .*在 Rust 中值得关注？它与日常编程中的哪些痛点相关？\s*$')),
    ("步骤2", re.compile(r'^2\. \*\*概念建立\*\*: 掌握 .*的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。\s*$')),
    ("步骤3", re.compile(r'^3\. \*\*机制推理\*\*: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。\s*$')),
    ("步骤4", re.compile(r'^4\. \*\*边界辨析\*\*: 借助反命题/反例理解常见错误与.*的适用边界。\s*$')),
    ("步骤5", re.compile(r'^5\. \*\*迁移应用\*\*: 将 .*与前置/后置概念链接，形成跨层知识网络。\s*$')),
    # ── 第二波家族（2026-07-12 下午取证：tmp/cross_dup_scan.txt；清理见
    # reports/TEMPLATE_BACKFILL_QUALITY_2026_07_12.md 与 tmp/clean_template_cliches_v2.py）──
    ("过渡A", re.compile(r'^> \*\*过渡\*\*: 掌握 .+ 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。\s*$')),
    ("过渡B", re.compile(r'^> \*\*过渡\*\*: 在工程实践中应用 .+ 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。\s*$')),
    ("过渡C", re.compile(r'^> \*\*过渡\*\*: .+ 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。\s*$')),
    ("过渡D", re.compile(r'^> \*\*过渡\*\*: .+ 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。\s*$')),
    ("反命题A", re.compile(r'^> \*\*反命题\*\*: ".+ 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。\s*$')),
    ("反命题B", re.compile(r'^> \*\*反命题\*\*: ".+ 在所有场景下都是最佳选择" —— 错误。需要根据具体上下文权衡性能、可读性与安全性，某些场景下显式替代方案可能更优。\s*$')),
    ("定理D", re.compile(r'^- \*\*定理\*\*: .+ 定义 ⟹ 类型安全保证\s*$')),
    # 第三波（75 文件，L1/L4 文件的另一组过渡变体）
    ("过渡E", re.compile(r'^> \*\*过渡\*\*: 掌握 .+ 的基础语法后，下一步需要理解其在类型系统.+位置与与其他概念的交互关系。\s*$')),
    ("过渡F", re.compile(r'^> \*\*过渡\*\*: 在实践中应用 .+ 时，务必关注边界条件与异常处理，这是从"能编译"到"能生产"的关键跃迁。\s*$')),
    ("过渡G", re.compile(r'^> \*\*过渡\*\*: .+ 的设计理念体现了 Rust 零成本抽象（Zero-Cost Abstraction）与安全保证的核心权衡，理解这一权衡有助于迁移到更高级的并发与形式化验证领域。\s*$')),
]

# 豁免：元层模板文件（其中的模板句是结构说明，非注入物）与只读归档
EXEMPT_STEM_CONTAINS = ("template",)
EXEMPT_PARTS = ("archive",)


def scan(base: Path) -> list[tuple[str, int, str, str]]:
    hits: list[tuple[str, int, str, str]] = []
    for path in sorted(base.rglob("*.md")):
        rel_parts = path.relative_to(ROOT).parts if path.is_relative_to(ROOT) else path.parts
        if any(p in rel_parts for p in EXEMPT_PARTS):
            continue
        if any(k in path.stem for k in EXEMPT_STEM_CONTAINS):
            continue
        for lineno, line in enumerate(
            path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1
        ):
            for name, pat in CLICHE_PATTERNS:
                if pat.match(line.rstrip()):
                    hits.append((str(path), lineno, name, line.strip()[:100]))
                    break
    return hits


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict", action="store_true", help="发现模板句时 exit 1")
    ap.add_argument("--path", default="concept", help="扫描根目录(默认 concept/)")
    args = ap.parse_args()

    base = (ROOT / args.path).resolve()
    if not base.is_dir():
        print(f"ERROR: 目录不存在: {base}", file=sys.stderr)
        return 2

    hits = scan(base)
    if not hits:
        print(f"[check_template_cliches] OK: {base} 未发现模板套话")
        return 0

    print(f"[check_template_cliches] 发现 {len(hits)} 处模板套话（黑名单 {len(CLICHE_PATTERNS)} 类）:")
    for path, lineno, name, snippet in hits:
        print(f"  {path}:{lineno} [{name}] {snippet}")
    print("说明：上述句子为批量注入风格的通用模板句（仅主题名不同），"
          "请改写为主题相关内容或删除；豁免:文件名含 template 的元层模板与 archive/。")
    return 1 if args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
