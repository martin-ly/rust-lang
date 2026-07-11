# Safety Tags（安全标签）

**EN**: Safety Tags for Unsafe Code
**Summary**: RFC #3842 proposal for structured attributes marking the safety contracts of `unsafe` functions, checkable by tooling and formal reasoning.

> **权威来源**: 本主题已合并至 [`../../07_future/03_preview_features/08_safety_tags_preview.md`](../../07_future/03_preview_features/08_safety_tags_preview.md)，本文件保留为重定向。
>
> 根据 AGENTS.md §2 Canonical 规则，同一概念只能有一个权威页。
> 经 2026-07-12 审计，本文件与预览权威页内容高度重复（v2 相似度 0.855），且未包含独立的形式化（分离逻辑）推导内容——其形式化语义（契约的谓词逻辑表示、与 Kani/Prusti/Verus 的映射）已由 08 号权威页「二、形式化语义」一节覆盖。形式化视角的延伸阅读见：
>
> - [AutoVerus/Verus](../04_model_checking/24_autoverus.md) — `requires`/`ensures` 契约验证
> - [Miri](../04_model_checking/31_miri.md) · [形式化验证工具生态](../../06_ecosystem/08_formal_verification/74_formal_verification_tools.md)
> - [BorrowSanitizer 深度](34_borrow_sanitizer_in_formal.md)
