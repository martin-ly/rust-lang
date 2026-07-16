---
name: Pull Request
about: 提交 Rust 知识库变更
title: '[PR] '
labels: ''
assignees: ''
---

## 变更概述

<!-- 用 1–3 句话说明本次 PR 做了什么 -->

## 影响范围

- [ ] 本次变更涉及 `concept/` 中的概念/权威页
- [ ] 本次变更涉及 `knowledge/`、`docs/`、`content/` 或 `crates/*/docs/` 中的摘要/指南/stub
- [ ] 本次变更仅涉及工具、脚本、CI、报告或元数据

<!-- 如涉及 concept/ 权威页，请填写： -->
**受影响的 concept/ 权威页**（如有）：`concept/xx_xx/xx_xx.md`

## 语义深度检查单

> PR 不仅要通过形式质量门，还必须提升或保持知识库的语义深度。请勾选并简要说明：

- [ ] **新增或精化了一个定义**：请说明定义内容
- [ ] **新增或调整了一条决策规则**：请说明适用场景与边界
- [ ] **新增了一个反例或错误模式**：请说明对应的 rustc 错误码（如有）
- [ ] **新增或澄清了一个跨域语义边界**（如 async+unsafe、FFI+async、Send/Sync boundaries、let chains 等）：请说明边界语义
- [ ] **以上均无**：请说明本次变更为何不需要增加语义深度

## Stub / Redirect 声明

- [ ] 本次变更是 stub/redirect 文件

<!-- 如是 stub/redirect，请填写指向的权威页： -->
**指向的权威页**（如有）：`concept/xx_xx/xx_xx.md`

## 新增 concept/ 页元数据

<!-- 如在 concept/ 中新增权威页，请确认已包含： -->

- [ ] **EN** 英文标题
- [ ] **Summary** 一句话英文摘要
- [ ] **Bloom 层级**（L0–L7）
- [ ] **Rust 版本**（如 `1.97.0+ (Edition 2024)`）
- [ ] **权威来源**声明：包含“本文件为 concept/ 权威页”的声明

## 本地质量门确认

> 在提交 PR 前，请在本地运行以下命令并确认通过：

- [ ] 我运行了 `bash scripts/run_quality_gates.sh`，全部 23 个阻断门与 5 个语义观察门通过（观察门以最新报告为准）
- [ ] 我运行了 `python scripts/detect_content_overlap.py` 检查新增/修改内容是否存在重复
- [ ] 如涉及新增代码示例，我运行了 `cargo test --workspace` 或对应 crate 的测试
- [ ] 如修改了 KG 关系，我运行了 `python scripts/check_kg_relation_precision.py --strict`

## 附加上下文字

<!-- 任何有助于 review 的信息：相关 issue、决策依据、替代方案等 -->
