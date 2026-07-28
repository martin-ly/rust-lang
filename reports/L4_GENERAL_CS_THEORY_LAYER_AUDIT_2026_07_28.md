# L4 通用 CS 理论内容层归属审计

**EN**: L4 General Computer Science Theory Layer Assignment Audit
**Summary**: 审计 `concept/04_formal/` 中过度泛化的通用计算机科学理论内容，标注其项目教学桥梁定位，并提出层归属建议。

> **生成时间**: 2026-07-28
> **审计范围**: `concept/04_formal/`
> **工具**: 关键词搜索 + 人工复核

---

## 一、审计方法

1. 搜索关键词：图灵机、主定理、停机问题、Church-Turing 论题、通用范畴论、Haskell 对比等。
2. 判断标准：内容是否以通用 CS 理论为主，Rust 仅作为示例或对比，而非 Rust 官方语义。
3. 处理方式：在文件 frontmatter 中增加 `project-specific` 标记，明确其教学桥梁定位。

---

## 二、发现列表

| 文件 | 通用 CS 理论内容 | 处理状态 | 备注 |
|---|---|---|---|
| `concept/04_formal/00_type_theory/13_formal_algorithm_theory.md` | 图灵机、Church-Turing 论题、主定理 | ✅ 已标记 `project-specific` | 作为算法形式化教学入口保留在 L4 |
| `concept/04_formal/04_model_checking/05_programming_language_foundations.md` | λ 演算、停机问题、System F、Currying | ✅ 已标记 `project-specific` | 作为 PL 理论教学入口保留在 L5-L6 |
| `concept/04_formal/00_type_theory/04_category_theory.md` | Functor/Applicative/Monad 的 Haskell 对比 | ✅ 已标记 `project-specific`（已有纯数学警告） | 作为跨语言理论桥梁保留在 L4-L5 |
| `concept/04_formal/00_type_theory/05_lambda_calculus.md` | Church-Turing 论题 | ⚠️ 未改动 | 内容以 Rust 闭包/计算模型映射为主，通用 λ 演算占比适中 |
| `concept/04_formal/00_type_theory/08_type_inference_complexity.md` | 交替图灵机比喻 | ⚠️ 未改动 | 仅一句话教学比喻，不影响整体 Rust 类型推断主题 |

---

## 三、处理原则

1. **不删除、不重命名**：这些文件对学习路径有价值，尤其是从 PL/CS 背景进入 Rust 的读者。
2. **显式标记 `project-specific`**：让读者清楚这些页面是项目教学创新，非 Rust 官方规范。
3. **保留 canonical 链接**：每个标记页都链接到对应的 Rust 权威页，避免概念漂移。
4. **后续监控**：新增 L4 形式化页时，若出现通用 CS 理论占比 >50% 的情况，应主动评估是否标记。

---

## 四、后续建议

- 若未来发现更多类似页面，可直接套用本审计的标记模板。
- 考虑在 `scripts/check_authority_coverage.py` 中识别 `project-specific` 标记并排除统计，避免覆盖率虚高。
