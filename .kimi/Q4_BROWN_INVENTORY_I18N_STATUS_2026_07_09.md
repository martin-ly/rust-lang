# Q4 2026 Brown Inventory 练习 i18n 就绪状态报告

> **日期**: 2026-07-09
> **范围**: `exercises/src/ownership_borrowing/brown_inventories/`
> **检查项**: 双语注释、元数据格式、TODO 国际化、与 `concept/` 权威页 i18n 规范的对齐度

---

## 1. 文件清单（8 个）

| 文件 | 主题（中文 / 英文） | 当前字数（含注释） | 测试 |
|---|---|---|---|
| `inventory_01.rs` | 移动语义 vs. Copy 语义 / Move Semantics vs. Copy Semantics | ~54 行 | ✅ |
| `inventory_02.rs` | 可变借用规则 / Mutable Borrowing Rules | ~ | ✅ |
| `inventory_03.rs` | 悬垂引用 / Dangling References | ~ | ✅ |
| `inventory_04.rs` | 生命周期标注 / Lifetime Annotations | ~ | ✅ |
| `inventory_05.rs` | RAII 与 Drop 语义 / RAII and Drop Semantics | ~72 行 | ✅ |
| `inventory_06.rs` | 借用检查器错误修复 / Fixing Borrow Checker Errors | ~ | ✅ |
| `inventory_07.rs` | Vec 重新分配与切片失效 / Vec Reallocation and Slice Invalidation | ~ | ✅ |
| `inventory_08.rs` | 循环中的所有权 / Ownership in Loops | ~ | ✅ |
| `README.md` | 练习索引与学习入口 | ~45 行 | — |

> 注：所有 8 个 `.rs` 文件均包含 `#[cfg(test)]` 模块，可直接通过 `cargo test -p exercises --lib ownership_borrowing::brown_inventories` 运行。

---

## 2. 现有双语化情况

### 2.1 已具备的双语元素 ✅

1. **文件头元数据**
   - 每个 `.rs` 文件顶部都有统一的 rustdoc 块：

     ```rust
     //! # Brown University CRP Ownership Inventory — Program 0X
     //!
     //! **来源 / Source**: Brown University CRP Ownership Inventory 样题
     //! **主题 / Topic**: 中文主题 / 英文主题
     //!
     //! ## 学习目标 / Learning Goal
     //!
     //! 中文说明
     //! English description.
     ```

   - 标题、来源、主题、学习目标均为中英对照。

2. **代码注释双语化**
   - 函数级 doc 注释通常采用：

     ```rust
     /// 返回两个数字和两个字符串长度的总和。
     /// Returns the sum of lengths of two numbers (as string) and two strings.
     ```

   - 关键实现注释也多为中英双语或中文带英文术语。

3. **README 双语索引**
   - `README.md` 的表格列标题使用“主题 / Topic”。
   - 包含“国际学习者入口”小节，指向 Brown University 官方英文资源。

### 2.2 尚未对齐项目 i18n 规范的部分 ⚠️

1. **缺少 `**EN**` / `**Summary**` 元数据块**
   - `concept/` 权威页要求在标题后放置：

     ```markdown
     > **EN**: English Title
     > **Summary**: One-sentence abstract.
     ```

   - Brown Inventory 的 rustdoc 块虽然包含英文标题，但**没有独立、结构化的 Summary 行**，也未使用 `**EN**` / `**Summary**` 标记。

2. **TODO 提示未完全双语化**
   - 当前 TODO 多为中文，例如：

     ```rust
     // TODO: 请改用借用，避免拿走 s1 和 s2 的所有权。
     ```

   - 缺少对应的英文 TODO 提示，对非中文学习者不够友好。

3. **缺少 Bloom / 受众 / 层级元数据**
   - `concept/` 文件包含：
     - `**受众**`
     - `**层级**`
     - `**Bloom 层级**`
     - `**前置概念**` / `**后置概念**`
   - 练习文件尚未引入这些元数据，不利于与知识图谱或学习路径自动关联。

4. **术语表 / 关键词未提取**
   - `concept/` 文件通常在开头列出“本节关键术语”。
   - Brown Inventory 未在文件头提取关键术语（如 `Copy`、`move`、`&mut`、`lifetime`、`Drop` 等）。

---

## 3. 与 `concept/` 权威页的对应关系

| Brown 练习 | 对应 `concept/` 主题（建议链接） |
|---|---|
| `inventory_01.rs` Move vs. Copy | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` |
| `inventory_02.rs` Mutable Borrowing | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` |
| `inventory_03.rs` Dangling References | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| `inventory_04.rs` Lifetime Annotations | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| `inventory_05.rs` RAII & Drop | `concept/01_foundation/01_ownership_borrow_lifetime/05_drop_and_raii.md` |
| `inventory_06.rs` Fixing Borrow Errors | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` |
| `inventory_07.rs` Vec Reallocation | `concept/01_foundation/06_collections/01_vec.md` |
| `inventory_08.rs` Ownership in Loops | `concept/01_foundation/04_control_flow/02_loops.md` |

> 建议在练习文件头增加 `**Related Concepts**` 或 `**前置概念**` 字段，直接链接到 `concept/` 权威页。

---

## 4. 改进建议（Q4 2026 可执行）

### 4.1 低工作量、高回报

1. **统一文件头模板**
   为每个 `inventory_0X.rs` 添加标准化 rustdoc 头：

   ```rust
   //! **EN**: Move Semantics vs. Copy Semantics
   //! **Summary**: Determine which types move ownership on assignment and which are bitwise copied.
   //! **Topic**: 移动语义 vs. Copy 语义 / Move Semantics vs. Copy Semantics
   //! **Bloom Level**: Understand → Apply
   //! **Related Concepts**: [Ownership](...) · [Copy Trait](...)
   ```

2. **为 TODO 添加英文对照**
   将关键 TODO 改为中英对照或英文优先，例如：

   ```rust
   // TODO (CN): 请改用借用，避免拿走 s1 和 s2 的所有权。
   // TODO (EN): Use borrowing instead of moving s1 and s2.
   ```

3. **提取关键术语**
   在文件头增加 `**Key Terms / 关键术语**`：
   - `inventory_01.rs`: `Copy` · `move` · `ownership`
   - `inventory_05.rs`: `RAII` · `Drop` · `destructor`

### 4.2 中等工作量

1. **建立练习 ↔ 权威页反向链接**
   - 在相关 `concept/` 文件底部“练习与延伸阅读”小节引用 Brown Inventory。
   - 在 `exercises/README.md` 或 `knowledge/` 学习路径中列出 Brown Inventory。

2. **引入 i18n 检查脚本**
   - 扩展 `scripts/kb_auditor.py` 或新增脚本，检查练习文件是否包含 `**EN**` / `**Summary**`。

### 4.3 高工作量（可选，视资源而定）

1. **生成英文版练习页面**
   - 若未来引入 `mdbook-i18n-helpers`，可将练习 rustdoc 一并提取到 PO 文件。
   - 短期更实际的做法是：维护一份 `exercises/src/ownership_borrowing/brown_inventories/README.en.md` 作为英文导航页。

---

## 5. 结论

- **状态**: Brown Inventory 8 个练习已具备基础双语注释，i18n **部分就绪**。
- **主要差距**: 缺少与 `concept/` 统一规范的 `**EN**` / `**Summary**` 元数据块、TODO 未完全双语化、缺少前置/后置概念链接。
- **建议 Q4 行动**: 先完成 8 个文件的文件头标准化（EN/Summary/Key Terms/Related Concepts），再扩展 TODO 双语化。无需引入重型 i18n 工具即可显著提升国际学习者体验。
