# Rust 1.97.0 稳定特性

> **状态**: 预迁移模板 — 正式发布日（2026-07-09）根据官方 Release Notes 和探测结果填充内容。
> **对应预览文档**: `../../concept/07_future/rust_1_97_preview.md`
> **发布日执行清单**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
> **API 激活指南**: `.kimi/RUST_197_API_ACTIVATION_GUIDE.md`
> **探测报告**: `reports/RUST_197_API_PROBE_2026_06_28.md`

---

## 待填充目录（发布日按实际稳定特性勾选）

### 标准库新 API

- [ ] `NonZero` 位操作：`highest_one` / `lowest_one` / `bit_width`
- [ ] `char::is_control()` const 稳定化
- [ ] `NonZeroU32::midpoint` / `isqrt`
- [ ] `ptr::fn_addr_eq`
- [ ] `const size_of_val` / `align_of_val`
- [ ] `BuildHasherDefault::new` const
- [ ] `Box::as_ptr` / `Box::as_mut_ptr`
- [ ] `int::format_into`（`core::fmt::NumBuffer`）
- [ ] `VecDeque::truncate_front`（若进入 1.97.0）

### 语言与编译器

- [ ] 待根据 Release Notes 补充

### Cargo / rustdoc / 工具链

- [ ] 待根据 Release Notes 补充

---

## 发布日迁移步骤

1. 复制 `concept/07_future/rust_1_97_preview.md` 中已稳定章节的精炼版本到本文件。
2. 删除所有 `🧪 Nightly` / `🔄 PFCP` / `📋 RFC 讨论` 等未稳定标记。
3. 将代码块从 `rust,ignore` 改为可编译的 `rust`。
4. 在 `concept/07_future/rust_1_97_preview.md` 顶部添加重定向说明。
5. 更新 `CHANGELOG.md [3.1.0]` 和 `concept/00_meta/terminology_glossary.md`。

---

*本模板生成于 2026-06-28，随发布日执行清单同步更新。*
