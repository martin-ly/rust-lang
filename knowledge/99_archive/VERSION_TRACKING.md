# Rust 版本跟踪

> **Bloom 层级**: 理解

> 自动跟踪 Rust 版本更新和知识库同步状态

---

## 当前目标版本
>
> **[来源: Rust Official Docs]**

**Rust**: 1.95.0
**Edition**: 2024
**最后同步**: 2026-05-06

---

## 版本同步状态
>
> **[来源: Rust Official Docs]**

### Rust 1.95.0 ✅
>
> **[来源: Rust Official Docs]**

| 特性 | 文档状态 | 代码示例 | 最后更新 |
|------|---------|---------|----------|
| cfg_select! | ✅ 完整 | ✅ | 2026-05-06 |
| if let guards | ✅ 完整 | ✅ | 2026-05-06 |
| core::range | ✅ 完整 | ✅ | 2026-05-06 |
| Atomic*::update/try_update | ✅ 完整 | ✅ | 2026-05-06 |
| Vec::push_mut / insert_mut | ✅ 完整 | ✅ | 2026-05-06 |
| VecDeque/LinkedList push_*_mut | ✅ 完整 | ✅ | 2026-05-06 |
| *const/mut T::as_ref_unchecked | ✅ 完整 | ✅ | 2026-05-06 |
| Layout::dangling_ptr/repeat/extend_packed | ✅ 完整 | ✅ | 2026-05-06 |
| core::hint::cold_path | ✅ 完整 | ✅ | 2026-05-06 |
| bool::TryFrom<{integer}> | ✅ 完整 | ✅ | 2026-05-06 |
| MaybeUninit/Cell 数组转换 | ✅ 完整 | ✅ | 2026-05-06 |
| PowerPC/PowerPC64 内联汇编 | ✅ 完整 | ✅ | 2026-05-06 |
| fmt::from_fn / ControlFlow const | ✅ 完整 | ✅ | 2026-05-06 |
| --remap-path-scope | ✅ 完整 | - | 2026-05-06 |
| Apple 嵌入式平台 Tier 2 | ✅ 完整 | - | 2026-05-06 |

### Rust 1.94.0 ✅ (历史归档)
>
> **[来源: Rust Official Docs]**

| 特性 | 文档状态 | 代码示例 | 最后更新 |
|------|---------|---------|----------|
| array_windows | ✅ 完整 | ✅ | 2026-03-19 |
| LazyCell/LazyLock | ✅ 完整 | ✅ | 2026-03-19 |
| char→usize | ✅ 完整 | ✅ | 2026-03-19 |
| 数学常量 | ✅ 完整 | ✅ | 2026-03-19 |
| ControlFlow | ✅ 完整 | ✅ | 2026-03-19 |
| Peekable::next_if | ✅ 完整 | ✅ | 2026-03-19 |
| Edition 2024 | ✅ 完整 | ✅ | 2026-03-19 |

### Rust 1.96.0 ⏳ (Beta / 预计 2026-05-28)
>
> **[来源: Rust Official Docs]**

| 特性 | 预计发布 | 准备状态 | 文档 |
|------|---------|---------|------|
| 新 Range 类型 | 2026-05-28 | 🔄 准备中 | - |
| cargo script | 2026-05-28 | 🔄 准备中 | - |

---

## 同步检查清单

### 每版本发布时执行

- [ ] 阅读官方 Release Notes
- [ ] 识别新特性和破坏性变更
- [ ] 创建/更新对应文档
- [ ] 添加代码示例
- [ ] 更新本跟踪文件
- [ ] 测试代码示例
- [ ] 更新 INDEX.md

### 每季度执行

- [ ] 审查所有文档的时效性
- [ ] 更新过时内容
- [ ] 检查链接有效性
- [ ] 更新权威引用

---

## 历史记录

| 日期 | 版本 | 变更 |
|------|------|------|
| 2026-03-19 | 1.94.0 | 初始创建，完成所有 1.94 特性文档 |

---

**维护者**: Rust 学习项目团队
---

> **权威来源**: [来源: Rust 官方文档](https://doc.rust-lang.org/)

---

## 相关概念

- [Rust 生产案例研究](case_studies.md)
- [Rust 知识库建设完成报告](COMPLETION_REPORT_2026_03_1.94.md)
