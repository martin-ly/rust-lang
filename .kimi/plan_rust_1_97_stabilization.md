# Rust 1.97 稳定化准备清单

> **目标版本**: Rust 1.97.0 (预计 2026-07-09)
> **创建日期**: 2026-06-08
> **执行窗口**: 1.97.0 发布当日或次日

---

## 一、Crate 代码激活

以下文件中的 1.97 特性代码当前为注释/等效实现状态，需在 1.97 稳定后取消注释：

### 1. `crates/c08_algorithms/src/rust_197_features.rs`

| 特性 | 当前状态 | 稳定后操作 | 行号 |
|:---|:---|:---|:---|
| `VecDeque::truncate_front` | 🧪 等效实现 (`while len > n { pop_front() }`) | 取消注释 `deque.truncate_front(2)`，删除等效实现 | L16-30 |
| `VecDeque::retain_back` | 🧪 等效实现 (`rev()` 遍历) | ⚠️ **nightly 1.98.0 验证不存在**，可能推迟至 1.98+；若稳定：取消注释 | L35-50 |
| `float_algebraic` | 🧪 概念伪代码 | 若稳定：添加实际属性语法示例；若未稳定：保持现状 | L62-80 |
| `RandomSource` | 🧪 概念伪代码 | 若稳定：添加实际 trait 使用示例 | L91-101 |
| `box_vec_non_null` | 🔄 PFCP / 当前 nightly 方法不存在 | 若稳定：添加 `Box::into_non_null` / `Vec::into_non_null` 实际调用；名称以 Release Notes 为准 | L140-150 |
| `int_format_into` | 🧪 Nightly | 若稳定：添加 `n.format_into(&mut buf)` 实际调用 | L155-165 |
| C-variadic 定义 | 🔄 PFCP | 若稳定：恢复 `...` 语法签名 | L113-119 |

**重要发现 (2026-06-08 nightly 验证)**:

- `truncate_front(2)` 行为：**保留后部 2 个元素**，从 `[1,2,3,4,5]` 变为 `[4,5]`（与 `truncate(2)` 对称）
- `retain_back`: 在 nightly 1.98.0 (2026-06-05) 中不存在，需密切关注 PR #151973 实际合并状态

### 验证步骤

```bash
cd crates/c08_algorithms && cargo test --lib
```

---

## 二、文档状态更新

### 2.1 `concept/07_future/rust_1_97_preview.md`

- [ ] 更新文件标题和版本状态声明为 "Rust 1.97 稳定特性"
- [ ] 将 🔄 PFCP / 🧪 Nightly 标记更新为 ✅ Stable
- [ ] 添加 1.97 Release Notes 引用链接
- [ ] 将本文件迁移至 `docs/06_toolchain/06_21_rust_1_97_features.md`（或类似位置）

### 2.2 `knowledge/06_ecosystem/emerging/05_rust_1_96.md`

- [ ] 添加 1.97 新特性小节（若该文件是滚动更新的）
- [ ] 或新建 `05_rust_1_97.md`

### 2.3 各概念文档中的状态标记

| 文档 | 需更新内容 |
|:---|:---|
| `concept/03_advanced/08_nll_and_polonius.md` | 若 `VecDeque` 方法稳定，更新 "当前状态" 时间戳 |
| `concept/03_advanced/13_inline_assembly.md` | 若 s390x `vreg` 有任何变更，更新说明 |

---

## 三、练习补全

### 3.1 `exercises/src/rust_196_feature_exercises.rs`

当前已有：

- ✅ `NonZeroRangeExercises`
- ✅ `AssertUnwindSafeExercises`

1.97 稳定后需新增：

- [ ] `VecDequeExercises`（`truncate_front`、`retain_back`）
- [ ] `FloatAlgebraicExercises`（若 `float_algebraic` 稳定）

### 3.2 测试验证

```bash
cd exercises && cargo test
```

---

## 四、术语表更新

### 4.1 `concept/00_meta/terminology_glossary.md`

1.97 稳定后需将以下术语从 🔄/🧪 状态改为 ✅：

- [ ] `VecDeque::truncate_front` / `retain_back`
- [ ] `box_vec_non_null`
- [ ] `int_format_into`
- [ ] `c_variadic`（若稳定）
- [ ] `RandomSource`（若稳定）

---

## 五、CHANGELOG 更新

在 `CHANGELOG.md` 顶部添加新章节：

```markdown
## [3.1.0] - 2026-07-09 — Rust 1.97.0 稳定支持

### 语言特性
- VecDeque::truncate_front / retain_back（若稳定）
- ...（根据实际稳定内容补充）

### 文档更新
- ...

### Crate 代码
- ...
```

---

## 六、执行顺序

1. **发布当日**: 更新 rust-toolchain.toml channel 为 `1.97.0`
2. **第 1 小时**: 激活 crate 代码（取消注释）
3. **第 2 小时**: 运行全 workspace 测试
4. **第 3-4 小时**: 更新核心文档状态
5. **第 5-6 小时**: 补充新练习
6. **第 7-8 小时**: 更新术语表和 CHANGELOG

---

## 七、风险预案

| 风险 | 缓解措施 |
|:---|:---|
| 某特性未如期稳定 | 保持等效实现，更新状态为 "推迟至 1.98" |
| 稳定后 API 微调 | 根据实际 API 调整代码，而非直接取消注释 |
| 编译器行为差异 | 运行完整测试套件，对比 1.96 和 1.97 输出 |
