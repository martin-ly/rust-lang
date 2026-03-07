# Rust 所有权可判定性项目 - 完成路线图 2026 Q1

> **目标日期**: 2026-06-30 (100% 完成)
> **当前日期**: 2026-03-07
> **剩余时间**: ~16 周

---

## 一、目标定义 (什么是 "100% 完成")

### 1.1 100% 完成标准

```markdown
## 文档完整性
- [ ] 所有计划模块有实质内容 (L2+ 深度)
- [ ] 无空目录或仅 README 的目录
- [ ] 所有代码示例可编译运行

## 形式化完整性
- [ ] 所有核心概念有形式化定义
- [ ] 所有定理有完整证明 (L2+)
- [ ] Coq 代码通过验证

## 权威对齐
- [ ] 覆盖 The Rust Book 所有章节
- [ ] 覆盖 The Reference 核心章节
- [ ] 覆盖 The Rustonomicon 核心章节

## 可验证性
- [ ] 所有链接有效
- [ ] 所有代码示例通过 CI
- [ ] 交叉引用完整
```

### 1.2 优先级矩阵

| 模块 | 当前状态 | 目标深度 | 优先级 | 工作量 |
|------|---------|---------|-------|-------|
| 17-unsafe-rust (新建) | ❌ 缺失 | L3 | 🔴 P0 | 4周 |
| 08-advanced-topics/data-layout | ❌ 缺失 | L2 | 🔴 P0 | 2周 |
| 03-verification-tools | 🟡 浅 | L2 | 🟡 P1 | 2周 |
| 05-comparative-study | 🟡 浅 | L2 | 🟡 P1 | 2周 |
| 11-design-patterns (扩展) | 🟢 基础 | L2 | 🟡 P1 | 2周 |
| 其他深化 | 🟡 中 | L3 | 🟢 P2 | 4周 |

---

## 二、详细执行计划

### Phase 1: 关键缺失填补 (Week 1-4) 🔴

#### Week 1: Unsafe Rust 基础

**任务清单**:

- [ ] 创建 `17-unsafe-rust/` 目录结构
- [ ] 编写 `17-unsafe-rust/README.md` (导航)
- [ ] 编写 `17-unsafe-rust/01-intro.md` (Unsafe 概述)
- [ ] 编写 `17-unsafe-rust/02-raw-pointers.md` (原始指针)

**验收标准**:

- 每个文档 >300 行
- 包含形式化定义 (Unsafe 操作语义)
- 包含可运行代码示例

#### Week 2: Data Layout & 内存布局

**任务清单**:

- [ ] 编写 `08-advanced-topics/data-layout.md`
- [ ] 编写 `08-advanced-topics/repr.md` (repr 属性)
- [ ] 编写 `08-advanced-topics/alignment.md` (内存对齐)

**关键内容**:

- `#[repr(C)]`, `#[repr(Rust)]`, `#[repr(packed)]`
- ZST, DST, 对齐规则
- FFI 布局兼容性

#### Week 3: Uninitialized Memory & Drop

**任务清单**:

- [ ] 编写 `17-unsafe-rust/03-uninitialized.md`
- [ ] 编写 `17-unsafe-rust/04-drop-flags.md`
- [ ] 编写 `17-unsafe-rust/05-maybe-uninit.md`

**参考**: The Rustonomicon Ch 5, 6

#### Week 4: Panic & Unwinding

**任务清单**:

- [ ] 编写 `17-unsafe-rust/06-panic.md`
- [ ] 编写 `17-unsafe-rust/07-unwinding.md`
- [ ] 编写 `17-unsafe-rust/08-exception-safety.md`

**关键内容**:

- catch_unwind
- UnwindSafe trait
- 异常安全保证

### Phase 2: 内容扩展 (Week 5-8) 🟡

#### Week 5: 验证工具深化

**任务清单**:

- [ ] 扩展 `03-verification-tools/03-03-miri-deep-dive.md`
- [ ] 编写 `03-verification-tools/03-04-kani-guide.md`
- [ ] 编写 `03-verification-tools/03-05-prusti-guide.md`

#### Week 6: 对比研究扩展

**任务清单**:

- [ ] 编写 `05-comparative-study/05-02-rust-vs-cpp.md`
- [ ] 编写 `05-comparative-study/05-03-rust-vs-go.md`
- [ ] 编写 `05-comparative-study/05-04-rust-vs-swift.md`

**对比维度**:

- 内存安全机制
- 并发模型
- 性能特征
- 生态成熟度

#### Week 7-8: 设计模式扩展

**任务清单**:

- [ ] 编写 `11-design-patterns/behavioral/state.md`
- [ ] 编写 `11-design-patterns/behavioral/iterator.md`
- [ ] 编写 `11-design-patterns/structural/bridge.md`
- [ ] 编写 `11-design-patterns/structural/composite.md`

### Phase 3: 对齐优化 (Week 9-12) 🟢

#### Week 9-10: 与 The Rust Book 对齐

**对齐检查清单**:

- [ ] Ch 13: Iterators & Closures 完全覆盖
- [ ] Ch 19: Patterns 完全覆盖
- [ ] Ch 20: Advanced Features 完全覆盖

#### Week 11-12: 与 The Reference 对齐

**对齐检查清单**:

- [ ] Ch 6: Items 全部类型覆盖
- [ ] Ch 10: Type System 完整对应
- [ ] Ch 13: Memory Model 补充

### Phase 4: 质量冲刺 (Week 13-16) ⭐

#### Week 13-14: 代码验证

**任务清单**:

- [ ] 所有 Rust 代码示例通过 `cargo check`
- [ ] 所有 Coq 代码通过 `coqc`
- [ ] 修复编译错误

#### Week 15: 链接检查

**任务清单**:

- [ ] 运行链接检查脚本
- [ ] 修复所有失效链接
- [ ] 补充缺失的交叉引用

#### Week 16: 最终审查

**任务清单**:

- [ ] 100% 完成度验证
- [ ] 生成最终报告
- [ ] 创建发布标签

---

## 三、资源需求

### 3.1 人力投入

| 角色 | 人数 | 投入时间 | 职责 |
|------|-----|---------|------|
| 技术写作 | 1-2 | 全职 | 文档撰写 |
| Rust 专家 | 1 | 兼职(20%) | 技术审查 |
| 形式化专家 | 1 | 兼职(10%) | Coq/形式化审查 |

### 3.2 工具需求

- Coq 8.17+ (形式化验证)
- Rust 1.94+ (代码示例)
- mdbook (文档构建)
- 链接检查工具

---

## 四、风险与应对

| 风险 | 可能性 | 影响 | 应对措施 |
|------|-------|------|---------|
| Unsafe 内容复杂度高 | 高 | 延迟 | 分阶段交付，先基础后深度 |
| Rust 版本更新 | 中 | 返工 | 锁定 1.94 基准，后续迭代更新 |
| 形式化证明困难 | 中 | 质量下降 | 适当降低形式化深度，保证 L2 |
| 人力不足 | 中 | 进度延迟 | 优先级排序，P0 必须完成 |

---

## 五、成功指标

### 5.1 量化指标

| 指标 | 当前 | 目标 | 测量方法 |
|------|-----|------|---------|
| 总文档数 | ~350 | 400+ | 文件计数 |
| L2+ 文档比例 | 50% | 80% | 行数统计 |
| 代码可编译率 | ? | 100% | CI 检查 |
| 链接有效 rate | ? | 100% | 链接检查 |
| Book 覆盖率 | 75% | 95% | 章节对照 |
| Reference 覆盖率 | 55% | 80% | 章节对照 |

### 5.2 定性指标

- [ ] 专家评审通过
- [ ] 社区反馈积极
- [ ] 可作为教学材料使用

---

## 六、每周检查清单模板

```markdown
## Week X 检查清单

### 计划任务
- [ ] 任务 1
- [ ] 任务 2

### 完成标准
- [ ] 代码可编译
- [ ] 文档 >300 行
- [ ] 通过自审

### 问题记录
- 问题 1: ...
- 问题 2: ...

### 下周计划
- ...
```

---

## 七、可持续维护建议

### 7.1 长期维护机制

1. **版本冻结**: 每季度发布一个稳定版本
2. **增量更新**: 跟随 Rust 发布周期更新
3. **社区贡献**: 接受 PR，建立贡献指南
4. **定期审查**: 每半年进行一次全面审查

### 7.2 质量保证

1. **CI/CD**: 自动化代码检查和链接检查
2. **代码审查**: 所有变更需审查
3. **版本标记**: 明确标记每文档对应的 Rust 版本

---

*路线图制定: 2026-03-07*
*计划周期: 16 周*
*目标: 2026-06-30 100% 完成*
