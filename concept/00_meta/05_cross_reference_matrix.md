# Cross Reference Matrix（交叉引用矩阵）

> **受众**: [进阶]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **双维定位**: P×Eva — 评价概念间引用完整性

## 10.4 边界测试：交叉引用的循环依赖与 markdown 链接死链（文档问题）

```rust,compile_fail
// 概念: 交叉引用的反向验证
// 若文件 A 引用文件 B 的概念，但文件 B 不存在或重命名，读者会看到死链

// 模拟: 假设引用了一个不存在的文件
// [不存在的概念](./README.md)

fn main() {
    // 这不是 Rust 编译错误，而是文档维护问题
    // 但 Rust 的编译器错误信息模式类似：
    // "cannot find value `x` in this scope" — 类似于 "cannot find file"
    let _y = x; // ❌ 编译错误: cannot find value `x`
}
```

> **修正**: **交叉引用矩阵**的维护挑战：
>
> 1) 文件重命名导致链接断裂；
> 2) 概念合并或拆分导致引用指向错误位置；
> 3) 新增文件未加入索引。
>
> 解决方案：
>
> 1) **CI 检查** — 链接检查器（如 `mdbook-linkcheck`）；
> 2) **命名约定** — 文件 ID 稳定（如 `c01_ownership.md` 而非 `ownership.md`）；
> 3) **自动审计** — `concept_consistency_auditor.py` 扫描所有交叉引用。
>
> Rust 项目的引用验证：
>
> 1) `cargo doc` 验证 rustdoc 链接；
> 2) 编译器验证 `use` 语句（类似 markdown 链接检查）；
> 3) `cargo check` 验证依赖版本。
>
> 当前项目的交叉引用状态：208 文件，655 概念定义，170 交叉文件引用，0 无效引用。
> 这与 Wikipedia 的引用验证（自动检测死链）或大型代码库的依赖管理（cargo 自动解析）类似——知识库的引用健康需要持续维护。
> [来源: [mdBook Configuration](https://rust-lang.github.io/mdBook/format/configuration/renderers.html)] ·
> [来源: [Rustdoc Linking](https://doc.rust-lang.org/rustdoc/linking-to-items-by-name.html)]

## 相关概念文件

- [概念索引](./README.md) — 知识体系总览
- [Bloom 分类法](./03_bloom_taxonomy.md) — 认知层级标注标准
- [学习指南](./learning_guide.md) — 学习路径规划
- [概念审计指南](./08_concept_audit_guide.md) — 质量检查规范
- [语义空间坐标系](./semantic_space.md) — 概念定位方法
