# Rustdoc 1.96 改进速览 {#rustdoc-196-改进速览}

> **受众**: [进阶]
> **内容分级**: [综述级]
> **Bloom 层级**: 理解
> **跟踪版本**: Rust 1.96.0 stable (2026-05-28)
>
> **权威来源**: [Rust 1.96 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) · [rust-lang/rust#156512](https://github.com/rust-lang/rust/issues/156512)

---

## 一、弃用说明渲染改进 (Deprecation Notes Rendering) {#一弃用说明渲染改进-deprecation-notes-rendering}

**变更**: 弃用说明（`#[deprecated = "..."]`）的 HTML 渲染方式变得更可预测。

**影响**:

- 文档阅读者能更一致地看到弃用原因和替代方案
- 不再出现某些边界情况下弃用说明丢失或格式错乱的问题

**示例**:

```rust
#[deprecated(since = "1.96.0", note = "使用 `new_method` 替代")]
pub fn old_method() {}
```

在生成的文档中，弃用横幅现在始终显示在条目顶部，且 `note` 文本的 Markdown 渲染更可靠。

---

## 二、`missing_doc_code_examples` lint 范围缩小 {#二missing_doc_code_examples-lint-范围缩小}

**变更**: `missing_doc_code_examples` lint 不再在 **impl items** 上触发。

**背景**:

- 该 lint 要求公共 API 的文档中包含代码示例（`# Examples` 节）
- 此前，为 trait 实现方法（`impl Trait for Type { fn method() {} }`）编写文档示例往往与 trait 本身的文档重复
- 1.96 起，编译器不再要求 impl items 必须有独立代码示例，减少了无意义的 lint 警告

**影响**:

- `cargo doc` 输出更干净
- 开发者可以将精力集中在 trait 定义和独立函数的文档示例上

---

## 三、侧边栏方法分离 (Sidebar Separation) {#三侧边栏方法分离-sidebar-separation}

**变更**: 在生成的 HTML 文档侧边栏中，**方法（Methods）**和**关联函数（Associated Functions）**现在分开显示。

**背景**:

- 此前，impl 块中的所有函数都混在一起，难以区分 `self` 接收者方法和平凡关联函数
- 1.96 起，侧边栏添加了二级分组：
  - **Methods**: `fn method(&self)`、`fn method_mut(&mut self)`、`fn method_owned(self)`
  - **Functions**: `fn new()`、`fn default()` 等无 `self` 参数的关联函数

**影响**:

- 提升标准库和大型 crate 文档的可导航性
- 与 [docs.rs](https://docs.rs) 的渲染风格保持一致

---

## 四、兼容性注意 {#四兼容性注意}

以上三项改进均为**纯文档体验优化**，不影响：

- 源代码编译
- 现有文档注释语法
- `cargo doc` 的命令行接口

无需代码修改即可自动获得改进（使用 Rust 1.96+ 重新生成文档即可）。

---

> **最后更新**: 2026-06-08
> **状态**: ✅ 与 Rust 1.96.0 Release Notes 逐项核对完成
