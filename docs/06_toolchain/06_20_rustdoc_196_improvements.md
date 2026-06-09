# Rustdoc 1.96 改进深度解析

> **版本状态声明**: 本文档覆盖 **Rust 1.96.0 (2026-05-28)** 稳定版 rustdoc 改进。
> **分级**: [A]
> **最后更新**: 2026-06-01
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

---

## 一、概述

Rust 1.96 对文档生成工具 `rustdoc` 进行了三项重要改进，影响 crate 作者和文档维护者的日常工作。
与语言特性或标准库 API 变更不同，rustdoc 改进是**工具链层面的体验优化**，不破坏现有代码，但可能要求调整文档编写习惯以获得最佳渲染效果。

| 改进项 | 影响人群 | 是否需要 action |
| :--- | :--- | :---: |
| Deprecation notes 渲染方式变更 | 维护有弃用 API 的 crate 作者 | 🟡 建议审查 |
| `missing_doc_code_examples` lint 范围缩小 | 使用 `#![warn(missing_doc_code_examples)]` 的项目 | 🟢 通常减少误报 |
| Sidebar 方法与关联函数分离 | 所有文档阅读者 | 🟢 纯体验提升 |

---

## 二、Deprecation Notes 渲染方式变更

### 2.1 变更前行为（< 1.96）

在 Rust 1.96 之前，`#[deprecated = "..."]` 属性的说明文本在 rustdoc 渲染时：

- 使用 `white-space: pre-wrap` CSS 样式
- 自动剥离 `<p>` 标签
- 多行文本的换行行为不可预测

```rust
// 旧行为下的渲染问题示例
#[deprecated(
    since = "2.0.0",
    note = "此函数已被 `new_api()` 替代。\n"
         "请迁移至新 API 以获得更好的性能。\n"
         "详见: https://docs.rs/mycrate/2.0.0"
)]
pub fn old_api() {}
```

**问题**: 多行 `note` 在文档中的换行可能不符合预期——有时全部挤在一行，有时产生过多空白。

### 2.2 变更后行为（1.96+）

Rust 1.96 将 deprecation notes 的渲染方式与普通文档对齐：

- **不再使用** `white-space: pre-wrap`
- **保留**标准 Markdown 处理流程
- 多行换行需使用标准 Markdown 方法：`"  \n"`（两个空格 + 换行）

### 2.3 对 Crate 作者的影响

**不需要修改的情况**:

- 单行 deprecation note → 行为不变
- 使用标准 Markdown 语法编写的 note → 行为改善

**建议审查的情况**:

- 依赖 `\n` 换行符控制格式的多行 note
- 使用 HTML 标签（如 `<p>`）的 note

**推荐写法**（1.96+）:

```rust
#[deprecated(
    since = "2.0.0",
    note = "请使用 [`new_api()`](Self::new_api) 替代。  \n\
            新 API 提供更佳的性能和类型安全。  \n\
            迁移指南: <https://docs.rs/mycrate/2.0.0/migration.html>"
)]
pub fn old_api() {}
```

> **关键差异**: `"  \\n"`（两个空格 + 反斜杠换行）在 Rust 字符串字面量中渲染为 Markdown 软换行，rustdoc 会正确将其转换为 `<br>` 或段落分隔。

---

## 三、`missing_doc_code_examples` Lint 范围缩小

### 3.1 背景

`missing_doc_code_examples` 是一个允许级 lint，用于提醒开发者为公共 API 添加文档中的代码示例：

```rust
#![warn(missing_doc_code_examples)]

/// 计算两个数的和
///
/// # Examples
/// ```
/// let result = mycrate::add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 { a + b }
```

### 3.2 1.96 的变更

**变更前**: lint 在以下位置触发：

- trait 声明中的方法
- `impl` 块中的方法（impl items）
- 公共函数和类型

**变更后**: lint **不再在 impl items 上触发**，仅在 trait 声明和顶层公共项上触发。

### 3.3 为什么做这个变更

1. **减少误报**: impl items 的方法通常已有 trait 文档中的示例，重复添加示例增加维护负担
2. **DRY 原则**: 文档应集中于定义处（trait），而非每个实现处重复
3. **实际反馈**: 社区报告 impl items 上的 lint 过于嘈杂

### 3.4 对项目的影响

```rust
# 1.96 之前: 可能需要在每个 impl 块中添加重复示例
# 1.96 之后: 只需在 trait 定义处添加示例

# 示例: 移除不必要的 impl item 文档示例后，lint 不再报错
pub trait Drawable {
    /// 绘制此对象
    ///
    /// # Examples
    /// ```
    /// let circle = Circle::new(5.0);
    /// circle.draw();
    /// ```
    fn draw(&self);
}

impl Drawable for Circle {
    // 1.96 之前: 此处缺少代码示例会触发 lint
    // 1.96 之后: 不再触发，因为 impl item 被豁免
    fn draw(&self) { /* ... */ }
}
```

---

## 四、Sidebar 方法与关联函数分离

### 4.1 变更内容

rustdoc 生成的 HTML 文档侧边栏（sidebar）中，**方法（methods）**和**关联函数（associated functions）**现在分为两个独立的列表显示。

```text
侧边栏结构（1.96 之前）:
├── Methods
│   ├── new
│   ├── from
│   ├── parse
│   └── display

侧边栏结构（1.96 之后）:
├── Functions
│   ├── new        ← 关联函数 (Self 参数)
│   ├── from       ← 关联函数 (Self 参数)
│   └── parse      ← 关联函数 (Self 参数)
├── Methods
│   └── display    ← 方法 (&self / &mut self 接收器)
```

### 4.2 为什么分离

| 维度 | 关联函数 | 方法 |
|:---|:---|:---|
| 调用语法 | `Type::func()` | `instance.method()` |
| 第一个参数 | 无 `self` | `&self` / `&mut self` / `self` |
| 用途 | 构造、转换、解析 | 操作实例状态 |
| 读者预期 | 在类型级别查找 | 在实例级别查找 |

分离后，文档读者可以更快地定位到所需 API：

- 想构造实例？查看 **Functions** 列表
- 想操作已有实例？查看 **Methods** 列表

### 4.3 对文档编写者的建议

无需修改现有文档。但可以在 trait/impl 文档中明确标注：

```rust
/// # Constructors
///
/// 使用以下关联函数创建实例：
/// - [`new()`](Self::new): 默认构造
/// - [`from_str()`](Self::from_str): 从字符串解析
///
/// # Methods
///
/// 构造后使用以下方法操作实例：
/// - [`process()`](Self::process): 处理数据
/// - [`validate()`](Self::validate): 验证状态
```

---

## 五、综合对比与迁移建议

| 场景 | 1.95 行为 | 1.96 行为 | 建议 action |
|:---|:---|:---|:---|
| 多行 deprecation note | `pre-wrap` 换行 | Markdown 处理 | 审查并测试渲染效果 |
| impl item 缺少 doc example | lint 触发 | lint 豁免 | 可删除重复示例 |
| 侧边栏导航 | 方法/函数混排 | 分类显示 | 无需修改，享受改善 |
| CI 文档构建 | 可能有 lint 失败 | impl item lint 减少 | 观察 CI 变化 |

---

## 六、来源与参考

| 来源 | 说明 |
|:---|:---|
| [Rust 1.96.0 Release Notes](https://github.com/rust-lang/rust/issues/156512) | 官方发布说明 |
| [rustdoc CHANGELOG](https://github.com/rust-lang/rust/blob/master/RELEASES.md) | rustdoc 专项变更日志 |
| [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) | rustdoc 官方文档 |

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+
**最后更新**: 2026-06-01
**状态**: ✅ 已与官方 Release Notes 逐条核对

> **权威来源**: [Rust 1.96.0 Release Notes](https://github.com/rust-lang/rust/issues/156512)
>
> **权威来源对齐变更日志**: 2026-06-01 创建 [来源: Official Release Notes #156512]
