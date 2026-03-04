# Pulldown-CMark Markdown形式化分析

> **主题**: 快速Markdown解析
>
> **形式化框架**: 拉取解析 + 事件流
>
> **参考**: pulldown-cmark Documentation

---

## 目录

- [Pulldown-CMark Markdown形式化分析](#pulldown-cmark-markdown形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 拉取解析](#2-拉取解析)
    - [定理 2.1 (惰性解析)](#定理-21-惰性解析)
  - [3. 事件类型](#3-事件类型)
    - [定理 3.1 (平衡标签)](#定理-31-平衡标签)
  - [4. 零拷贝](#4-零拷贝)
    - [定理 4.1 (字符串引用)](#定理-41-字符串引用)
  - [5. 反例](#5-反例)
    - [反例 5.1 (未处理所有事件)](#反例-51-未处理所有事件)
    - [反例 5.2 (递归深度)](#反例-52-递归深度)

---

## 1. 引言

pulldown-cmark提供:

- CommonMark兼容
- 拉取式解析
- 事件驱动API
- 零拷贝选项

---

## 2. 拉取解析

### 定理 2.1 (惰性解析)

> 按需生成事件，不构建完整AST。

```rust
let parser = Parser::new(markdown);
for event in parser {
    match event {
        Event::Start(Tag::Paragraph)) => {},
        Event::Text(text) => {},
        Event::End(Tag::Paragraph)) => {},
        _ => {}
    }
}
```

∎

---

## 3. 事件类型

### 定理 3.1 (平衡标签)

> Start/End事件成对出现。

```rust
// 输入: **bold**
// 事件: Start(Emphasis), Text("bold"), End(Emphasis)
```

∎

---

## 4. 零拷贝

### 定理 4.1 (字符串引用)

> 默认返回原始输入的切片。

```rust
let markdown = "Hello **world**";
let parser = Parser::new(markdown);
// Event::Text 返回 &str 指向 markdown
```

∎

---

## 5. 反例

### 反例 5.1 (未处理所有事件)

```rust
// 忽略某些事件可能导致渲染错误
for event in parser {
    if let Event::Text(t) = event {
        output.push_str(&t);
    }
    // 忽略 Start/End，格式丢失!
}
```

### 反例 5.2 (递归深度)

```rust
// 嵌套HTML可能深度过大
// 需限制递归或使用迭代方式
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
