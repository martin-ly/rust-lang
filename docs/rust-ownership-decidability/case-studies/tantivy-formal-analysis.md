# Tantivy 搜索引擎形式化分析

> **主题**: 全文索引的并发安全
>
> **形式化框架**: 索引段 + 写入提交
>
> **参考**: tantivy Documentation

---

## 目录

- [Tantivy 搜索引擎形式化分析](#tantivy-搜索引擎形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 索引架构](#2-索引架构)
    - [定理 2.1 (段不可变)](#定理-21-段不可变)
  - [3. 写入语义](#3-写入语义)
    - [定理 3.1 (提交点)](#定理-31-提交点)
    - [定理 3.2 (回滚)](#定理-32-回滚)
  - [4. 搜索一致性](#4-搜索一致性)
    - [定理 4.1 (快照读取)](#定理-41-快照读取)
  - [5. 段合并](#5-段合并)
    - [定理 5.1 (后台合并)](#定理-51-后台合并)
  - [6. 反例](#6-反例)
    - [反例 6.1 (频繁提交)](#反例-61-频繁提交)
    - [反例 6.2 (写后读)](#反例-62-写后读)

---

## 1. 引言

Tantivy提供:

- 全文搜索引擎
- Lucene风格架构
- 增量索引
- 近实时搜索

---

## 2. 索引架构

### 定理 2.1 (段不可变)

> 已写入段不可修改，新文档写入新段。

```text
Index = [Segment1, Segment2, ..., SegmentN]
Segment = 倒排索引 + 存储字段
```

∎

---

## 3. 写入语义

### 定理 3.1 (提交点)

> commit创建新的搜索可见点。

```rust
let mut index_writer = index.writer(50_000_000)?;
index_writer.add_document(doc)?;
index_writer.commit()?;  // 新文档可搜索
```

∎

### 定理 3.2 (回滚)

> 未提交数据可丢弃。

```rust
index_writer.rollback()?;  // 丢弃未提交文档
```

∎

---

## 4. 搜索一致性

### 定理 4.1 (快照读取)

> Reader基于提交点快照搜索。

```rust
let reader = index.reader()?;
let searcher = reader.searcher();  // 当前快照
// 后续commit不影响此searcher
```

∎

---

## 5. 段合并

### 定理 5.1 (后台合并)

> 小段自动合并成大段。

```rust
let mut index_writer = index.writer_with_num_threads(1, 50_000_000)?;
index_writer.set_merge_policy(Box::new(LogMergePolicy::default()));
```

∎

---

## 6. 反例

### 反例 6.1 (频繁提交)

```rust
// 每次添加都提交，性能极差
for doc in docs {
    index_writer.add_document(doc)?;
    index_writer.commit()?;  // 开销大!
}

// 正确: 批量提交
for doc in docs {
    index_writer.add_document(doc)?;
}
index_writer.commit()?;
```

### 反例 6.2 (写后读)

```rust
index_writer.add_document(doc)?;
// 错误: 未提交不可搜索
let results = searcher.search(&query, &TopDocs::with_limit(10))?;

// 正确: 提交后重新加载reader
index_writer.commit()?;
reader.reload()?;
let searcher = reader.searcher();
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
