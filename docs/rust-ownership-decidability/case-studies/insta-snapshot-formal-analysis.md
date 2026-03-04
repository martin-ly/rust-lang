# Insta 快照测试形式化分析

> **主题**: 快照测试的确定性
>
> **形式化框架**: 输出不变式 + 更新语义
>
> **参考**: insta Documentation

---

## 目录

- [Insta 快照测试形式化分析](#insta-快照测试形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 快照语义](#2-快照语义)
    - [定理 2.1 (精确匹配)](#定理-21-精确匹配)
    - [定理 2.2 (序列化快照)](#定理-22-序列化快照)
  - [3. 内联快照](#3-内联快照)
    - [定理 3.1 (源码内联)](#定理-31-源码内联)
  - [4. 更新模式](#4-更新模式)
    - [定理 4.1 (更新语义)](#定理-41-更新语义)
  - [5. 反例](#5-反例)
    - [反例 5.1 (非确定性输出)](#反例-51-非确定性输出)
    - [反例 5.2 (大快照文件)](#反例-52-大快照文件)

---

## 1. 引言

Insta提供:

- 内联/文件快照
- 自动更新
- 差异查看
- 红action过滤

---

## 2. 快照语义

### 定理 2.1 (精确匹配)

> 实际输出必须与快照完全一致。

```rust
#[test]
fn test_simple() {
    let result = generate_output();
    insta::assert_snapshot!(result, @"expected output");
}
```

∎

### 定理 2.2 (序列化快照)

> 支持复杂类型的快照。

```rust
#[derive(Serialize)]
struct User { id: u64, name: String }

insta::assert_json_snapshot!(user, {
    ".id" => "[user-id]"  // 红action
});
```

∎

---

## 3. 内联快照

### 定理 3.1 (源码内联)

> 内联快照存储在源码中。

```rust
insta::assert_snapshot!(result, @"snapshot content");
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//          运行 cargo insta review 更新
```

∎

---

## 4. 更新模式

### 定理 4.1 (更新语义)

| 模式 | 行为 |
|------|------|
| always | 无条件更新 |
| new | 仅新快照 |
| unmatched | 不匹配时更新 |

```bash
INSTA_UPDATE=always cargo test
```

∎

---

## 5. 反例

### 反例 5.1 (非确定性输出)

```rust
// 危险: 包含时间戳
let output = format!("Result at {}", Utc::now());
insta::assert_snapshot!(output);  // 总是失败!

// 正确: 红action或模拟时间
insta::assert_snapshot!(output, {
    "[datetime]" => "[redacted]"
});
```

### 反例 5.2 (大快照文件)

```rust
// 避免巨大快照，考虑选择性验证
insta::assert_snapshot!(huge_json);  // 难以审查

// 更好: 验证结构而非完整输出
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
