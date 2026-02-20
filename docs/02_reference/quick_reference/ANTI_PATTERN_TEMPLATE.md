# 速查卡反例速查小节 - 统一模板

> **用途**: 为 20 个速查卡提供统一的"反例速查"小节模板
> **创建日期**: 2026-02-12

---

## 模板结构

每个速查卡的反例速查小节应包含以下结构：

```markdown
    ## 反例速查

    ### 反例 1: [简短描述]

    **错误示例**:

    ```rust
    // ❌ 错误代码
    ```

    **原因**: [1-2 句话说明为什么错误]

    **修正**:

    ```rust
    // ✅ 正确做法
    ```

    ---

    ### 反例 2: [简短描述]

    （同上结构）

    ---

    ### 反例 N: [简短描述]

    （同上结构）

```

---

## 反例数量建议

| 速查卡类型 | 建议反例数 | 说明 |
| :--- | :--- | :--- || 核心概念（所有权、类型、错误处理） | 3-5 | 常见陷阱多 |
| 进阶主题（泛型、异步、宏） | 2-4 | 聚焦典型错误 |
| 工具/环境（Cargo、测试） | 2-3 | 配置与用法 |
| 其他 | 2-3 | 根据主题 |

---

## 示例：所有权反例

### 反例 1: 移动后使用

**错误示例**:

```rust
let s = String::from("hello");
let s2 = s;  // 所有权转移
println!("{}", s);  // ❌ 编译错误：s 已失效
```

**原因**: 值移动后原变量不可用。

**修正**:

```rust
let s = String::from("hello");
let s2 = s.clone();  // 或借用 &s
println!("{}", s);
```

---

### 反例 2: 可变借用与不可变借用冲突

**错误示例**:

```rust
let mut v = vec![1, 2, 3];
let r1 = &v;
let r2 = &mut v;  // ❌ 编译错误：已有不可变借用
```

**原因**: 同一时刻不能同时存在可变借用和不可变借用。

**修正**:

```rust
let mut v = vec![1, 2, 3];
let r1 = &v;
// 使用 r1 后再借出 r2
let r2 = &mut v;
```

---

## 编译失败测试（compile_fail）

典型反例可通过 `compile_fail` 在 doc-test 或 trybuild 中验证编译失败：

```rust
/// 反例：移动后使用——应编译失败
///
/// ```rust,compile_fail
/// let s = String::from("hello");
/// let s2 = s;
/// println!("{}", s);  // 错误：s 已失效
/// ```
```

**参考**: [testing_cheatsheet](./testing_cheatsheet.md) 编译测试；[c11 宏模块 trybuild](../../../crates/c11_macro_system/) 过程宏编译失败测试。

---

## 速查卡清单（已补全反例 2026-02-12）

- [x] ownership_cheatsheet
- [x] type_system.md
- [x] error_handling_cheatsheet
- [x] generics_cheatsheet
- [x] async_patterns
- [x] control_flow_functions_cheatsheet
- [x] threads_concurrency_cheatsheet
- [x] collections_iterators_cheatsheet
- [x] smart_pointers_cheatsheet
- [x] macros_cheatsheet
- [x] modules_cheatsheet
- [x] testing_cheatsheet
- [x] cargo_cheatsheet
- [x] design_patterns_cheatsheet
- [x] process_management_cheatsheet
- [x] network_programming_cheatsheet
- [x] algorithms_cheatsheet
- [x] wasm_cheatsheet
- [x] strings_formatting_cheatsheet
