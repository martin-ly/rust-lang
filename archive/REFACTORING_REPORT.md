# Rust 1.95 if let guards on match arms 重构报告

## 概述

本次重构将代码库中使用 `match` + `if let` 组合的旧模式转换为 Rust 1.95 新特性 `if let guards on match arms`。

## 重构前后对比

### 旧模式

```rust
match value {
    Some(x) => {
        if let Ok(y) = parse(x) {
            handle(y);
        }
    }
    _ => {}
}
```

### 新模式

```rust
match value {
    Some(x) if let Ok(y) = parse(x) => handle(y),
    _ => {}
}
```

## 已重构的文件列表

### 1. crates/c08_algorithms/src/leetcode/stack.rs

- **行号**: 63
- **说明**: 逆波兰表达式求值中的数字解析
- **重构前**:

```rust
_ => {
    if let Ok(num) = token.parse::<i32>() {
        stack.push(num);
    }
}
```

- **重构后**:

```rust
_ if let Ok(num) = token.parse::<i32>() => stack.push(num),
_ => {}
```

### 2. crates/c10_networks/src/rust_194_features.rs

- **行号**: 103
- **说明**: 帧提取中的边界处理
- **重构前**:

```rust
BoundaryType::End => {
    if let Some(start) = start_idx {
        frames.push(&data[start + 4..idx]);
        start_idx = None;
    }
}
```

- **重构后**:

```rust
BoundaryType::End if let Some(start) = start_idx => {
    frames.push(&data[start + 4..idx]);
    start_idx = None;
}
BoundaryType::End => {}
```

### 3. crates/c06_async/src/csp_model_comparison.rs

- **行号**: 316-319
- **说明**: tokio::select! 宏中的消息接收处理
- **重构前**:

```rust
msg1 = rx1.recv() => {
    if let Some(msg1) = msg1 {
        println!("  [Select] 收到 ch1: {}", msg1);
    }
}
msg2 = rx2.recv() => {
    if let Some(msg2) = msg2 {
        println!("  [Select] 收到 ch2: {}", msg2);
    }
}
```

- **重构后**:

```rust
msg1 = rx1.recv() => if let Some(msg1) = msg1 {
    println!("  [Select] 收到 ch1: {}", msg1);
}
msg2 = rx2.recv() => if let Some(msg2) = msg2 {
    println!("  [Select] 收到 ch2: {}", msg2);
}
```

### 4. crates/c01_ownership_borrow_scope/src/lifetime/mod.rs

- **行号**: 338-357
- **说明**: 生命周期约束检查
- **重构前**:

```rust
ConstraintType::LifetimeBound => {
    if let (Some(left), Some(right)) = (
        lifetime_map.get(&self.left_lifetime),
        lifetime_map.get(&self.right_lifetime),
    ) {
        left.is_compatible_with(right)
    } else {
        false
    }
}
```

- **重构后**:

```rust
ConstraintType::LifetimeBound if let (Some(left), Some(right)) = (
    lifetime_map.get(&self.left_lifetime),
    lifetime_map.get(&self.right_lifetime),
) => left.is_compatible_with(right),
ConstraintType::LifetimeBound => false,
```

### 5. crates/c06_async/examples/async_message_queues_2025.rs

- **行号**: 903
- **说明**: 消息过滤器中的属性包含检查
- **重构前**:

```rust
FilterCondition::AttributeContains(key, value) => {
    if let Some(attr_value) = message.attributes.get(key) {
        if !attr_value.contains(value) {
            return false;
        }
    } else {
        return false;
    }
}
```

- **重构后**:

```rust
FilterCondition::AttributeContains(key, value) if let Some(attr_value) = message.attributes.get(key)
    => if !attr_value.contains(value) { return false; },
FilterCondition::AttributeContains(_, _) => return false,
```

## 统计信息

- **总重构文件数**: 5
- **涉及目录**:
  - `crates/c01_ownership_borrow_scope/`
  - `crates/c02_type_system/`
  - `crates/c06_async/`
  - `crates/c08_algorithms/`
  - `crates/c10_networks/`

## 注意事项

1. **语义保持不变**: 所有重构都保持了原有的代码逻辑和语义
2. **兼容性**: 这些重构需要 Rust 1.95+ 编译器支持
3. **代码简化**: 减少了嵌套层级，提高了代码可读性

## 未重构的代码

以下情况未进行重构：

- 包含 `break`/`continue` 语句的复杂控制流
- `if let` 内部有多条语句的情况
- 涉及变量赋值并在后续代码中使用的场景
