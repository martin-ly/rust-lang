# Rust 2024 Edition `let chains` 深度专题

## 概述

`let chains` 是 Rust 2024 Edition 中稳定化的重要特性，允许在 `if` 和 `while` 条件中将 `let` 绑定与普通布尔表达式链式组合，大幅简化嵌套的 `if let` 代码。

## 语法

```rust
// 传统嵌套 if let
if let Some(x) = opt {
    if x > 0 {
        if let Ok(y) = parse(x) {
            // ...
        }
    }
}

// let chains 写法 (Rust 2024)
if let Some(x) = opt && x > 0 && let Ok(y) = parse(x) {
    // ...
}
```

## 核心优势

1. **减少嵌套层级**：代码更扁平，避免"右漂移"
2. **条件逻辑一目了然**：所有前置条件在同一行表达
3. **`while` 循环支持**：持续处理直到任一条件不满足
4. **`match` arm guards**：结合模式守卫进行复杂条件判断

## 重要语义差异

### `if let chains` vs `while let chains`

- **`if let chains`**：条件不满足时跳过当前代码块，不影响外层循环
- **`while let chains`**：条件不满足时**循环终止**，不是跳过当前项继续

```rust
// if let chains：过滤并处理
for record in records {
    if let Some(s) = record
        && let Ok(n) = s.parse::<i32>()
        && n > 0
    {
        // 只处理满足条件的记录，循环继续处理下一个
        process(n);
    }
}

// while let chains：持续处理直到条件终止
while let Some(packet) = stream.next()
    && let Ok(data) = parse_packet(packet)
    && data.is_valid()
{
    // 只要所有条件满足就持续处理
    // 任一条件不满足，循环立即终止
    handle(data);
}
```

## 完整示例

### 示例 1：解析并验证数值

```rust
pub fn parse_and_validate(input: Option<&str>) -> Result<i32, &'static str> {
    if let Some(s) = input
        && let Ok(n) = s.parse::<i32>()
        && n > 0
        && n <= 1000
    {
        Ok(n)
    } else {
        Err("输入必须是 1 到 1000 之间的正整数")
    }
}
```

### 示例 2：多模式组合

```rust
pub fn combine_options(a: Option<i32>, b: Option<i32>, c: Result<i32, &str>) -> Option<i32> {
    if let Some(x) = a
        && let Some(y) = b
        && x < y
        && let Ok(z) = c
        && z > x + y
    {
        Some(x + y + z)
    } else {
        None
    }
}
```

### 示例 3：配置解析

```rust
pub fn from_args(
    host_arg: Option<&str>,
    port_arg: Option<&str>,
    timeout_arg: Option<&str>,
) -> Result<ServerConfig, &'static str> {
    if let Some(host) = host_arg
        && !host.is_empty()
        && let Some(port_str) = port_arg
        && let Ok(port) = port_str.parse::<u16>()
        && port > 1024
        && let Some(timeout_str) = timeout_arg
        && let Ok(timeout_ms) = timeout_str.parse::<u64>()
        && timeout_ms >= 100
        && timeout_ms <= 60000
    {
        Ok(ServerConfig { host: host.to_string(), port, timeout_ms })
    } else {
        Err("参数无效")
    }
}
```

### 示例 4：match 守卫

```rust
pub fn classify_value(value: Result<Option<&str>, &str>) -> &'static str {
    match value {
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n > 0 && n % 2 == 0 => "正偶数",
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n > 0 => "正奇数",
        Ok(Some(s)) if let Ok(n) = s.parse::<i32>() && n < 0 => "负数",
        Ok(Some(_)) => "非数字字符串",
        Ok(None) => "空值",
        Err(_) => "错误结果",
    }
}
```

## 适用场景

- **参数验证**：多个输入需要同时满足解析和范围条件
- **嵌套 Option/Result 解构**：多层数据结构的安全访问
- **流处理**：从异步流或迭代器中按条件提取数据
- **命令解析**：CLI 参数的多阶段验证

## 注意事项

1. **while 语义**：`while let chains` 中任一条件失败会终止整个循环
2. **生命周期**：在 `impl Trait` 返回类型中，匿名生命周期需要显式命名
3. **可读性**：条件链过长时建议拆分或使用辅助函数
