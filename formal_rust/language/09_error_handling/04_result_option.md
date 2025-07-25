# Result和Option类型

## 1. 类型定义与性质

- `Result<T, E>`：可恢复错误的类型安全表示
- `Option<T>`：空值安全表示，防止空指针
- 两者均为代数数据类型，支持模式匹配

## 2. 单子性质与组合子

- Result/Option满足单子律，支持and_then、map、map_err等组合子
- ?操作符自动传播错误/空值

## 3. 工程案例

### 3.1 Result链式处理

```rust
fn process(path: &str) -> Result<usize, std::io::Error> {
    std::fs::read_to_string(path)
        .map(|s| s.len())
}
```

### 3.2 Option链式处理

```rust
fn get_first_even(nums: &[i32]) -> Option<i32> {
    nums.iter().find(|&&x| x % 2 == 0).copied()
}
```

### 3.3 ?操作符自动传播

```rust
fn parse_number(s: &str) -> Result<i32, std::num::ParseIntError> {
    let n: i32 = s.parse()?;
    Ok(n)
}
```

## 4. 批判性分析与未来展望

- Result/Option类型安全、零成本、组合性强，但链式处理过多时代码可读性下降
- 未来可探索更智能的错误/空值传播与IDE辅助
