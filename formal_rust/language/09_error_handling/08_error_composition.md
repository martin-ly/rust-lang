# 错误组合模式

## 1. 错误累积与并行错误

- collect、try_join等收集多个错误
- 并行任务错误聚合

## 2. 组合子与链式处理

- and、or、map、map_err、and_then等组合子

## 3. 工程案例

### 3.1 错误累积

```rust
fn validate_all(inputs: &[&str]) -> Result<(), Vec<Error>> {
    let mut errors = Vec::new();
    for i in inputs {
        if let Err(e) = validate(i) { errors.push(e); }
    }
    if errors.is_empty() { Ok(()) } else { Err(errors) }
}
```

### 3.2 并行错误聚合

```rust
use futures::future::try_join_all;
async fn process_all(urls: Vec<String>) -> Result<Vec<String>, Vec<anyhow::Error>> {
    let results = try_join_all(urls.into_iter().map(fetch_url)).await;
    results
}
```

## 4. 批判性分析与未来展望

- Rust错误组合模式类型安全、组合性强，但并行错误聚合和累积需手动实现
- 未来可探索自动化错误聚合与分布式错误处理
