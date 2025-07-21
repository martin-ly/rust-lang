# 错误处理机制

## 1. 错误传播与单调性

- Result/Option类型自动传播错误
- 错误单调性：链中任一环出错即终止

## 2. try/catch与错误恢复

- 支持局部try/catch捕获与恢复
- 错误上下文传递与日志记录

## 3. 工程案例

```rust
fn error_middleware(next: impl Fn(String) -> Result<String, String>) -> impl Fn(String) -> Result<String, String> {
    move |req| {
        match next(req) {
            Ok(resp) => Ok(resp),
            Err(e) => { println!("error: {}", e); Err(e) }
        }
    }
}
```

## 4. 批判性分析与未来展望

- 错误处理机制提升健壮性，但复杂链路下错误定位难
- 未来可探索自动化错误链追踪与IDE集成
