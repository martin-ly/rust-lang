# 错误传播机制

## 1. ?操作符与自动传播

- ?操作符自动将Result/Option中的错误/空值向上传播
- 编译期类型检查保证传播路径安全

## 2. map/map_err与链式传播

- map处理成功值，map_err处理错误值
- and_then链式组合多步操作

## 3. 错误链与上下文

- thiserror/anyhow等库支持错误链追踪与上下文信息
- source方法递归追踪底层错误

## 4. 工程案例

### 4.1 ?操作符传播

```rust
fn read_config(path: &str) -> Result<Config, ConfigError> {
    let s = std::fs::read_to_string(path)?;
    let cfg = toml::from_str(&s)?;
    Ok(cfg)
}
```

### 4.2 map_err转换

```rust
fn parse_num(s: &str) -> Result<i32, String> {
    s.parse().map_err(|e| format!("parse error: {}", e))
}
```

### 4.3 错误链追踪

```rust
use thiserror::Error;
#[derive(Error, Debug)]
enum MyError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),
}
```

## 5. 批判性分析与未来值值值展望

- Rust错误传播机制类型安全、零成本，但复杂错误链和上下文管理需依赖第三方库
- 未来值值值可探索自动化错误链分析与IDE集成

"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 概述
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 形式化分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


