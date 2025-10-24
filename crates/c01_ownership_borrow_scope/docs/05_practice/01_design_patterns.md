# 设计模式 - Design Patterns

**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 完整版  

## 📋 目录

- [设计模式 - Design Patterns](#设计模式---design-patterns)
  - [📋 目录](#-目录)
  - [1. 构建器模式](#1-构建器模式)
  - [2. 新类型模式](#2-新类型模式)
  - [3. RAII 模式](#3-raii-模式)

## 1. 构建器模式

```rust
struct Config {
    name: String,
    value: i32,
    enabled: bool,
}

struct ConfigBuilder {
    name: Option<String>,
    value: Option<i32>,
    enabled: bool,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            name: None,
            value: None,
            enabled: false,
        }
    }
    
    fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }
    
    fn value(mut self, value: i32) -> Self {
        self.value = Some(value);
        self
    }
    
    fn enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }
    
    fn build(self) -> Result<Config, &'static str> {
        Ok(Config {
            name: self.name.ok_or("name required")?,
            value: self.value.unwrap_or(0),
            enabled: self.enabled,
        })
    }
}
```

## 2. 新类型模式

```rust
struct UserId(u64);
struct ProductId(u64);

fn process_user(user_id: UserId) {
    // 类型系统防止传递错误的ID
}
```

## 3. RAII 模式

```rust
struct FileHandle {
    // 文件句柄
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        // 自动清理资源
    }
}
```

---

**相关文档**：

- [最佳实践](./02_best_practices.md)

**最后更新**: 2025年1月27日
