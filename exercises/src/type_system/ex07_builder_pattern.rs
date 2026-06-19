//! # 练习 7: Builder 模式 / Exercise 7: Builder Pattern
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 消耗式 Builder、类型状态模式、方法链
//!
//! ## 题目描述 / Problem Description
//!
//! 实现一个 `RequestBuilder`，支持链式设置 HTTP 方法、URL、Header，
//! 最后通过 `build()` 构造一个不可变的 `Request`。
//!
//! 对应 Google Comprehensive Rust Day 3 Memory Management 练习：Builder Type。
//!
//! ## 要求 / Requirements
//!
//! - 不得修改公开 API / Do not modify the public API
//! - 不得使用 `unsafe` / Do not use `unsafe`
//! - `build()` 返回 `Result<Request, String>`，缺少 URL 时返回错误

use std::collections::HashMap;

/// HTTP 请求（不可变）
/// Immutable HTTP request
#[derive(Debug, Clone, PartialEq)]
pub struct Request {
    pub method: String,
    pub url: String,
    pub headers: HashMap<String, String>,
}

/// 请求构建器
/// Request builder
#[derive(Debug, Default)]
pub struct RequestBuilder {
    method: String,
    url: Option<String>,
    headers: HashMap<String, String>,
}

impl RequestBuilder {
    /// 创建空构建器
    pub fn new() -> Self {
        Self {
            method: "GET".to_string(),
            url: None,
            headers: HashMap::new(),
        }
    }

    /// 设置 HTTP 方法
    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = method.into();
        self
    }

    /// 设置 URL
    pub fn url(mut self, url: impl Into<String>) -> Self {
        self.url = Some(url.into());
        self
    }

    /// 添加 Header
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// 构造 Request
    pub fn build(self) -> Result<Request, String> {
        let url = self.url.ok_or_else(|| "URL is required".to_string())?;
        Ok(Request {
            method: self.method,
            url,
            headers: self.headers,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_chain() {
        let req = RequestBuilder::new()
            .method("POST")
            .url("https://example.com/api")
            .header("Content-Type", "application/json")
            .build()
            .expect("valid request");

        assert_eq!(req.method, "POST");
        assert_eq!(req.url, "https://example.com/api");
        assert_eq!(req.headers.get("Content-Type").unwrap(), "application/json");
    }

    #[test]
    fn test_default_method_is_get() {
        let req = RequestBuilder::new()
            .url("https://example.com")
            .build()
            .expect("valid request");

        assert_eq!(req.method, "GET");
    }

    #[test]
    fn test_missing_url_errors() {
        let result = RequestBuilder::new().build();
        assert!(result.is_err());
    }
}
