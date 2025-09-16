//! HTTP 协议实现模块

use crate::error::NetworkError;
use bytes::Bytes;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

/// HTTP 方法枚举
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum HttpMethod {
    GET,
    POST,
    PUT,
    DELETE,
    HEAD,
    OPTIONS,
    PATCH,
    TRACE,
    CONNECT,
}

impl FromStr for HttpMethod {
    type Err = NetworkError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "GET" => Ok(HttpMethod::GET),
            "POST" => Ok(HttpMethod::POST),
            "PUT" => Ok(HttpMethod::PUT),
            "DELETE" => Ok(HttpMethod::DELETE),
            "HEAD" => Ok(HttpMethod::HEAD),
            "OPTIONS" => Ok(HttpMethod::OPTIONS),
            "PATCH" => Ok(HttpMethod::PATCH),
            "TRACE" => Ok(HttpMethod::TRACE),
            "CONNECT" => Ok(HttpMethod::CONNECT),
            _ => Err(NetworkError::Protocol(format!(
                "Unknown HTTP method: {}",
                s
            ))),
        }
    }
}

impl fmt::Display for HttpMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HttpMethod::GET => write!(f, "GET"),
            HttpMethod::POST => write!(f, "POST"),
            HttpMethod::PUT => write!(f, "PUT"),
            HttpMethod::DELETE => write!(f, "DELETE"),
            HttpMethod::HEAD => write!(f, "HEAD"),
            HttpMethod::OPTIONS => write!(f, "OPTIONS"),
            HttpMethod::PATCH => write!(f, "PATCH"),
            HttpMethod::TRACE => write!(f, "TRACE"),
            HttpMethod::CONNECT => write!(f, "CONNECT"),
        }
    }
}

/// HTTP 版本枚举
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HttpVersion {
    Http1_0,
    Http1_1,
    Http2_0,
}

impl FromStr for HttpVersion {
    type Err = NetworkError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "HTTP/1.0" => Ok(HttpVersion::Http1_0),
            "HTTP/1.1" => Ok(HttpVersion::Http1_1),
            "HTTP/2.0" => Ok(HttpVersion::Http2_0),
            _ => Err(NetworkError::Protocol(format!(
                "Unknown HTTP version: {}",
                s
            ))),
        }
    }
}

impl fmt::Display for HttpVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HttpVersion::Http1_0 => write!(f, "HTTP/1.0"),
            HttpVersion::Http1_1 => write!(f, "HTTP/1.1"),
            HttpVersion::Http2_0 => write!(f, "HTTP/2.0"),
        }
    }
}

/// HTTP 状态码
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HttpStatusCode {
    pub code: u16,
    pub reason: String,
}

impl HttpStatusCode {
    pub fn new(code: u16, reason: impl Into<String>) -> Self {
        Self {
            code,
            reason: reason.into(),
        }
    }

    pub fn ok() -> Self {
        Self::new(200, "OK")
    }

    pub fn not_found() -> Self {
        Self::new(404, "Not Found")
    }

    pub fn internal_server_error() -> Self {
        Self::new(500, "Internal Server Error")
    }
}

impl fmt::Display for HttpStatusCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.code, self.reason)
    }
}

/// HTTP 请求结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpRequest {
    pub method: HttpMethod,
    pub uri: String,
    pub version: HttpVersion,
    pub headers: HashMap<String, String>,
    pub body: Bytes,
}

impl HttpRequest {
    pub fn new(method: HttpMethod, uri: impl Into<String>, version: HttpVersion) -> Self {
        Self {
            method,
            uri: uri.into(),
            version,
            headers: HashMap::new(),
            body: Bytes::new(),
        }
    }

    pub fn add_header(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.headers.insert(name.into(), value.into());
    }

    pub fn set_body(&mut self, body: impl Into<Bytes>) {
        self.body = body.into();
        self.add_header("Content-Length", self.body.len().to_string());
    }
}

/// HTTP 响应结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpResponse {
    pub version: HttpVersion,
    pub status: HttpStatusCode,
    pub headers: HashMap<String, String>,
    pub body: Bytes,
}

impl HttpResponse {
    pub fn new(version: HttpVersion, status: HttpStatusCode) -> Self {
        Self {
            version,
            status,
            headers: HashMap::new(),
            body: Bytes::new(),
        }
    }

    pub fn add_header(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.headers.insert(name.into(), value.into());
    }

    pub fn set_body(&mut self, body: impl Into<Bytes>) {
        self.body = body.into();
        self.add_header("Content-Length", self.body.len().to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_http_method_parsing() {
        assert_eq!(HttpMethod::from_str("GET").unwrap(), HttpMethod::GET);
        assert_eq!(HttpMethod::from_str("POST").unwrap(), HttpMethod::POST);
        assert!(HttpMethod::from_str("INVALID").is_err());
    }

    #[test]
    fn test_http_version_parsing() {
        assert_eq!(
            HttpVersion::from_str("HTTP/1.1").unwrap(),
            HttpVersion::Http1_1
        );
        assert_eq!(
            HttpVersion::from_str("HTTP/2.0").unwrap(),
            HttpVersion::Http2_0
        );
        assert!(HttpVersion::from_str("HTTP/3.0").is_err());
    }

    #[test]
    fn test_http_request_creation() {
        let mut request = HttpRequest::new(HttpMethod::GET, "/test", HttpVersion::Http1_1);

        request.add_header("Content-Type", "application/json");
        request.set_body(b"test body".as_slice());

        assert_eq!(request.method, HttpMethod::GET);
        assert_eq!(request.uri, "/test");
        assert_eq!(
            request.headers.get("Content-Type"),
            Some(&"application/json".to_string())
        );
        assert_eq!(request.body, Bytes::from("test body"));
    }

    #[test]
    fn test_http_response_creation() {
        let mut response = HttpResponse::new(HttpVersion::Http1_1, HttpStatusCode::ok());

        response.add_header("Content-Type", "text/html");
        response.set_body(b"<html></html>".as_slice());

        assert_eq!(response.status.code, 200);
        assert_eq!(
            response.headers.get("Content-Type"),
            Some(&"text/html".to_string())
        );
        assert_eq!(response.body, Bytes::from("<html></html>"));
    }
}
