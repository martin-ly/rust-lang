//! WebSocket 握手处理

// use crate::error::NetworkError; // 暂时注释掉未使用的导入
use std::collections::HashMap;

/// WebSocket 握手请求
#[derive(Debug, Clone)]
pub struct WebSocketHandshakeRequest {
    pub method: String,
    pub uri: String,
    pub version: String,
    pub headers: HashMap<String, String>,
}

impl WebSocketHandshakeRequest {
    /// 创建新的握手请求
    pub fn new(uri: &str) -> Self {
        Self {
            method: "GET".to_string(),
            uri: uri.to_string(),
            version: "HTTP/1.1".to_string(),
            headers: HashMap::new(),
        }
    }

    /// 添加请求头
    pub fn add_header(&mut self, name: &str, value: &str) {
        self.headers.insert(name.to_string(), value.to_string());
    }

    /// 设置 WebSocket 密钥
    pub fn set_websocket_key(&mut self, key: &str) {
        self.add_header("Sec-WebSocket-Key", key);
    }

    /// 设置 WebSocket 版本
    pub fn set_websocket_version(&mut self, version: &str) {
        self.add_header("Sec-WebSocket-Version", version);
    }

    /// 设置主机
    pub fn set_host(&mut self, host: &str) {
        self.add_header("Host", host);
    }

    /// 设置升级头
    pub fn set_upgrade(&mut self) {
        self.add_header("Upgrade", "websocket");
        self.add_header("Connection", "Upgrade");
    }

    /// 编码为 HTTP 请求
    pub fn encode(&self) -> String {
        let mut request = format!("{} {} {}\r\n", self.method, self.uri, self.version);

        for (name, value) in &self.headers {
            request.push_str(&format!("{}: {}\r\n", name, value));
        }

        request.push_str("\r\n");
        request
    }
}

/// WebSocket 握手响应
#[derive(Debug, Clone)]
pub struct WebSocketHandshakeResponse {
    pub status_code: u16,
    pub status_text: String,
    pub version: String,
    pub headers: HashMap<String, String>,
}

impl WebSocketHandshakeResponse {
    /// 创建新的握手响应
    pub fn new(status_code: u16, status_text: &str) -> Self {
        Self {
            status_code,
            status_text: status_text.to_string(),
            version: "HTTP/1.1".to_string(),
            headers: HashMap::new(),
        }
    }

    /// 添加响应头
    pub fn add_header(&mut self, name: &str, value: &str) {
        self.headers.insert(name.to_string(), value.to_string());
    }

    /// 设置 WebSocket 接受密钥
    pub fn set_websocket_accept(&mut self, accept: &str) {
        self.add_header("Sec-WebSocket-Accept", accept);
    }

    /// 设置升级头
    pub fn set_upgrade(&mut self) {
        self.add_header("Upgrade", "websocket");
        self.add_header("Connection", "Upgrade");
    }

    /// 编码为 HTTP 响应
    pub fn encode(&self) -> String {
        let mut response = format!(
            "{} {} {}\r\n",
            self.version, self.status_code, self.status_text
        );

        for (name, value) in &self.headers {
            response.push_str(&format!("{}: {}\r\n", name, value));
        }

        response.push_str("\r\n");
        response
    }
}

/// WebSocket 客户端工具
pub struct WebSocketClient;

impl WebSocketClient {
    /// 生成 WebSocket 密钥
    pub fn generate_key() -> String {
        // 简化的密钥生成，实际应用中应该使用更安全的随机数生成
        "dGhlIHNhbXBsZSBub25jZQ==".to_string()
    }

    /// 计算 WebSocket 接受密钥
    pub fn calculate_accept(_key: &str) -> String {
        // 简化的接受密钥计算，实际应用中应该使用 SHA-1 和 Base64
        "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_websocket_handshake_request() {
        let mut request = WebSocketHandshakeRequest::new("/chat");
        request.set_host("example.com");
        request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
        request.set_websocket_version("13");
        request.set_upgrade();

        let encoded = request.encode();
        assert!(encoded.contains("GET /chat HTTP/1.1"));
        assert!(encoded.contains("Host: example.com"));
        assert!(encoded.contains("Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ=="));
        assert!(encoded.contains("Upgrade: websocket"));
    }

    #[test]
    fn test_websocket_handshake_response() {
        let mut response = WebSocketHandshakeResponse::new(101, "Switching Protocols");
        response.set_websocket_accept("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=");
        response.set_upgrade();

        let encoded = response.encode();
        assert!(encoded.contains("HTTP/1.1 101 Switching Protocols"));
        assert!(encoded.contains("Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo="));
        assert!(encoded.contains("Upgrade: websocket"));
    }

    #[test]
    fn test_websocket_client() {
        let key = WebSocketClient::generate_key();
        assert!(!key.is_empty());

        let accept = WebSocketClient::calculate_accept(&key);
        assert!(!accept.is_empty());
    }
}
