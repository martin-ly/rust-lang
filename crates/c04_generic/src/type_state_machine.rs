//! # 类型状态机（Type-State Pattern）
//! 这是一种零运行时开销的设计模式，错误的状态转换会在编译期被拒绝。
//! runtime overhead design ，state conversion in is 。

/// HTTP 请求构建器 —— 类型状态机示例
/// HTTP builder —— type state machine example
/// 只有按正确顺序设置 method → url → body 后才能发送请求。
/// order method → url → body after 。
/// 未完成前置步骤时，后续方法不可用。
/// before step ，after method 。
pub struct HttpRequestBuilder<State> {
    method: Option<String>,
    url: Option<String>,
    body: Option<String>,
    _state: std::marker::PhantomData<State>,
}

/// 初始状态：尚未设置任何字段
/// initial state ：field
/// initial state：尚未Set任何field
pub struct Init;
/// 已设置 method
/// method
/// 已Set method
pub struct MethodSet;
/// 已设置 method + url
/// 已Set method + url
pub struct UrlSet;
/// 已设置 method + url + body（可发送）
/// 已Set method + url + body（可Send）
pub struct Ready;

impl Default for HttpRequestBuilder<Init> {
    fn default() -> Self {
        Self::new()
    }
}

impl HttpRequestBuilder<Init> {
    /// 创建新的请求构建器
    /// Creates新的请求构建器
    /// builder
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            body: None,
            _state: std::marker::PhantomData,
        }
    }

    pub fn method(self, m: impl Into<String>) -> HttpRequestBuilder<MethodSet> {
        HttpRequestBuilder {
            method: Some(m.into()),
            url: self.url,
            body: self.body,
            _state: std::marker::PhantomData,
        }
    }
}

impl HttpRequestBuilder<MethodSet> {
    pub fn url(self, u: impl Into<String>) -> HttpRequestBuilder<UrlSet> {
        HttpRequestBuilder {
            method: self.method,
            url: Some(u.into()),
            body: self.body,
            _state: std::marker::PhantomData,
        }
    }
}

impl HttpRequestBuilder<UrlSet> {
    /// Set请求volume，stateconversionas Ready
    pub fn body(self, b: impl Into<String>) -> HttpRequestBuilder<Ready> {
        HttpRequestBuilder {
            method: self.method,
            url: self.url,
            body: Some(b.into()),
            _state: std::marker::PhantomData,
        }
    }

    /// 不设置 body 直接发送（GET 请求等）
    /// body （GET etc. ）
    /// 不Set body 直接Send（GET 请求etc.）
    pub fn send(self) -> String {
        format!(
            "{} {} (no body)",
            self.method.unwrap_or_default(),
            self.url.unwrap_or_default()
        )
    }
}

impl HttpRequestBuilder<Ready> {
    /// 发送已构建的请求
    /// Sends已构建的请求
    pub fn send(self) -> String {
        format!(
            "{} {} with body: {}",
            self.method.unwrap_or_default(),
            self.url.unwrap_or_default(),
            self.body.unwrap_or_default()
        )
    }
}

/// 文件操作状态机 —— 防止未打开就读写
/// file operation state machine ——
pub struct FileHandle<State> {
    path: String,
    _state: std::marker::PhantomData<State>,
}

pub struct Closed;
pub struct Open;

impl FileHandle<Closed> {
    pub fn new(path: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            _state: std::marker::PhantomData,
        }
    }

    pub fn open(self) -> FileHandle<Open> {
        FileHandle {
            path: self.path,
            _state: std::marker::PhantomData,
        }
    }
}

impl FileHandle<Open> {
    pub fn read(&self) -> String {
        format!("Reading from {}", self.path)
    }

    pub fn write(&mut self, _data: &str) -> String {
        format!("Writing to {}", self.path)
    }

    pub fn close(self) -> FileHandle<Closed> {
        FileHandle {
            path: self.path,
            _state: std::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_http_request_builder() {
        let response = HttpRequestBuilder::new()
            .method("POST")
            .url("https://api.example.com/users")
            .body(r#"{"name":"alice"}"#)
            .send();

        assert!(response.contains("POST"));
        assert!(response.contains("api.example.com"));
        assert!(response.contains("alice"));
    }

    #[test]
    fn test_http_get_without_body() {
        let response = HttpRequestBuilder::new()
            .method("GET")
            .url("https://api.example.com/users")
            .send();

        assert!(response.contains("GET"));
        assert!(response.contains("no body"));
    }

    #[test]
    fn test_file_state_machine() {
        let file = FileHandle::new("data.txt");
        let mut open_file = file.open();
        assert_eq!(open_file.read(), "Reading from data.txt");
        assert_eq!(open_file.write("hello"), "Writing to data.txt");
        let _closed = open_file.close();
        // _closed 不能调用 read() —— 编译期保证
    }
}
