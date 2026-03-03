//! 类型状态模式
//!
//! 编译时状态机验证

use std::marker::PhantomData;

// ============================================
// 基础类型状态
// ============================================

/// 状态标记
pub struct Uninitialized;
pub struct Initialized;
pub struct Running;
pub struct Stopped;

/// 类型状态状态机：Connection<State>
pub struct Connection<State> {
    url: String,
    state: PhantomData<State>,
}

impl Connection<Uninitialized> {
    pub fn new(url: String) -> Self {
        Self { url, state: PhantomData }
    }
    
    pub fn init(self) -> Result<Connection<Initialized>, String> {
        if self.url.starts_with("http") {
            Ok(Connection {
                url: self.url,
                state: PhantomData,
            })
        } else {
            Err("Invalid URL scheme".to_string())
        }
    }
}

impl Connection<Initialized> {
    pub fn connect(self) -> Connection<Running> {
        println!("Connecting to {}", self.url);
        Connection {
            url: self.url,
            state: PhantomData,
        }
    }
}

impl Connection<Running> {
    pub fn request(&self, path: &str) -> String {
        format!("GET {}{}", self.url, path)
    }
    
    pub fn disconnect(self) -> Connection<Stopped> {
        println!("Disconnected from {}", self.url);
        Connection {
            url: self.url,
            state: PhantomData,
        }
    }
}

impl Connection<Stopped> {
    pub fn restart(self) -> Connection<Initialized> {
        Connection {
            url: self.url,
            state: PhantomData,
        }
    }
}

// ============================================
// 构建者模式
// ============================================

pub struct Incomplete;
pub struct Complete;

pub struct ConfigBuilder<State> {
    host: Option<String>,
    port: Option<u16>,
    state: PhantomData<State>,
}

impl ConfigBuilder<Incomplete> {
    pub fn new() -> Self {
        Self {
            host: None,
            port: None,
            state: PhantomData,
        }
    }
    
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    pub fn build(self) -> Result<ConfigBuilder<Complete>, String> {
        if self.host.is_none() {
            return Err("Host is required".to_string());
        }
        
        Ok(ConfigBuilder {
            host: self.host,
            port: self.port.or(Some(8080)),
            state: PhantomData,
        })
    }
}

impl ConfigBuilder<Complete> {
    pub fn host(&self) -> &str {
        self.host.as_ref().unwrap()
    }
    
    pub fn port(&self) -> u16 {
        self.port.unwrap()
    }
}

// ============================================
// 资源生命周期管理
// ============================================

pub struct Open;
pub struct Closed;

pub struct FileHandle<State> {
    name: String,
    _state: PhantomData<State>,
}

impl FileHandle<Closed> {
    pub fn open(name: impl Into<String>) -> FileHandle<Open> {
        FileHandle {
            name: name.into(),
            _state: PhantomData,
        }
    }
}

impl FileHandle<Open> {
    pub fn read(&self) -> String {
        format!("Contents of {}", self.name)
    }
    
    pub fn close(self) -> FileHandle<Closed> {
        FileHandle {
            name: self.name,
            _state: PhantomData,
        }
    }
}

// 禁止重新关闭
impl FileHandle<Closed> {
    pub fn cannot_read(&self) {
        println!("Cannot read from closed file: {}", self.name);
    }
}

// ============================================
// 权限类型系统
// ============================================

pub struct ReadOnly;
pub struct ReadWrite;
pub struct Admin;

pub struct User<Permission> {
    name: String,
    _perm: PhantomData<Permission>,
}

impl User<ReadOnly> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            _perm: PhantomData,
        }
    }
    
    pub fn view(&self, doc: &str) {
        println!("{} is viewing: {}", self.name, doc);
    }
}

impl User<ReadWrite> {
    pub fn promote(user: User<ReadOnly>) -> Self {
        Self {
            name: user.name,
            _perm: PhantomData,
        }
    }
    
    pub fn edit(&self, doc: &str) {
        println!("{} is editing: {}", self.name, doc);
    }
}

impl User<Admin> {
    pub fn promote_rw(user: User<ReadWrite>) -> Self {
        Self {
            name: user.name,
            _perm: PhantomData,
        }
    }
    
    pub fn delete(&self, doc: &str) {
        println!("{} is deleting: {}", self.name, doc);
    }
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_connection_lifecycle() {
        let conn = Connection::new("https://example.com".to_string());
        let initialized = conn.init().unwrap();
        let running = initialized.connect();
        let response = running.request("/api");
        assert_eq!(response, "GET https://example.com/api");
        let stopped = running.disconnect();
        let _ = stopped.restart();
    }
    
    #[test]
    fn test_config_builder() {
        let config = ConfigBuilder::new()
            .host("localhost")
            .port(3000)
            .build()
            .unwrap();
        
        assert_eq!(config.host(), "localhost");
        assert_eq!(config.port(), 3000);
    }
    
    #[test]
    fn test_file_handle() {
        let file = FileHandle::open("test.txt");
        let content = file.read();
        assert_eq!(content, "Contents of test.txt");
        let closed = file.close();
        closed.cannot_read();
    }
    
    #[test]
    fn test_permission_system() {
        let user = User::<ReadOnly>::new("Alice");
        user.view("document.txt");
        
        let rw_user = User::<ReadWrite>::promote(user);
        rw_user.edit("document.txt");
        
        let admin = User::<Admin>::promote_rw(rw_user);
        admin.delete("document.txt");
    }
}
