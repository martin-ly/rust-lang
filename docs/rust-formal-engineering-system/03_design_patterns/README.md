# 设计模式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [c09_design_pattern/](../../../crates/c09_design_pattern/)

[返回主索引](../00_master_index.md)

---

## Rust 设计模式概览

### 类型系统驱动的模式

```rust
// 类型状态模式（Type State Pattern）
struct Door<State> {
    _state: std::marker::PhantomData<State>,
}

struct Closed;
struct Open;

impl Door<Closed> {
    fn new() -> Self {
        Self { _state: std::marker::PhantomData }
    }

    fn open(self) -> Door<Open> {
        Door { _state: std::marker::PhantomData }
    }
}

impl Door<Open> {
    fn close(self) -> Door<Closed> {
        Door { _state: std::marker::PhantomData }
    }

    fn walk_through(&self) {
        println!("Walking through the door");
    }
}

// 使用：编译时防止无效状态转换
fn type_state_demo() {
    let door = Door::new();
    let door = door.open();
    door.walk_through();
    let _door = door.close();
    // _door.walk_through();  // 编译错误：Closed 状态没有 walk_through
}
```

### 构造器模式

```rust
// 消耗型构造器（Consuming Builder）
struct HttpRequest {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
}

struct HttpRequestBuilder {
    url: Option<String>,
    method: String,
    headers: Vec<(String, String)>,
}

impl HttpRequestBuilder {
    fn new() -> Self {
        Self {
            url: None,
            method: "GET".to_string(),
            headers: vec![],
        }
    }

    fn url(mut self, url: impl Into<String>) -> Self {
        self.url = Some(url.into());
        self
    }

    fn method(mut self, method: impl Into<String>) -> Self {
        self.method = method.into();
        self
    }

    fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    fn build(self) -> Result<HttpRequest, String> {
        Ok(HttpRequest {
            url: self.url.ok_or("URL is required")?,
            method: self.method,
            headers: self.headers,
        })
    }
}

fn builder_demo() -> Result<(), String> {
    let request = HttpRequestBuilder::new()
        .url("https://example.com")
        .method("POST")
        .header("Content-Type", "application/json")
        .build()?;

    Ok(())
}
```

### RAII 模式

```rust
// 资源获取即初始化
struct FileGuard {
    path: String,
}

impl FileGuard {
    fn new(path: &str) -> std::io::Result<Self> {
        // 打开文件
        println!("Opening file: {}", path);
        Ok(Self {
            path: path.to_string(),
        })
    }
}

impl Drop for FileGuard {
    fn drop(&mut self) {
        // 自动清理
        println!("Closing file: {}", self.path);
    }
}

// 使用：自动资源管理
fn raii_demo() {
    let _file = FileGuard::new("data.txt").unwrap();
    // 使用文件...
}  // 自动调用 drop，关闭文件
```

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c09_design_pattern | 设计模式实现集合 | [../../../crates/c09_design_pattern/](../../../crates/c09_design_pattern/) |
