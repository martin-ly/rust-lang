# 安装指南

## 系统要求

- **Rust 版本**：≥ 1.70
- **操作系统**：Windows、macOS、Linux
- **架构**：x86_64、ARM64

## 安装 Rust

如果还没有安装 Rust，请访问 [rustup.rs](https://rustup.rs/) 安装 Rust 工具链。

```bash
# 检查 Rust 版本
rustc --version
cargo --version
```

## 添加依赖

### 方法一：直接添加到 Cargo.toml

在项目的 `Cargo.toml` 文件中添加：

```toml
[dependencies]
c18_model = "0.1.0"
```

### 方法二：使用 cargo add

```bash
cargo add c18_model
```

### 方法三：从源码构建

```bash
git clone https://github.com/your-username/c18_model.git
cd c18_model
cargo build --release
```

## 验证安装

创建一个简单的测试文件来验证安装：

```rust
// main.rs
use c18_model::{MM1Queue, ModelConfig};

fn main() {
    // 测试排队论模型
    let queue = MM1Queue::new(1.0, 2.0);
    println!("利用率: {:.2}%", queue.utilization() * 100.0);
    
    // 测试配置管理
    let config = ModelConfig::default();
    println!("配置创建成功: {}", config.precision.default_precision);
    
    println!("c18_model 安装成功！");
}
```

运行测试：

```bash
cargo run
```

预期输出：

```text
利用率: 50.00%
配置创建成功: 0.000001
c18_model 安装成功！
```

## 可选依赖

如果需要特定的功能，可以启用相应的特性：

```toml
[dependencies]
c18_model = { version = "0.1.0", features = ["visualization", "benchmarks"] }
```

## 故障排除

### 常见问题

1. **编译错误**：确保 Rust 版本 ≥ 1.70
2. **依赖冲突**：检查 `Cargo.lock` 文件
3. **内存不足**：增加系统内存或使用 `--release` 模式

### 获取帮助

- 查看 [API 文档](api-reference/)
- 阅读 [使用指南](guides/)
- 查看 [示例代码](examples/)
- 提交 Issue

## 下一步

安装完成后，建议：

1. 阅读 [快速开始指南](quick-start.md)
2. 查看 [使用示例](examples.md)
3. 探索 [API 参考](api-reference/)
