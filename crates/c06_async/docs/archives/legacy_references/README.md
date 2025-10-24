# API参考 (References)

本目录包含C06异步编程模块的API参考文档和技术规范。

## 📚 文档列表

- **[api_reference.md](./api_reference.md)**  
  核心API详细参考文档

- **[utils_reference.md](./utils_reference.md)**  
  工具函数和辅助模块参考

- **[msrv_and_compatibility.md](./msrv_and_compatibility.md)**  
  最小支持Rust版本(MSRV)和兼容性信息

## 📖 快速查找

### 核心Trait

- `Future` - 异步计算抽象
- `Stream` - 异步迭代器
- `Sink` - 异步接收器

### 运行时API

- Tokio API参考
- async-std API参考
- Smol API参考

### 工具函数

- 超时控制
- 错误处理
- 测试辅助

## 🔗 外部参考

- [std::future](https://doc.rust-lang.org/std/future/)
- [futures crate](https://docs.rs/futures/)
- [tokio docs](https://docs.rs/tokio/)

**最后更新**: 2025-10-19
