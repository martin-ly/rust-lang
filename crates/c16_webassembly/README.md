# WebAssembly 2.0 与 Rust 1.89 集成项目

## 项目概述

本项目展示了 Rust 1.89 的新特性如何与 WebAssembly 2.0 的最新功能深度集成，提供了一个完整的 WebAssembly 运行时实现，支持最新的语言特性和标准。

## 🚀 主要特性

### Rust 1.89 新特性支持

- ✅ **常量泛型推断**：使用 `_` 让编译器自动推断常量泛型参数
- ✅ **生命周期语法检查**：改进的生命周期语法检查和错误提示
- ✅ **FFI 改进**：支持 `i128` 和 `u128` 类型在 `extern "C"` 函数中使用
- ✅ **跨平台文档测试**：支持针对特定平台的文档测试
- ✅ **API 稳定化**：`Result::flatten` 和文件锁相关 API

### WebAssembly 2.0 新特性支持

- ✅ **批量内存操作**：支持高效的内存复制和填充操作
- ✅ **尾调用优化**：减少递归函数的调用栈深度
- ✅ **宿主绑定**：直接操作 JavaScript/DOM 对象
- ✅ **接口类型**：支持更丰富的类型系统（字符串、记录、变体等）
- ✅ **SIMD 操作**：支持 128 位向量操作
- ✅ **ECMAScript 模块集成**：通过 ESM 导入方式加载 Wasm 模块

## 📁 项目结构

```text
c16_webassembly/
├── src/
│   ├── main.rs                 # 主程序入口
│   ├── types.rs                # 核心类型定义
│   ├── vm.rs                   # 虚拟机实现
│   ├── runtime.rs              # 运行时环境
│   ├── security.rs             # 安全模型
│   ├── tools.rs                # 工具函数
│   └── rust_189_features.rs    # Rust 1.89 特性集成
├── docs/                       # 详细文档
├── Cargo.toml                  # 项目配置
└── README.md                   # 项目说明
```

## 🛠️ 快速开始

### 环境要求

- Rust 1.89+
- wasm-pack 0.12+
- Node.js 16+ (用于 WebAssembly 测试)

### 安装依赖

```bash
# 安装 Rust 工具链
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 安装项目依赖
cargo build
```

### 运行示例

```bash
# 运行主程序
cargo run

# 运行测试
cargo test

# 构建 WebAssembly 模块
wasm-pack build --target web

# 运行 WebAssembly 测试
wasm-pack test --headless --firefox
```

## 📚 核心功能演示

### 1. Rust 1.89 常量泛型推断

```rust
// 使用下划线让编译器自动推断常量泛型参数
pub fn create_wasm_array<const LEN: usize>() -> [Value; LEN] {
    [Value::I32(0); _] // 编译器自动推断 LEN
}

// 创建不同大小的数组
let array_5: WasmArrayBuilder<5> = WasmArrayBuilder::new();
let array_10: WasmArrayBuilder<10> = WasmArrayBuilder::new();
```

### 2. WebAssembly 2.0 批量内存操作

```rust
let mut memory_manager = BulkMemoryManager::new(1024);

// 执行批量内存复制
memory_manager.bulk_copy(0, 100, 50)?;

// 执行批量内存填充
memory_manager.bulk_fill(200, 0xFF, 25)?;
```

### 3. WebAssembly 2.0 尾调用优化

```rust
let mut optimizer = TailCallOptimizer::new();

// 执行尾调用，减少调用栈深度
let args = vec![Value::I32(42), Value::I64(123)];
let result = optimizer.execute_tail_call(0, args)?;
```

### 4. WebAssembly 2.0 宿主绑定

```rust
let mut binding_manager = HostBindingManager::new();

// 注册 JavaScript 函数绑定
binding_manager.register_binding(
    "console.log".to_string(),
    HostBindingType::JavaScriptFunction,
    "console".to_string(),
);

// 调用 JavaScript 函数
let args = vec![Value::string("Hello from WebAssembly!".to_string())];
let result = binding_manager.call_javascript_function("console.log", args)?;
```

### 5. Rust 1.89 FFI 改进

```rust
// 128位整数类型现在可以在 extern "C" 函数中安全使用
extern "C" {
    fn wasm_i128_operation(value: i128) -> i128;
    fn wasm_u128_operation(value: u128) -> u128;
}

// 在 WebAssembly 中的使用
pub unsafe fn call_128bit_operations() -> (i128, u128) {
    let i128_result = wasm_i128_operation(123456789012345678901234567890i128);
    let u128_result = wasm_u128_operation(987654321098765432109876543210u128);
    (i128_result, u128_result)
}
```

## 🧪 测试

### 运行所有测试

```bash
cargo test
```

### 运行特定测试

```bash
# 测试 Rust 1.89 特性
cargo test rust_189_features

# 测试 WebAssembly 2.0 功能
cargo test wasm_2_0

# 测试集成功能
cargo test integration
```

### 性能基准测试

```bash
cargo bench --features bench
```

## 📖 文档

详细的文档位于 `docs/` 目录中：

- `rust_webassembly/view01.md` - Rust 1.89 特性详解
- `rust_webassembly/view02.md` - WebAssembly 2.0 新特性
- `rust_webassembly/view03.md` - 集成示例和最佳实践
- `12_webassembly.md` - 完整的集成指南

## 🔧 开发工具

### 代码格式化

```bash
cargo fmt
```

### 代码检查

```bash
cargo clippy -- -D warnings
```

### 文档生成

```bash
cargo doc --open
```

## 🌟 最佳实践

### 1. 使用 Rust 1.89 新特性

- 利用常量泛型推断简化数组创建
- 使用生命周期语法检查提高代码质量
- 在 FFI 中安全使用 128 位整数类型

### 2. WebAssembly 2.0 优化

- 使用批量内存操作提升性能
- 利用尾调用优化减少栈深度
- 通过宿主绑定简化 JavaScript 集成

### 3. 错误处理

- 使用 `thiserror` 提供详细的错误信息
- 实现完整的错误链和上下文
- 提供清晰的错误恢复策略

## 🤝 贡献

欢迎贡献代码！请遵循以下步骤：

1. Fork 项目
2. 创建特性分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 创建 Pull Request

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双许可证。详情请参见 [LICENSE](LICENSE) 文件。

## 🙏 致谢

- Rust 团队提供的优秀语言特性
- WebAssembly 社区的标准制定工作
- 所有贡献者的努力和反馈

## 📞 联系方式

如有问题或建议，请通过以下方式联系：

- 创建 [Issue](https://github.com/rust-lang/webassembly/issues)
- 发送邮件至项目维护者
- 参与社区讨论

---

**注意**：本项目展示了 Rust 1.89 和 WebAssembly 2.0 的最新特性集成，部分功能可能需要最新的工具链支持。请确保使用推荐的版本以获得最佳体验。
