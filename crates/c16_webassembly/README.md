# WebAssembly 2.0 与 Rust 1.90 集成项目

## 项目概述

本项目展示了 Rust 1.90 的新特性如何与 WebAssembly 2.0 的最新功能深度集成，提供了一个完整的 WebAssembly 运行时实现，支持最新的语言特性和标准。项目包含2025年9月最新的WebAssembly开源库、工具链和应用案例。

## 🚀 主要特性

### Rust 1.90 新特性支持

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
├── src/                        # 源代码
│   ├── main.rs                 # 主程序入口
│   ├── types.rs                # 核心类型定义
│   ├── vm.rs                   # 虚拟机实现
│   ├── runtime.rs              # 运行时环境
│   ├── security.rs             # 安全模型
│   ├── tools.rs                # 工具函数
│   └── rust_189_features.rs    # Rust 1.90 特性集成
├── docs/                       # 详细文档
│   ├── 2025_september/         # 2025年9月最新开源库
│   ├── tools/                  # 开发工具文档
│   │   ├── security/           # 安全工具
│   │   └── optimization/       # 优化工具
│   ├── examples/               # 示例代码文档
│   │   ├── rust_190/           # Rust 1.90 示例
│   │   └── webassembly_20/     # WebAssembly 2.0 示例
│   ├── projects/               # 项目案例文档
│   │   ├── cloud_native/       # 云原生项目
│   │   ├── ai_inference/       # AI 推理项目
│   │   └── blockchain/         # 区块链项目
│   ├── rust_webassembly/       # Rust WebAssembly 技术视图
│   └── README.md               # 文档中心导航
├── Cargo.toml                  # 项目配置
├── README.md                   # 项目说明
└── 12_webassembly.md           # 完整集成指南
```

## 🛠️ 快速开始

### 环境要求

- Rust 1.90+
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

### 1. Rust 1.90 常量泛型推断

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

### 5. Rust 1.90 FFI 改进

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
# 测试 Rust 1.90 特性
cargo test rust_190_features

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

- `docs/2025_september/` - 2025年9月最新开源库和依赖库
- `docs/tools/security/` - WebAssembly 安全工具集
- `docs/tools/optimization/` - WebAssembly 优化工具集
- `docs/examples/rust_190/` - Rust 1.90 新特性示例
- `docs/examples/webassembly_20/` - WebAssembly 2.0 新特性示例
- `docs/projects/cloud_native/` - 云原生项目案例
- `docs/projects/ai_inference/` - AI 推理项目案例
- `docs/projects/blockchain/` - 区块链项目案例
- `docs/rust_webassembly/` - Rust WebAssembly 技术视图
- `docs/README.md` - 文档中心导航
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

### 1. 使用 Rust 1.90 新特性

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

**注意**：本项目展示了 Rust 1.90 和 WebAssembly 2.0 的最新特性集成，包含2025年9月最新的开源库和工具链。部分功能可能需要最新的工具链支持。请确保使用推荐的版本以获得最佳体验。

## 🆕 2025年9月更新内容

### 最新开源库和依赖库

- **wasmtime 37.0.0**: 支持WebAssembly 2.0的最新运行时
- **wasm-bindgen 0.2.103**: 增强的Rust-JavaScript互操作
- **wasm-pack 0.12+**: 改进的包管理工具
- **Yew 0.21+**: 基于Rust的前端框架
- **Seed 0.10+**: 轻量级前端框架

### 安全工具

- **Wasmati**: 静态漏洞扫描工具
- **Wasabi**: 动态分析框架
- **Twine**: 嵌入式可信运行时
- **wasm-mutate**: 二进制多样化引擎

### 新兴语言支持

- **MoonBit**: 专为WebAssembly优化的编程语言
- **凹语言**: 面向WebAssembly的中文编程语言

### 项目案例

- **云原生**: 容器化、微服务、服务网格
- **AI推理**: 机器学习模型推理、神经网络计算
- **区块链**: 智能合约、去中心化应用、跨链互操作
