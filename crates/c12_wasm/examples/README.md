# C12 WASM Examples

本目录包含了各种 WASM 示例代码，展示如何使用 Rust 开发 WebAssembly 应用。

## 📚 示例列表

### 基础示例

| 示例 | 描述 | 难度 | 运行环境 |
| --- | --- | --- | --- |
| [01_basic_add.rs](./01_basic_add.rs) | 基础数学运算，展示最简单的 WASM 函数导出 | ⭐ | Browser |
| [02_string_operations.rs](./02_string_operations.rs) | 字符串操作，展示 Rust 和 JS 之间的字符串传递 | ⭐ | Browser |
| [03_array_processing.rs](./03_array_processing.rs) | 数组处理，展示数组数据的传递和操作 | ⭐⭐ | Browser |
| [04_counter_class.rs](./04_counter_class.rs) | 有状态的类，展示如何导出 Rust 结构体 | ⭐⭐ | Browser |

### 高级示例

| 示例 | 描述 | 难度 | 运行环境 |
| --- | --- | --- | --- |
| [05_wasi_file_processor.rs](./05_wasi_file_processor.rs) | WASI 文件处理器，命令行工具示例 | ⭐⭐⭐ | WASI Runtime |
| [06_async_fetch.rs](./06_async_fetch.rs) | 异步 HTTP 请求，展示异步编程 | ⭐⭐⭐ | Browser |
| [07_design_patterns.rs](./07_design_patterns.rs) | 设计模式实现（工厂、建造者、单例等） | ⭐⭐⭐⭐ | Browser |

### Rust 1.92.0 特性示例 ⭐ NEW

| 示例 | 描述 | 难度 | 运行环境 |
| --- | --- | --- | --- |
| [rust_192_features_demo.rs](./rust_192_features_demo.rs) | Rust 1.92.0 特性演示 | ⭐⭐⭐ | Native/WASM |
| [12_rust_192_comprehensive_demo.rs](./12_rust_192_comprehensive_demo.rs) | Rust 1.92.0 综合应用示例 | ⭐⭐⭐⭐ | Native/WASM |

## 🚀 快速开始

### 浏览器环境 (Browser)

#### 方式1：使用 wasm-pack

```bash
# 1. 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 2. 构建项目
wasm-pack build --target web

# 3. 创建 HTML 文件并引入
# 查看 demo/ 目录中的示例
```

#### 方式2：直接编译

```bash
# 1. 添加 WASM 目标
rustup target add wasm32-unknown-unknown

# 2. 编译示例
cargo build --example 01_basic_add --target wasm32-unknown-unknown --release

# 3. 查看生成的 WASM 文件
ls -lh target/wasm32-unknown-unknown/release/examples/
```

### WASI 环境 (Command-line)

#### 使用 WasmEdge

```bash
# 1. 安装 WasmEdge
curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | bash

# 2. 添加 WASI 目标
rustup target add wasm32-wasi

# 3. 编译示例
cargo build --example 05_wasi_file_processor --target wasm32-wasi --release

# 4. 运行
wasmedge target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm count test.txt
```

#### 使用 Wasmtime

```bash
# 1. 安装 Wasmtime
curl https://wasmtime.dev/install.sh -sSf | bash

# 2. 编译（同上）
cargo build --example 05_wasi_file_processor --target wasm32-wasi --release

# 3. 运行
wasmtime target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm count test.txt
```

## 📝 详细说明

### 01_basic_add.rs - 基础加法运算

最简单的 WASM 示例，展示如何导出基本函数。

```bash
# 编译
cargo build --example 01_basic_add --target wasm32-unknown-unknown --release

# 在 JavaScript 中使用
# 见示例代码中的注释
```

**学习要点**：

- `#[wasm_bindgen]` 宏的使用
- 基础数据类型传递
- WASM 模块初始化

### 02_string_operations.rs - 字符串操作

展示字符串在 Rust 和 JavaScript 之间的传递。

```bash
# 使用 wasm-pack 构建
wasm-pack build --target web
```

**学习要点**：

- 字符串内存管理
- UTF-8 编码处理
- 字符串所有权

### 03_array_processing.rs - 数组处理

展示如何处理数组数据，包括各种常见的数组操作。

**学习要点**：

- 类型化数组 (TypedArray) 的使用
- 数组内存布局
- 零拷贝优化

### 04_counter_class.rs - 计数器类

展示如何导出有状态的 Rust 结构体到 JavaScript。

**学习要点**：

- 结构体导出
- 方法绑定
- getter/setter 使用
- 内存管理

### 05_wasi_file_processor.rs - WASI 文件处理器

完整的命令行工具示例，展示 WASI 应用开发。

```bash
# 编译
cargo build --example 05_wasi_file_processor --target wasm32-wasi --release

# 使用示例
wasmedge target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm count test.txt
wasmedge target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm search test.txt "hello"
```

**学习要点**：

- WASI API 使用
- 文件系统访问
- 命令行参数处理
- 错误处理

### 06_async_fetch.rs - 异步 HTTP 请求

展示如何在 WASM 中使用异步编程和 Fetch API。

**学习要点**：

- async/await 语法
- Promise 集成
- Fetch API 使用
- 错误处理

### 07_design_patterns.rs - 设计模式

展示常见设计模式在 WASM 中的实现。

**包含的模式**：

- 工厂模式 (Factory)
- 建造者模式 (Builder)
- 单例模式 (Singleton)
- 策略模式 (Strategy)
- 观察者模式 (Observer)

**学习要点**：

- 设计模式在 Rust 中的实现
- WASM 中的单例模式
- 回调函数处理
- 内存管理

## 🔧 开发工具

### 推荐的开发工具

1. **wasm-pack** - WASM 包管理工具

   ```bash
   curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
   ```

2. **WasmEdge** - 高性能 WASM 运行时

   ```bash
   curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | bash
   ```

3. **wasmtime** - 独立 WASM 运行时

   ```bash
   curl https://wasmtime.dev/install.sh -sSf | bash
   ```

4. **wasm-opt** - WASM 优化工具

   ```bash
   # 使用 wasm-opt 优化二进制大小
   wasm-opt -Oz -o output.wasm input.wasm
   ```

### 调试工具

1. **Chrome DevTools** - 浏览器调试
   - 打开 Chrome DevTools
   - 在 Sources 面板中可以看到 WASM 模块
   - 支持断点调试

2. **Console logging** - 日志输出

   ```rust
   use web_sys::console;
   console::log_1(&"Debug message".into());
   ```

## 📚 学习路径

1. **第1周：基础入门**
   - 完成 01-04 基础示例
   - 理解 wasm-bindgen 工作原理
   - 掌握基本的数据类型传递

2. **第2周：进阶学习**
   - 完成 05-06 高级示例
   - 学习 WASI 应用开发
   - 掌握异步编程

3. **第3周：实战应用**
   - 完成 07 设计模式示例
   - 创建自己的 WASM 项目
   - 性能优化实践

## 🐛 常见问题

### Q: 编译失败，提示找不到 wasm32 目标

```bash
# 解决方案：添加 WASM 目标
rustup target add wasm32-unknown-unknown
rustup target add wasm32-wasi
```

### Q: 二进制文件太大

```bash
# 解决方案：优化编译配置
# 1. 在 Cargo.toml 中设置 release profile
[profile.release]
opt-level = "z"
lto = true
codegen-units = 1
strip = true

# 2. 使用 wasm-opt 优化
wasm-opt -Oz -o optimized.wasm original.wasm
```

### Q: JavaScript 中无法调用 WASM 函数

```javascript
// 解决方案：确保正确初始化
import init, { add } from './pkg/c12_wasm.js';

// 必须先调用 init()
await init();

// 然后才能使用函数
const result = add(2, 3);
```

## 🤝 贡献

欢迎提交新的示例！请确保：

1. 包含详细的文档注释
2. 提供使用示例
3. 添加测试用例
4. 更新本 README

## 📖 更多资源

- [Rust and WebAssembly Book](https://rustwasm.github.io/docs/book/)
- [wasm-bindgen Guide](https://rustwasm.github.io/docs/wasm-bindgen/)
- [WASI Documentation](https://wasi.dev/)
- [WasmEdge Documentation](https://wasmedge.org/book/en/)

---

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ / Edition 2024
