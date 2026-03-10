# C12 WASM 快速开始指南

> 5 分钟上手 Rust WebAssembly 开发

## 🚀 快速开始（3 步）

### 1. 环境设置

运行自动设置脚本：

**Linux/macOS:**

```bash
chmod +x scripts/setup.sh
./scripts/setup.sh
```

**Windows:**

```cmd
scripts\setup.bat
```

脚本会自动：

- ✅ 检查 Rust 安装
- ✅ 安装 WASM 目标
- ✅ 安装 wasm-pack
- ✅ 安装开发工具
- ✅ 运行测试验证

### 2. 构建项目

```bash
# 构建库
cargo build --lib

# 构建 WASM 模块（用于浏览器）
wasm-pack build --target web
```

### 3. 运行演示

```bash
# 启动 HTTP 服务器
python -m http.server 8080

# 访问演示页面
# 打开浏览器: http://localhost:8080/demo/
```

就这么简单！🎉

---

## 📖 5 分钟教程

### 第 1 步：编写第一个 WASM 函数

创建文件 `src/my_first.rs`:

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn hello(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

### 第 2 步：构建

```bash
wasm-pack build --target web
```

### 第 3 步：在 JavaScript 中使用

```javascript
import init, { hello } from "./pkg/c12_wasm.js"

async function run() {
  await init()
  const greeting = hello("WASM")
  console.log(greeting) // "Hello, WASM!"
}

run()
```

### 第 4 步：在 HTML 中使用

```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="UTF-8" />
    <title>My First WASM</title>
  </head>
  <body>
    <h1>My First WASM App</h1>
    <input type="text" id="name" value="World" />
    <button onclick="greet()">Greet</button>
    <p id="result"></p>

    <script type="module">
      import init, { hello } from "./pkg/c12_wasm.js"

      let wasm

      async function initWasm() {
        wasm = await init()
      }

      window.greet = function () {
        const name = document.getElementById("name").value
        const greeting = wasm.hello(name)
        document.getElementById("result").textContent = greeting
      }

      initWasm()
    </script>
  </body>
</html>
```

完成！🎊

---

## 🎯 常用命令速查

### 开发

```bash
# 检查代码
cargo check --lib

# 格式化代码
cargo fmt

# 代码检查
cargo clippy

# 构建
cargo build --lib
```

### 测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_add

# 显示测试输出
cargo test -- --nocapture

# WASI 测试
cargo test --target wasm32-wasi
```

### WASM 构建

```bash
# 浏览器目标
wasm-pack build --target web

# Node.js 目标
wasm-pack build --target nodejs

# 打包器目标（Webpack 等）
wasm-pack build --target bundler
```

### 性能测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench array_processing
```

---

## 📂 项目结构速览

```text
c12_wasm/
├── src/                    # 源代码
│   ├── lib.rs             # 主库
│   ├── ecosystem_examples.rs  # 生态库示例
│   ├── wasi_examples.rs   # WASI 示例
│   └── wasmedge_examples.rs   # WasmEdge 示例
│
├── examples/              # 可运行示例
│   ├── 01_basic_add.rs
│   ├── 02_string_operations.rs
│   └── ...
│
├── tests/                 # 测试
│   ├── basic_tests.rs
│   ├── wasi_tests.rs
│   └── ...
│
├── benches/              # 性能基准测试
│   ├── array_processing_bench.rs
│   └── ...
│
├── demo/                 # 演示页面
│   └── index.html
│
├── docs/                 # 文档
│   ├── tier_01_foundations/
│   ├── tier_02_guides/
│   ├── tier_03_references/
│   └── tier_04_advanced/
│
└── scripts/              # 工具脚本
    ├── setup.sh
    ├── setup.bat
    └── build-all.sh
```

---

## 🎓 学习路径

### Week 1: 基础（2-4 小时）

1. 阅读 [项目概览](./docs/tier_01_foundations/01_项目概览.md)
2. 运行示例 `examples/01_basic_add.rs`
3. 查看演示页面 `demo/index.html`

### Week 2: 实践（10-20 小时）

1. 学习 [Rust 编译 WASM](./docs/tier_02_guides/02_rust_编译_wasm.md)
2. 完成 `examples/02_string_operations.rs`
3. 实践 JavaScript 互操作

### Week 3-4: 进阶（20-30 小时）

1. 学习 [性能优化](./docs/tier_02_guides/04_性能优化指南.md)
2. 研究设计模式 `examples/07_design_patterns.rs`
3. 学习 WASI 应用开发

### Week 5+: 高级

1. 深入 [WasmEdge](./docs/tier_04_advanced/05_wasmedge_与新技术深入.md)
2. 创建自己的项目
3. 性能优化实践

---

## 💡 快速技巧

### 技巧 1: 减小 WASM 大小

在 `Cargo.toml` 中：

```toml
[profile.release]
opt-level = "z"      # 优化大小
lto = true           # 链接时优化
codegen-units = 1    # 更好的优化
strip = true         # 去除调试符号
```

### 技巧 2: 调试 WASM

```rust
use web_sys::console;

#[wasm_bindgen]
pub fn debug_function() {
    console::log_1(&"Debug message".into());
}
```

### 技巧 3: 错误处理

```rust
#[wasm_bindgen]
pub fn safe_function(x: i32) -> Result<i32, JsValue> {
    if x < 0 {
        Err(JsValue::from_str("x must be positive"))
    } else {
        Ok(x * 2)
    }
}
```

### 技巧 4: 性能优化

```rust
// ✅ 好：使用引用
#[wasm_bindgen]
pub fn process(data: &[i32]) -> Vec<i32> {
    data.iter().filter(|&&x| x > 0).copied().collect()
}

// ❌ 不好：不必要的克隆
#[wasm_bindgen]
pub fn process_bad(data: Vec<i32>) -> Vec<i32> {
    data.clone().into_iter().filter(|&x| x > 0).collect()
}
```

---

## 🐛 常见问题

### Q: "WASM 未加载" 错误？

**A**: 确保：

1. 已运行 `wasm-pack build --target web`
2. 通过 HTTP 服务器访问（不是 file://）
3. 检查浏览器控制台的错误信息

### Q: 编译很慢？

**A**: 首次编译需要下载依赖，后续会快很多。使用 `cargo check` 进行快速检查。

### Q: 如何查看 WASM 大小？

**A**:

```bash
ls -lh pkg/*.wasm
# 或
wasm-pack build --target web
du -h pkg/c12_wasm_bg.wasm
```

### Q: 性能不如预期？

**A**:

1. 使用 release 模式构建
2. 检查是否有不必要的数据复制
3. 使用性能分析工具 `cargo bench`

---

## 📚 更多资源

### 文档

- 📖 [完整文档](./docs/README.md)
- 📝 [API 参考](./docs/tier_03_references/01_api_参考.md)
- 🎯 [最佳实践](./docs/tier_03_references/03_最佳实践.md)

### 示例

- 💻 [示例代码](./examples/README.md)
- 🌐 [演示页面](./demo/README.md)
- 🧪 [测试代码](./tests/README.md)

### 工具

- 🛠️ [贡献指南](./CONTRIBUTING.md)
- 📋 [更新日志](./CHANGELOG.md)
- 📊 [项目状态](./PROJECT_STATUS.md)

---

## 🤝 获取帮助

1. **查看文档**: 先查看[常见问题](./docs/tier_01_foundations/04_常见问题.md)
2. **搜索 Issues**: 在 GitHub 上搜索类似问题
3. **提问**: 在 GitHub Discussions 中提问
4. **贡献**: 查看[贡献指南](./CONTRIBUTING.md)

---

## 🎉 开始你的 WASM 之旅

选择最适合你的方式开始：

- 🚀 **快速体验**: 直接打开 `demo/index.html`
- 📖 **系统学习**: 从 [Tier 1 文档](./docs/tier_01_foundations/README.md) 开始
- 💻 **动手实践**: 运行 `examples/` 中的示例
- 🧪 **深入研究**: 查看 `tests/` 和 `benches/`

**祝你编码愉快！** 🦀✨

---

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ / Edition 2024
