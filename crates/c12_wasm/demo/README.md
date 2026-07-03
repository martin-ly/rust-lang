# C12 WASM 演示页面

本目录包含交互式 HTML 演示页面，展示 Rust WASM 的各种功能。

## 📚 演示页面列表

| 文件                       | 描述         | 功能数 |
| :--- | :--- | :--- |
| [index.html](index.html) | 综合示例页面 | 20+    |

## 🚀 快速开始

### 1. 构建 WASM 模块

```bash
# 在项目根目录运行
wasm-pack build --target web

# 这会生成 pkg/ 目录，包含编译后的 WASM 模块
```

### 2. 启动本地服务器

由于浏览器的 CORS 策略，需要通过 HTTP 服务器访问演示页面。

#### 方式 1: 使用 Python (推荐)

```bash
# Python 3
python -m http.server 8080

# Python 2
python -m SimpleHTTPServer 8080

# 然后访问: http://localhost:8080/demo/
```

#### 方式 2: 使用 Node.js

```bash
# 安装 http-server
npm install -g http-server

# 启动服务器
http-server -p 8080

# 访问: http://localhost:8080/demo/
```

#### 方式 3: 使用 Rust

```bash
# 安装 basic-http-server
cargo install basic-http-server

# 启动服务器
basic-http-server .

# 访问: http://localhost:4000/demo/
```

### 3. 访问演示页面

打开浏览器访问：

```text
http://localhost:8080/demo/index.html
```

## 📖 功能演示

### 1. 基础示例标签

- **数学运算**: 展示基本的加减乘运算
- **问候函数**: 字符串处理和格式化

### 2. 字符串操作标签

- **字符串反转**: 反转任意字符串
- **回文检测**: 检测字符串是否为回文
- **单词统计**: 统计文本中的单词数量

### 3. 数组处理标签

- **数组求和**: 计算数组元素总和
- **平均值**: 计算数组平均值
- **最大值**: 查找数组最大元素
- **过滤偶数**: 过滤并返回偶数
- **数组反转**: 反转数组顺序

### 4. 计数器类标签

- **增加/减少**: +1 和 -1 操作
- **批量增加**: +10 操作
- **重置**: 重置计数器到 0

### 5. 设计模式标签

- **工厂模式**: HTML/Markdown/Text 渲染器
- **建造者模式**: 配置对象构建
- **策略模式**: 不同排序算法比较

### 6. 性能对比标签

- **WASM vs JavaScript**: 直观对比性能差异

## 🎨 自定义演示

### 添加新的演示功能

1. 在 `src/lib.rs` 中添加新的 WASM 函数：

   ```rust
   #[wasm_bindgen]
   pub fn my_new_function(input: i32) -> i32 {
       input * 2
   }
   ```

2. 重新构建 WASM：

   ```bash
   wasm-pack build --target web
   ```

3. 在 `index.html` 中添加 UI 和调用代码：

   ```html
   <div class="demo-section">
     <h3>新功能</h3>
     <input type="number" id="new-input" value="10" />
     <button onclick="runNewFunction()">运行</button>
     <div id="new-result" class="result-box"></div>
   </div>

   <script>
     window.runNewFunction = function () {
       if (!wasmModule) return alert("WASM 未加载")
       const input = parseInt(document.getElementById("new-input").value)
       const result = wasmModule.my_new_function(input)
       showResult("new-result", `结果: ${result}`, "success")
     }
   </script>
   ```

## 🔧 开发技巧

### 1. 实时重新加载

使用支持实时重新加载的开发服务器：

```bash
# 安装 live-server
npm install -g live-server

# 启动
live-server --port=8080

# 文件修改后会自动刷新浏览器
```

### 2. 调试 WASM

在浏览器中使用开发者工具：

1. 打开 Chrome/Firefox 开发者工具 (F12)
2. 在 Sources/Debugger 面板中找到 WASM 模块
3. 可以设置断点和单步调试

### 3. 性能分析

使用浏览器的性能分析工具：

```javascript
// 在代码中添加性能标记
performance.mark("wasm-start")
const result = wasmModule.heavy_computation()
performance.mark("wasm-end")
performance.measure("wasm-duration", "wasm-start", "wasm-end")

// 查看结果
console.log(performance.getEntriesByName("wasm-duration"))
```

### 4. 错误处理

WASM 函数可能抛出错误，使用 try-catch 捕获：

```javascript
try {
  const result = wasmModule.risky_function()
  showResult("result", result, "success")
} catch (err) {
  showResult("result", `错误: ${err}`, "error")
}
```

## 📊 浏览器兼容性

### 完全支持的浏览器

- ✅ Chrome 57+ (推荐)
- ✅ Firefox 52+
- ✅ Safari 11+
- ✅ Edge 16+

### 检查浏览器支持

```javascript
if (typeof WebAssembly === "object") {
  console.log("浏览器支持 WebAssembly")
} else {
  alert("您的浏览器不支持 WebAssembly，请升级浏览器")
}
```

## 🐛 常见问题

### Q: 页面显示 "WASM 未加载"

**解决方案**：

1. 确保已运行 `wasm-pack build --target web`
2. 检查 `pkg/` 目录是否存在
3. 确保通过 HTTP 服务器访问页面（不是 file:// 协议）
4. 查看浏览器控制台的错误信息

### Q: CORS 错误

**解决方案**：
必须通过 HTTP 服务器访问，不能直接双击打开 HTML 文件。

### Q: 模块加载缓慢

**解决方案**：

1. 使用 release 模式构建（默认）
2. 优化 Cargo.toml 中的编译配置
3. 使用 `wasm-opt` 进一步优化

```bash
# 安装 wasm-opt
npm install -g wasm-opt

# 优化 WASM 文件
wasm-opt -Oz -o pkg/c12_wasm_bg_optimized.wasm pkg/c12_wasm_bg.wasm
```

### Q: 某些功能不工作

**解决方案**：

1. 检查浏览器控制台的错误信息
2. 确认相应的 Rust 函数已导出 (`#[wasm_bindgen]`)
3. 确认函数签名（参数类型、返回类型）匹配

## 🎓 学习资源

### 官方文档

- [wasm-bindgen Book](https://rustwasm.github.io/docs/wasm-bindgen/)
- [WebAssembly MDN](https://developer.mozilla.org/en-US/docs/WebAssembly)
- [Rust and WebAssembly](https://rustwasm.github.io/docs/book/)

### 示例项目

- [wasm-bindgen Examples](https://github.com/rustwasm/wasm-bindgen/tree/main/examples)
- [awesome-wasm](https://github.com/mbasso/awesome-wasm)

## 📝 下一步

1. **探索示例代码**: 查看 `src/` 目录中的 Rust 实现
2. **修改和实验**: 尝试修改代码并查看效果
3. **创建自己的功能**: 添加新的 WASM 函数和 UI
4. **性能优化**: 学习如何优化 WASM 性能
5. **生产部署**: 了解如何部署 WASM 应用到生产环境

## 🤝 贡献

欢迎提交新的演示示例！请确保：

1. 代码有详细注释
2. UI 美观易用
3. 包含错误处理
4. 更新本 README

---

**最后更新**: 2025-12-11
**适用版本**: Rust 1.96.1+ / Edition 2024
**wasm-bindgen版本**: 0.2.x
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
