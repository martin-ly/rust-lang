# 调试技术 (Debugging Techniques)

## 📋 目录

- [调试技术 (Debugging Techniques)](#调试技术-debugging-techniques)
  - [📋 目录](#-目录)
  - [核心命题](#核心命题)
  - [浏览器调试](#浏览器调试)
    - [Chrome DevTools 深度使用](#chrome-devtools-深度使用)
    - [Firefox Developer Tools](#firefox-developer-tools)
  - [命令行调试](#命令行调试)
    - [wasm-objdump 深度分析](#wasm-objdump-深度分析)
    - [wasm-interp 交互式调试](#wasm-interp-交互式调试)
  - [Printf 调试](#printf-调试)
    - [Emscripten printf](#emscripten-printf)
    - [Rust println! / eprintln](#rust-println--eprintln)
  - [内存调试](#内存调试)
    - [内存越界检测](#内存越界检测)
    - [内存泄漏检测](#内存泄漏检测)
  - [性能调试](#性能调试)
    - [瓶颈定位](#瓶颈定位)
    - [指令级性能分析](#指令级性能分析)
  - [常见问题调试](#常见问题调试)
    - [问题 1: "LinkError: Import not found"](#问题-1-linkerror-import-not-found)
    - [问题 2: "RuntimeError: unreachable"](#问题-2-runtimeerror-unreachable)
    - [问题 3: 内存错乱](#问题-3-内存错乱)
  - [远程调试](#远程调试)
    - [Chrome Remote Debugging](#chrome-remote-debugging)
  - [高级调试技术](#高级调试技术)
    - [时间旅行调试 (Time-Travel)](#时间旅行调试-time-travel)
    - [调试符号优化](#调试符号优化)
    - [自定义调试器](#自定义调试器)
  - [生产环境调试](#生产环境调试)
    - [错误报告](#错误报告)
    - [日志采集](#日志采集)
  - [批判性分析](#批判性分析)
    - [调试工具的局限](#调试工具的局限)
    - [成本-收益分析](#成本-收益分析)
  - [最佳实践](#最佳实践)
    - [调试构建 vs 发布构建](#调试构建-vs-发布构建)
    - [防御性编程](#防御性编程)
    - [日志分级](#日志分级)
  - [参考文献](#参考文献)
  - [相关文档](#相关文档)

## 核心命题

**调试复杂度定理**：
\[
T\_{\text{debug}} \propto \frac{\text{SystemComplexity} \times \text{Abstraction}}{\text{Observability}}
\]

**Wasm 调试挑战**：
\[
\text{Observability}_{\text{Wasm}} < \text{Observability}_{\text{Native}} \times 0.3
\]

**工具链影响**：
\[
\text{Debug}\_{\text{quality}} = f(\text{SourceMap}, \text{Symbols}, \text{Runtime})
\]

---

## 浏览器调试

### Chrome DevTools 深度使用

**Source Map 配置**：

```bash
# Emscripten
emcc -g4 --source-map-base=http://localhost:8000/ main.c -o main.html

# Rust
RUSTFLAGS="-C debuginfo=2" cargo build --target wasm32-unknown-unknown
wasm-bindgen --debug --keep-debug --out-dir pkg target/wasm32-unknown-unknown/debug/mylib.wasm
```

**断点调试技巧**：

1. **条件断点**：

   ```javascript
   // 在 DevTools 中设置条件
   // 仅当 x > 100 时暂停
   ```

2. **日志点 (Logpoints)**：

   ```javascript
   // 不暂停执行，仅打印
   console.log("x =", x, "y =", y)
   ```

3. **监视表达式 (Watch)**：

   ```javascript
   // 监视 Wasm 内存
   new Uint8Array(instance.exports.memory.buffer, 0, 100)
   ```

**内存检查器**：

```javascript
// 检查 Wasm 线性内存
function inspectWasmMemory(instance, offset, length) {
  const memory = new Uint8Array(instance.exports.memory.buffer)
  return Array.from(memory.slice(offset, offset + length))
    .map(b => b.toString(16).padStart(2, "0"))
    .join(" ")
}

// 使用
console.log(inspectWasmMemory(wasmInstance, 0x1000, 64))
// 输出: 00 01 02 03 04 05 06 07 ...
```

**调用栈分析**：

```javascript
// 捕获混合调用栈 (JS ↔ Wasm)
function captureStackTrace() {
  const err = new Error()
  const stack = err.stack.split("\n")

  stack.forEach(line => {
    if (line.includes(".wasm")) {
      console.log("[WASM]", line)
    } else {
      console.log("[JS]", line)
    }
  })
}
```

### Firefox Developer Tools

**优势**：

- 更好的 WAT 反汇编显示
- 支持编辑 WAT 并重新编译
- 更精确的性能分析

**使用技巧**：

```javascript
// 在 Firefox 中启用 Wasm 调试
about: config
devtools.debugger.features.wasm = true
```

---

## 命令行调试

### wasm-objdump 深度分析

**反汇编特定函数**：

```bash
# 查找函数索引
wasm-objdump -x module.wasm | grep -A2 "Function\[123\]"

# 反汇编该函数
wasm-objdump -d module.wasm --section=Code | sed -n '/func\[123\]/,/^$/p'
```

**分析导入导出**：

```bash
# 检查所有导入
wasm-objdump -x module.wasm | grep -A5 "Import\["

# 检查所有导出
wasm-objdump -x module.wasm | grep -A5 "Export\["

# 生成导入导出映射
wasm-objdump -x module.wasm | \
  awk '/Import\[/{print "IMPORT:", $0} /Export\[/{print "EXPORT:", $0}' > interface.txt
```

**内存布局检查**：

```bash
# 检查数据段
wasm-objdump -s -j Data module.wasm

# 检查自定义段
wasm-objdump -s -j name module.wasm
```

### wasm-interp 交互式调试

**单步执行**：

```bash
# 交互式解释器
wasm-interp module.wasm --run-all-exports --trace

# 输出示例
#   0: V:2 | call 5
#   1: V:3 | i32.const 10
#   2: V:4 | i32.const 20
#   3: V:5 | i32.add
#   4: V:4 | return
```

**断点模拟**：

```bash
# 在指定指令处停止
wasm-interp module.wasm --trace --stop-at-instr=100
```

---

## Printf 调试

### Emscripten printf

**基础用法**：

```c
#include <stdio.h>
#include <emscripten.h>

EMSCRIPTEN_KEEPALIVE
int compute(int x) {
    printf("[DEBUG] compute called with x=%d\n", x);

    int result = x * x;
    printf("[DEBUG] result=%d\n", result);

    return result;
}
```

**格式化复杂数据**：

```c
void dump_array(int* arr, size_t len) {
    printf("[DEBUG] Array[%zu]: [", len);
    for (size_t i = 0; i < len; i++) {
        printf("%d%s", arr[i], i < len-1 ? ", " : "");
    }
    printf("]\n");
}
```

### Rust println! / eprintln

**Console 输出**：

```rust
use web_sys::console;

#[wasm_bindgen]
pub fn debug_function(x: i32) -> i32 {
    console::log_1(&format!("[DEBUG] x = {}", x).into());

    let result = x * 2;
    console::log_1(&format!("[DEBUG] result = {}", result).into());

    result
}
```

**条件调试**：

```rust
#[cfg(debug_assertions)]
macro_rules! debug_log {
    ($($arg:tt)*) => {
        web_sys::console::log_1(&format!($($arg)*).into());
    };
}

#[cfg(not(debug_assertions))]
macro_rules! debug_log {
    ($($arg:tt)*) => {};
}

// 使用
debug_log!("Processing item: {:?}", item);
```

---

## 内存调试

### 内存越界检测

**AddressSanitizer (ASAN) for Wasm**：

```bash
# Emscripten 启用 ASAN
emcc -fsanitize=address -g main.c -o main.html

# 运行时检测
# 访问越界会触发错误报告
```

**手动边界检查**：

```rust
fn safe_read(memory: &[u8], offset: usize, len: usize) -> Result<&[u8], String> {
    if offset + len > memory.len() {
        return Err(format!(
            "Out of bounds: offset={}, len={}, memory_size={}",
            offset, len, memory.len()
        ));
    }
    Ok(&memory[offset..offset + len])
}
```

### 内存泄漏检测

**手动引用计数**：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

static ALLOCATION_COUNT: AtomicUsize = AtomicUsize::new(0);

#[wasm_bindgen]
pub fn allocate_buffer(size: usize) -> *mut u8 {
    ALLOCATION_COUNT.fetch_add(1, Ordering::SeqCst);

    let layout = Layout::from_size_align(size, 8).unwrap();
    unsafe { alloc(layout) }
}

#[wasm_bindgen]
pub fn free_buffer(ptr: *mut u8, size: usize) {
    ALLOCATION_COUNT.fetch_sub(1, Ordering::SeqCst);

    let layout = Layout::from_size_align(size, 8).unwrap();
    unsafe { dealloc(ptr, layout) }
}

#[wasm_bindgen]
pub fn get_allocation_count() -> usize {
    ALLOCATION_COUNT.load(Ordering::SeqCst)
}
```

**使用示例**：

```javascript
console.log("Allocations before:", wasmInstance.get_allocation_count())

const ptr = wasmInstance.allocate_buffer(1024)
console.log("Allocations after alloc:", wasmInstance.get_allocation_count())

wasmInstance.free_buffer(ptr, 1024)
console.log("Allocations after free:", wasmInstance.get_allocation_count())
```

---

## 性能调试

### 瓶颈定位

**JS + Wasm 性能标记**：

```javascript
// JS 端
performance.mark("js-start")
const input = prepareData()
performance.mark("js-end")

// Wasm 调用
performance.mark("wasm-start")
const result = wasmInstance.process(input)
performance.mark("wasm-end")

// 后处理
performance.mark("post-start")
displayResult(result)
performance.mark("post-end")

// 测量
performance.measure("js-prepare", "js-start", "js-end")
performance.measure("wasm-compute", "wasm-start", "wasm-end")
performance.measure("post-process", "post-start", "post-end")

// 分析
const entries = performance.getEntriesByType("measure")
entries.forEach(entry => {
  console.log(`${entry.name}: ${entry.duration.toFixed(2)}ms`)
})
```

**Wasm 内部计时**：

```rust
use std::time::Instant;

#[wasm_bindgen]
pub fn benchmark_function() {
    let start = Instant::now();

    // 执行操作
    expensive_computation();

    let elapsed = start.elapsed();
    web_sys::console::log_1(&format!(
        "Computation took: {}ms",
        elapsed.as_millis()
    ).into());
}
```

### 指令级性能分析

**统计指令执行次数**：

```bash
# 使用 wasm-interp 的 trace 功能
wasm-interp module.wasm --trace > trace.log

# 分析最频繁的指令
cat trace.log | awk '{print $NF}' | sort | uniq -c | sort -rn | head -20

# 示例输出：
#  45230 i32.add
#  32100 local.get
#  28900 i32.const
#  15200 i32.load
```

---

## 常见问题调试

### 问题 1: "LinkError: Import not found"

**诊断**：

```javascript
// 检查导入需求
WebAssembly.Module.imports(wasmModule).forEach(imp => {
  console.log(`Import: ${imp.module}.${imp.name} (${imp.kind})`)
})

// 检查提供的导入
Object.keys(imports).forEach(module => {
  Object.keys(imports[module]).forEach(name => {
    console.log(`Provided: ${module}.${name}`)
  })
})
```

**解决方案**：

```javascript
// 提供缺失的导入
const imports = {
  env: {
    // 补全缺失的函数
    missing_function: () => {
      console.log("stub")
    },
  },
}
```

### 问题 2: "RuntimeError: unreachable"

**定位**：

```bash
# 生成源映射
emcc -g4 --source-map-base=. main.c -o main.html

# 在浏览器中查看具体代码位置
```

**常见原因**：

- 整数除以零
- 未初始化的函数指针调用
- 数组越界（安全检查版本）
- 显式 `unreachable` 指令

**调试**：

```c
// 添加断言
#include <assert.h>

int divide(int a, int b) {
    assert(b != 0 && "Division by zero");
    return a / b;
}
```

### 问题 3: 内存错乱

**症状**：

- 读取到错误的值
- 随机崩溃
- 数据结构损坏

**诊断工具**：

```rust
// 内存哨兵 (Canary)
const CANARY: u32 = 0xDEADBEEF;

struct GuardedBuffer {
    canary_start: u32,
    data: Vec<u8>,
    canary_end: u32,
}

impl GuardedBuffer {
    fn new(size: usize) -> Self {
        Self {
            canary_start: CANARY,
            data: vec![0; size],
            canary_end: CANARY,
        }
    }

    fn check(&self) {
        assert_eq!(self.canary_start, CANARY, "Start canary corrupted!");
        assert_eq!(self.canary_end, CANARY, "End canary corrupted!");
    }
}
```

---

## 远程调试

### Chrome Remote Debugging

**配置**：

```bash
# 启动 Chrome 远程调试
chrome --remote-debugging-port=9222

# 连接到远程 Chrome
curl http://localhost:9222/json
```

**Puppeteer 自动化调试**：

```javascript
const puppeteer = require("puppeteer")

;(async () => {
  const browser = await puppeteer.launch({
    headless: false,
    devtools: true,
  })

  const page = await browser.newPage()

  // 捕获控制台输出
  page.on("console", msg => {
    console.log(`[PAGE] ${msg.text()}`)
  })

  // 捕获 Wasm 错误
  page.on("pageerror", error => {
    console.error(`[ERROR] ${error.message}`)
  })

  await page.goto("http://localhost:8000")

  // 等待 Wasm 加载
  await page.waitForFunction(() => window.wasmLoaded === true)

  // 执行测试
  const result = await page.evaluate(() => {
    return window.wasmModule.compute(42)
  })

  console.log("Result:", result)
})()
```

---

## 高级调试技术

### 时间旅行调试 (Time-Travel)

**rr (Record and Replay)**：

```bash
# 记录执行
rr record wasmtime module.wasm

# 回放调试
rr replay

# 在 gdb 中使用反向执行
(gdb) continue
(gdb) reverse-continue
(gdb) reverse-step
```

### 调试符号优化

**DWARF 符号**：

```bash
# 检查调试符号
llvm-dwarfdump module.wasm

# 剥离调试符号
wasm-strip module.wasm -o module_stripped.wasm

# 对比大小
ls -lh module.wasm module_stripped.wasm
```

### 自定义调试器

**基于 WABT 的调试器**：

```python
from wabt import *

class WasmDebugger:
    def __init__(self, wasm_file):
        self.module = Module.from_file(wasm_file)
        self.breakpoints = set()

    def set_breakpoint(self, func_idx, instr_offset):
        self.breakpoints.add((func_idx, instr_offset))

    def run_with_trace(self):
        # 使用 wasm-interp 运行并跟踪
        import subprocess
        result = subprocess.run(
            ['wasm-interp', '--trace', self.module.name],
            capture_output=True, text=True
        )

        for line in result.stdout.split('\n'):
            # 解析跟踪输出
            # 检查是否命中断点
            pass
```

---

## 生产环境调试

### 错误报告

**Sentry 集成**：

```javascript
import * as Sentry from "@sentry/browser"

Sentry.init({
  dsn: "YOUR_DSN",
  integrations: [new Sentry.BrowserTracing()],
  tracesSampleRate: 1.0,
})

// 捕获 Wasm 错误
try {
  wasmInstance.risky_function()
} catch (error) {
  Sentry.captureException(error, {
    tags: { component: "wasm" },
    extra: {
      memorySize: wasmInstance.exports.memory.buffer.byteLength,
      // 附加上下文
    },
  })
}
```

### 日志采集

**结构化日志**：

```rust
use serde_json::json;

#[wasm_bindgen]
pub fn log_event(event_type: &str, data: &JsValue) {
    let log_entry = json!({
        "timestamp": js_sys::Date::now(),
        "type": event_type,
        "data": data,
        "memory_used": get_memory_usage(),
    });

    web_sys::console::log_1(&log_entry.to_string().into());
}
```

---

## 批判性分析

### 调试工具的局限

**对比**：

| 功能     | Native C++ | Wasm (最佳情况) | 差距 |
| :--- | :--- | :--- | :--- |
| 断点调试 | ★★★★★      | ★★★☆☆           | -40% |
| 变量检查 | ★★★★★      | ★★☆☆☆           | -60% |
| 内存分析 | ★★★★★      | ★★☆☆☆           | -60% |
| 性能分析 | ★★★★★      | ★★★☆☆           | -40% |
| 调用栈   | ★★★★★      | ★★★★☆           | -20% |

**批判**：

> Wasm 的调试体验显著劣于原生代码。优化构建几乎无法调试，开发者被迫在"性能"与"可调试性"间二选一。

### 成本-收益分析

**调试时间统计**：

| 问题类型 | Native | Wasm   | 增加比例 |
| :--- | :--- | :--- | :--- |
| 简单 bug | 10 min | 25 min | +150%    |
| 内存问题 | 1 h    | 4 h    | +300%    |
| 性能问题 | 2 h    | 6 h    | +200%    |
| 并发问题 | 4 h    | 12 h   | +200%    |

**批判**：

> Wasm 的调试成本是原生代码的 2-3 倍。对于复杂项目，额外的调试时间可能抵消 Wasm 带来的其他收益。

---

## 最佳实践

### 调试构建 vs 发布构建

**分离策略**：

```bash
# 开发模式：最大可调试性
make debug
# → 生成 module_debug.wasm (带符号、未优化、Source Map)

# 发布模式：最大性能
make release
# → 生成 module_release.wasm (无符号、优化、压缩)
```

### 防御性编程

**断言与检查**：

```rust
#[inline(never)]  // 确保断言在调试中可见
pub fn process_buffer(data: &[u8]) {
    debug_assert!(!data.is_empty(), "Empty buffer");
    debug_assert!(data.len() <= MAX_SIZE, "Buffer too large");

    // 生产环境也保留关键检查
    if data.len() > MAX_SIZE {
        panic!("Buffer overflow detected");
    }
}
```

### 日志分级

```rust
pub enum LogLevel {
    Trace,   // 最详细
    Debug,   // 调试信息
    Info,    // 一般信息
    Warn,    // 警告
    Error,   // 错误
}

#[wasm_bindgen]
pub fn set_log_level(level: LogLevel) {
    // 运行时调整日志级别
}
```

---

## 参考文献

1. **[Chrome DevTools]** WebAssembly Debugging (<https://developer.chrome.com/docs/devtools/wasm/>)
2. **[WABT]** WebAssembly Binary Toolkit (<https://github.com/WebAssembly/wabt>)
3. **[rr]** Record and Replay Debugger (<https://rr-project.org/>)

---

## 相关文档

- **[09.1 开发工具链](09.1_Development_Toolchain.md)** - 调试工具详解
- **[09.2 测试策略](09.2_Testing_Strategies.md)** - 测试与调试配合
- **[03.5 性能分析](../03_Runtime_Systems/03.5_Performance_Analysis.md)** - 性能调试方法
