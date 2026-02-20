# C12 WASM - 测试策略完整指南

> **文档类型**: 工程实践 - 测试策略
> **文档定位**: WASM 应用的完整测试策略和最佳实践
> **项目状态**: ✅ 完整完成
> **相关文档**: [开发工具链](./09.1_Development_Toolchain.md) | [调试技术](./09.3_Debugging_Techniques.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - 测试策略完整指南](#c12-wasm---测试策略完整指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🧪 单元测试](#-单元测试)
    - [Rust + wasm-bindgen-test](#rust--wasm-bindgen-test)
    - [C++ + Google Test](#c--google-test)
    - [AssemblyScript + as-pect](#assemblyscript--as-pect)
  - [🔗 集成测试](#-集成测试)
    - [JavaScript/TypeScript 集成](#javascripttypescript-集成)
    - [跨运行时测试](#跨运行时测试)
  - [🌐 端到端测试](#-端到端测试)
    - [Playwright 自动化测试](#playwright-自动化测试)
    - [跨浏览器测试](#跨浏览器测试)
  - [⚡ 性能测试](#-性能测试)
    - [基准测试](#基准测试)
    - [内存性能测试](#内存性能测试)
  - [🔍 模糊测试](#-模糊测试)
    - [cargo-fuzz](#cargo-fuzz)
    - [差异测试](#差异测试)
  - [🔄 回归测试](#-回归测试)
    - [快照测试](#快照测试)
    - [金标准测试](#金标准测试)
  - [📊 属性测试](#-属性测试)
  - [🎭 测试隔离与 Mock](#-测试隔离与-mock)
  - [🚀 持续集成测试](#-持续集成测试)
  - [📁 测试数据管理](#-测试数据管理)
  - [🎯 最佳实践](#-最佳实践)
    - [测试金字塔](#测试金字塔)
    - [测试先行 (TDD)](#测试先行-tdd)
    - [测试命名约定](#测试命名约定)
    - [测试隔离](#测试隔离)
  - [📚 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [测试工具](#测试工具)
    - [相关文档](#相关文档)

---

## 🎯 概述

本文档提供 WASM 应用的完整测试策略，涵盖单元测试、集成测试、性能测试等各个层面。

**测试策略金字塔**:

```text
       /\
      /E2E\         10% (慢、脆弱、昂贵)
     /------\
    /整合测试 \      20% (中速、较稳定)
   /----------\
  /  单元测试   \    70% (快、稳定、廉价)
 /--------------\
```

**核心原则**:

| 原则     | 说明                 | 价值         |
| :--- | :--- | :--- || 早测试   | 开发过程中持续测试   | 及早发现问题 |
| 自动化   | 尽可能自动化测试流程 | 提高效率     |
| 快速反馈 | 单元测试应秒级完成   | 快速迭代     |
| 真实环境 | 测试接近生产环境     | 发现实际问题 |
| 全面覆盖 | 覆盖边界和异常情况   | 提高质量     |

---

## 🧪 单元测试

### Rust + wasm-bindgen-test

**测试框架配置**:

```rust
// src/lib.rs
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}
```

**测试文件**:

```rust
// tests/web.rs
#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    // 配置在浏览器中运行
    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
        assert_eq!(add(0, 0), 0);
    }

    #[wasm_bindgen_test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(10), 55);
    }

    #[wasm_bindgen_test]
    async fn test_async_operation() {
        let result = async_fetch_data().await;
        assert!(result.is_ok());
    }
}
```

**运行测试**:

```bash
# 在 Firefox 中测试
wasm-pack test --headless --firefox

# 在 Chrome 中测试
wasm-pack test --headless --chrome

# 在 Node.js 中测试
wasm-pack test --node

# 测试特定模式
wasm-pack test --headless --firefox -- --test "test_add"

# 显示测试输出
wasm-pack test --headless --firefox -- --nocapture
```

**Cargo.toml 配置**:

```toml
[dev-dependencies]
wasm-bindgen-test = "0.3"

[lib]
crate-type = ["cdylib", "rlib"]

[profile.test]
opt-level = 0
```

**测试覆盖率**:

```bash
# 安装 tarpaulin
cargo install cargo-tarpaulin

# 生成 HTML 覆盖率报告
cargo tarpaulin --target wasm32-wasi --out Html --output-dir coverage

# 查看报告
open coverage/index.html
```

---

### C++ + Google Test

**测试代码**:

```cpp
// test.cpp
#include <gtest/gtest.h>
#include <emscripten.h>

extern "C" {
    int calculate(int a, int b);
    const char* process_string(const char* input);
}

TEST(CalculateTest, BasicOperation) {
    EXPECT_EQ(calculate(2, 3), 5);
    EXPECT_EQ(calculate(-1, 1), 0);
}

TEST(CalculateTest, EdgeCases) {
    EXPECT_EQ(calculate(0, 0), 0);
    EXPECT_EQ(calculate(INT_MAX, 0), INT_MAX);
}

TEST(StringTest, Processing) {
    const char* result = process_string("Hello");
    EXPECT_STREQ(result, "HELLO");
}

int main(int argc, char **argv) {
    testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
```

**编译和运行**:

```bash
# 编译为 Wasm
emcc test.cpp \
  -s WASM=1 \
  -s NODERAWFS=1 \
  -lgtest \
  -lgtest_main \
  -pthread \
  -o test.js

# 运行测试
node test.js
```

**CMake 集成**:

```cmake
# CMakeLists.txt
enable_testing()

add_executable(tests test.cpp)
target_link_libraries(tests gtest gtest_main)

add_test(NAME WasmTests COMMAND tests)
```

---

### AssemblyScript + as-pect

**测试代码**:

```typescript
// assembly/__tests__/example.spec.ts
import { fibonacci, isPalindrome } from "../index"

describe("Math Functions", () => {
  it("should calculate fibonacci correctly", () => {
    expect(fibonacci(0)).toBe(0)
    expect(fibonacci(1)).toBe(1)
    expect(fibonacci(10)).toBe(55)
  })

  it("should handle large numbers", () => {
    expect(fibonacci(20)).toBe(6765)
  })
})

describe("String Functions", () => {
  it("should detect palindromes", () => {
    expect(isPalindrome("racecar")).toBe(true)
    expect(isPalindrome("hello")).toBe(false)
  })

  it("should be case insensitive", () => {
    expect(isPalindrome("RaceCar")).toBe(true)
  })
})
```

**运行测试**:

```bash
# 运行所有测试
npm test

# 运行特定测试
npm test -- --filter "fibonacci"

# 生成覆盖率报告
npm test -- --coverage
```

---

## 🔗 集成测试

### JavaScript/TypeScript 集成

**Vitest 示例**:

```typescript
// tests/integration.test.ts
import { describe, it, expect, beforeAll } from "vitest"
import init, { greet, process_data, Counter } from "../pkg/mylib"

describe("Wasm Integration Tests", () => {
  beforeAll(async () => {
    // 初始化 WASM 模块
    await init()
  })

  describe("Basic Functions", () => {
    it("should greet correctly", () => {
      expect(greet("World")).toBe("Hello, World!")
      expect(greet("")).toBe("Hello, !")
    })

    it("should handle special characters", () => {
      expect(greet("测试")).toBe("Hello, 测试!")
    })
  })

  describe("Data Processing", () => {
    it("should process large data efficiently", () => {
      const input = new Uint8Array(1_000_000)
      input.fill(42)

      const start = performance.now()
      const output = process_data(input)
      const duration = performance.now() - start

      expect(output.length).toBe(1_000_000)
      expect(duration).toBeLessThan(100) // < 100ms
    })

    it("should handle edge cases", () => {
      expect(() => process_data(null)).toThrow()
      expect(process_data(new Uint8Array(0))).toHaveLength(0)
    })
  })

  describe("Class Instances", () => {
    it("should manage state correctly", () => {
      const counter = new Counter()
      expect(counter.value()).toBe(0)

      counter.increment()
      expect(counter.value()).toBe(1)

      counter.increment()
      expect(counter.value()).toBe(2)

      counter.reset()
      expect(counter.value()).toBe(0)
    })
  })
})
```

**性能基准测试**:

```typescript
// tests/benchmark.test.ts
import { bench, describe } from "vitest"
import { wasmSum, jsSum } from "../src"

describe("Performance Comparison", () => {
  const largeArray = new Int32Array(1_000_000).fill(1)

  bench("WASM implementation", () => {
    wasmSum(largeArray)
  })

  bench("JavaScript implementation", () => {
    jsSum(largeArray)
  })

  bench("Native array reduce", () => {
    largeArray.reduce((a, b) => a + b, 0)
  })
})
```

---

### 跨运行时测试

**测试矩阵**:

```yaml
# .github/workflows/test-cross-runtime.yml
name: Cross-Runtime Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        runtime:
          - wasmtime
          - wasmer
          - wasmedge
          - nodejs
          - deno

    steps:
      - uses: actions/checkout@v3

      - name: Install runtime
        run: |
          case ${{ matrix.runtime }} in
            wasmtime)
              curl https://wasmtime.dev/install.sh -sSf | bash
              ;;
            wasmer)
              curl https://get.wasmer.io -sSfL | sh
              ;;
            wasmedge)
              curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | bash
              ;;
          esac

      - name: Run tests
        run: ./scripts/test_runtime.sh ${{ matrix.runtime }}
```

**统一测试脚本**:

```bash
#!/bin/bash
# scripts/test_runtime.sh

RUNTIME=$1
WASM_MODULE="target/wasm32-wasi/release/myapp.wasm"

case $RUNTIME in
  wasmtime)
    wasmtime $WASM_MODULE --invoke main
    ;;
  wasmer)
    wasmer run $WASM_MODULE
    ;;
  wasmedge)
    wasmedge $WASM_MODULE
    ;;
  nodejs)
    node test_node.js
    ;;
  deno)
    deno run --allow-read test_deno.ts
    ;;
  *)
    echo "Unknown runtime: $RUNTIME"
    exit 1
    ;;
esac

echo "✅ Tests passed in $RUNTIME"
```

---

## 🌐 端到端测试

### Playwright 自动化测试

**完整E2E测试**:

```typescript
// tests/e2e/app.spec.ts
import { test, expect } from "@playwright/test"

test.describe("WASM Application E2E", () => {
  test.beforeEach(async ({ page }) => {
    // 导航到应用
    await page.goto("http://localhost:3000")

    // 等待 WASM 加载完成
    await page.waitForFunction(
      () => {
        return typeof window.wasmReady !== "undefined" && window.wasmReady === true
      },
      { timeout: 10000 }
    )
  })

  test("应用加载并初始化", async ({ page }) => {
    // 检查标题
    await expect(page).toHaveTitle(/WASM App/)

    // 检查主要元素
    await expect(page.locator("#app")).toBeVisible()
    await expect(page.locator("#compute-button")).toBeEnabled()
  })

  test("基本计算功能", async ({ page }) => {
    // 输入数据
    await page.fill("#input", "42")

    // 点击计算
    await page.click("#compute-button")

    // 等待结果
    await page.waitForSelector("#result:not(:empty)")

    // 验证结果
    const result = await page.textContent("#result")
    expect(result).toBe("1764") // 42^2
  })

  test("处理大文件上传", async ({ page }) => {
    // 创建 10MB 测试文件
    const testFile = Buffer.alloc(10 * 1024 * 1024, "A")

    // 上传文件
    const fileInput = await page.locator('input[type="file"]')
    await fileInput.setInputFiles({
      name: "test.bin",
      mimeType: "application/octet-stream",
      buffer: testFile,
    })

    // 开始处理
    await page.click("#process-button")

    // 等待进度条
    await page.waitForSelector('#progress[value="100"]', {
      timeout: 30000,
    })

    // 验证下载链接
    const downloadLink = await page.getAttribute("#download-link", "href")
    expect(downloadLink).toMatch(/^blob:/)
  })

  test("性能监控", async ({ page }) => {
    const start = Date.now()

    // 执行计算
    await page.click("#heavy-compute-button")
    await page.waitForSelector("#result:not(:empty)")

    const duration = Date.now() - start

    // 验证性能
    expect(duration).toBeLessThan(5000) // < 5秒

    // 检查性能指标
    const metrics = await page.evaluate(() => {
      const entries = performance.getEntriesByType("measure")
      return entries.map(e => ({
        name: e.name,
        duration: e.duration,
      }))
    })

    console.log("Performance metrics:", metrics)
  })

  test("错误处理", async ({ page }) => {
    // 触发错误
    await page.fill("#input", "invalid")
    await page.click("#compute-button")

    // 验证错误消息
    await expect(page.locator(".error-message")).toBeVisible()
    await expect(page.locator(".error-message")).toContainText("Invalid input")
  })
})
```

**配置文件**:

```typescript
// playwright.config.ts
import { defineConfig, devices } from "@playwright/test"

export default defineConfig({
  testDir: "./tests/e2e",
  timeout: 30000,
  retries: 2,
  workers: 4,

  use: {
    baseURL: "http://localhost:3000",
    trace: "on-first-retry",
    screenshot: "only-on-failure",
  },

  projects: [
    {
      name: "chromium",
      use: { ...devices["Desktop Chrome"] },
    },
    {
      name: "firefox",
      use: { ...devices["Desktop Firefox"] },
    },
    {
      name: "webkit",
      use: { ...devices["Desktop Safari"] },
    },
  ],

  webServer: {
    command: "npm run dev",
    port: 3000,
    reuseExistingServer: !process.env.CI,
  },
})
```

---

### 跨浏览器测试

**Selenium 示例**:

```python
# tests/test_cross_browser.py
from selenium import webdriver
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.by import By
import pytest

@pytest.fixture(params=['chrome', 'firefox', 'safari'])
def driver(request):
    browser = request.param

    if browser == 'chrome':
        driver = webdriver.Chrome()
    elif browser == 'firefox':
        driver = webdriver.Firefox()
    elif browser == 'safari':
        driver = webdriver.Safari()

    yield driver
    driver.quit()

def test_wasm_loading(driver):
    """测试 WASM 模块加载"""
    driver.get("http://localhost:3000")

    # 等待 WASM 加载
    WebDriverWait(driver, 10).until(
        lambda d: d.execute_script("return window.wasmLoaded === true")
    )

    assert True, "WASM loaded successfully"

def test_compute_function(driver):
    """测试计算功能"""
    driver.get("http://localhost:3000")

    # 等待加载
    WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.ID, "compute-button"))
    )

    # 输入数据
    input_field = driver.find_element(By.ID, "input")
    input_field.send_keys("42")

    # 点击计算
    compute_btn = driver.find_element(By.ID, "compute-button")
    compute_btn.click()

    # 等待结果
    result = WebDriverWait(driver, 5).until(
        EC.presence_of_element_located((By.ID, "result"))
    )

    assert result.text == "1764"

def test_performance(driver):
    """测试性能"""
    driver.get("http://localhost:3000")

    # 执行性能测试
    timing = driver.execute_script("""
        const start = performance.now();
        window.wasmModule.heavyCompute();
        const end = performance.now();
        return end - start;
    """)

    assert timing < 1000, f"Computation took {timing}ms, expected < 1000ms"
```

---

## ⚡ 性能测试

### 基准测试

**Criterion (Rust)**:

```rust
// benches/benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use mylib::{fibonacci, sum_array, process_string};

fn bench_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");

    for n in [10, 20, 30].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(n), n, |b, &n| {
            b.iter(|| fibonacci(black_box(n)));
        });
    }

    group.finish();
}

fn bench_array_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("array_ops");

    for size in [100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(
            BenchmarkId::new("sum", size),
            &data,
            |b, data| {
                b.iter(|| sum_array(black_box(data)));
            }
        );
    }

    group.finish();
}

criterion_group!(benches, bench_fibonacci, bench_array_operations);
criterion_main!(benches);
```

**运行基准测试**:

```bash
# 运行所有基准测试
cargo bench --target wasm32-wasi

# 运行特定基准测试
cargo bench --bench benchmark -- fibonacci

# 生成 HTML 报告
cargo bench --target wasm32-wasi -- --save-baseline current

# 对比基线
cargo bench --target wasm32-wasi -- --baseline current
```

**Criterion.toml 配置**:

```toml
[criterion]
confidence_level = 0.95
measurement_time = 10
sample_size = 100
warm_up_time = 3
```

---

### 内存性能测试

**内存泄漏检测**:

```javascript
// tests/memory-leak.test.js
import { test, expect } from "vitest"
import init, { processData } from "../pkg/mylib"

test("检测内存泄漏", async () => {
  await init()

  const iterations = 10000
  const measurements = []

  for (let i = 0; i < iterations; i++) {
    // 执行操作
    const data = new Uint8Array(1024)
    processData(data)

    // 每 1000 次记录内存使用
    if (i % 1000 === 0) {
      // 强制 GC（Node.js）
      if (global.gc) {
        global.gc()
      }

      const usage = process.memoryUsage()
      measurements.push({
        iteration: i,
        heapUsed: usage.heapUsed,
        external: usage.external,
      })

      console.log(`Iteration ${i}: Heap ${(usage.heapUsed / 1024 / 1024).toFixed(2)} MB`)
    }
  }

  // 分析内存增长趋势
  const firstMeasure = measurements[0].heapUsed
  const lastMeasure = measurements[measurements.length - 1].heapUsed
  const growth = lastMeasure - firstMeasure
  const growthPercent = (growth / firstMeasure) * 100

  console.log(
    `Memory growth: ${(growth / 1024 / 1024).toFixed(2)} MB (${growthPercent.toFixed(2)}%)`
  )

  // 内存增长应该小于 10%
  expect(growthPercent).toBeLessThan(10)
})
```

**WebAssembly 内存监控**:

```javascript
test("WASM 线性内存增长测试", async () => {
  const module = await WebAssembly.compile(wasmBytes)
  const memory = new WebAssembly.Memory({
    initial: 1, // 64KB
    maximum: 100, // 6.4MB
  })

  const instance = await WebAssembly.instantiate(module, {
    env: { memory },
  })

  // 初始大小
  expect(memory.buffer.byteLength).toBe(65536) // 1 page

  // 分配大缓冲区
  instance.exports.allocate_large_buffer(1000000) // 1MB

  // 检查内存增长
  const pages = memory.buffer.byteLength / 65536
  expect(pages).toBeGreaterThan(1)
  expect(pages).toBeLessThanOrEqual(100)

  console.log(`Memory pages: ${pages}`)
})
```

---

## 🔍 模糊测试

### cargo-fuzz

**模糊测试目标**:

```rust
// fuzz/fuzz_targets/parser.rs
#![no_main]
use libfuzzer_sys::fuzz_target;
use mylib::parse_input;

fuzz_target!(|data: &[u8]| {
    // 测试解析器不会 panic
    let _ = parse_input(data);
});
```

**多目标模糊测试**:

```rust
// fuzz/fuzz_targets/json_parser.rs
#![no_main]
use libfuzzer_sys::fuzz_target;
use mylib::parse_json;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = parse_json(s);
    }
});
```

**运行模糊测试**:

```bash
# 安装 cargo-fuzz
cargo install cargo-fuzz

# 运行特定目标
cargo fuzz run parser

# 限制时间
cargo fuzz run parser -- -max_total_time=3600

# 指定语料库
cargo fuzz run parser corpus/parser

# 并行运行
cargo fuzz run parser -- -jobs=8

# 查看覆盖率
cargo fuzz coverage parser
llvm-cov show target/*/release/parser
```

---

### 差异测试

**跨运行时差异测试**:

```python
# tests/differential_test.py
import subprocess
import json

def run_in_runtime(wasm_file, runtime, input_data):
    """在指定运行时中运行 WASM 模块"""
    commands = {
        'wasmtime': ['wasmtime', wasm_file],
        'wasmer': ['wasmer', 'run', wasm_file],
        'wasmedge': ['wasmedge', wasm_file],
    }

    cmd = commands[runtime]
    result = subprocess.run(
        cmd,
        input=input_data,
        capture_output=True,
        text=True
    )

    return result.stdout.strip()

def test_cross_runtime_consistency():
    """测试不同运行时的一致性"""
    wasm_file = 'target/wasm32-wasi/release/myapp.wasm'
    test_inputs = [
        b'{"value": 42}',
        b'{"value": -1}',
        b'{"array": [1,2,3,4,5]}',
    ]

    runtimes = ['wasmtime', 'wasmer', 'wasmedge']

    for input_data in test_inputs:
        results = {}

        for runtime in runtimes:
            try:
                output = run_in_runtime(wasm_file, runtime, input_data)
                results[runtime] = output
            except Exception as e:
                print(f"Error in {runtime}: {e}")
                continue

        # 验证所有运行时返回相同结果
        unique_results = set(results.values())

        if len(unique_results) != 1:
            print(f"❌ Inconsistent results for input: {input_data}")
            for runtime, output in results.items():
                print(f"  {runtime}: {output}")
            assert False, "Runtime results differ"
        else:
            print(f"✅ Consistent results: {unique_results.pop()}")

if __name__ == '__main__':
    test_cross_runtime_consistency()
```

---

## 🔄 回归测试

### 快照测试

**Jest/Vitest 快照**:

```typescript
// tests/snapshot.test.ts
import { test, expect } from "vitest"
import { renderWasmOutput } from "../src/renderer"

test("渲染输出快照测试", () => {
  const input = {
    data: [1, 2, 3, 4, 5],
    options: { format: "json" },
  }

  const output = renderWasmOutput(input)

  // 第一次运行会创建快照
  // 后续运行会对比快照
  expect(output).toMatchSnapshot()
})

test("复杂数据结构快照", () => {
  const complexData = {
    users: [
      { id: 1, name: "Alice", roles: ["admin"] },
      { id: 2, name: "Bob", roles: ["user"] },
    ],
    metadata: {
      version: "1.0",
      timestamp: 1234567890,
    },
  }

  expect(processComplexData(complexData)).toMatchSnapshot()
})
```

**更新快照**:

```bash
# 更新所有快照
npm test -- -u

# 更新特定测试的快照
npm test snapshot.test.ts -- -u
```

---

### 金标准测试

**文件对比测试**:

```rust
// tests/golden_tests.rs
use std::fs;

#[test]
fn test_image_processing() {
    let input = include_bytes!("fixtures/input.png");
    let expected = include_bytes!("fixtures/expected_output.png");

    let actual = process_image(input);

    assert_eq!(actual.as_slice(), expected.as_slice(),
        "Output doesn't match golden file");
}

#[test]
fn test_json_transformation() {
    let cases = [
        ("simple.json", "simple_output.json"),
        ("complex.json", "complex_output.json"),
        ("edge_case.json", "edge_case_output.json"),
    ];

    for (input_file, expected_file) in cases.iter() {
        let input = fs::read_to_string(
            format!("tests/fixtures/{}", input_file)
        ).unwrap();

        let expected = fs::read_to_string(
            format!("tests/fixtures/{}", expected_file)
        ).unwrap();

        let actual = transform_json(&input).unwrap();

        assert_eq!(actual, expected,
            "Mismatch for {}", input_file);
    }
}
```

**性能回归测试**:

```bash
#!/bin/bash
# scripts/perf_regression.sh

# 运行基准测试并保存结果
cargo bench --target wasm32-wasi -- --save-baseline current

# 切换到基线分支
git checkout main
cargo bench --target wasm32-wasi -- --save-baseline baseline

# 回到当前分支
git checkout -

# 对比结果
cargo bench --target wasm32-wasi -- --baseline baseline

# 检查回归
if cargo bench --target wasm32-wasi -- --baseline baseline 2>&1 | grep "regressed"; then
    echo "❌ Performance regression detected!"
    exit 1
else
    echo "✅ No performance regression"
fi
```

---

## 📊 属性测试

**QuickCheck (Rust)**:

```rust
#[cfg(test)]
mod property_tests {
    use quickcheck::{QuickCheck, TestResult};
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn prop_addition_commutative(a: i32, b: i32) -> bool {
        add(a, b) == add(b, a)
    }

    #[quickcheck]
    fn prop_addition_associative(a: i32, b: i32, c: i32) -> bool {
        add(add(a, b), c) == add(a, add(b, c))
    }

    #[quickcheck]
    fn prop_reverse_twice_is_identity(vec: Vec<i32>) -> bool {
        let reversed_twice = reverse(reverse(vec.clone()));
        vec == reversed_twice
    }

    #[quickcheck]
    fn prop_sort_preserves_length(mut vec: Vec<i32>) -> bool {
        let original_len = vec.len();
        sort(&mut vec);
        vec.len() == original_len
    }

    #[quickcheck]
    fn prop_sort_is_sorted(mut vec: Vec<i32>) -> bool {
        sort(&mut vec);
        vec.windows(2).all(|w| w[0] <= w[1])
    }

    #[quickcheck]
    fn prop_encode_decode_roundtrip(data: Vec<u8>) -> TestResult {
        if data.is_empty() {
            return TestResult::discard();
        }

        let encoded = encode(&data);
        let decoded = decode(&encoded).unwrap();

        TestResult::from_bool(data == decoded)
    }
}
```

---

## 🎭 测试隔离与 Mock

**Mock 导入函数**:

```javascript
// tests/mock-imports.test.js
import { test, expect } from "vitest"

test("Mock WASM 导入", async () => {
  const logBuffer = []
  const fetchResponses = new Map()

  // 创建 Mock 导入
  const mockImports = {
    env: {
      // Mock 日志函数
      log: (ptr, len) => {
        const message = readWasmString(ptr, len)
        logBuffer.push(message)
        console.log("[MOCK LOG]", message)
      },

      // Mock 数据获取
      fetch_data: (url_ptr, url_len) => {
        const url = readWasmString(url_ptr, url_len)
        const response = fetchResponses.get(url) || "default response"
        return writeWasmString(response)
      },

      // Mock 时间函数
      get_time: () => {
        return 1234567890 // 固定时间戳
      },
    },
  }

  // 设置测试数据
  fetchResponses.set("https://api.example.com/data", '{"value": 42}')

  // 实例化 WASM 模块
  const module = await WebAssembly.compile(wasmBytes)
  const instance = await WebAssembly.instantiate(module, mockImports)

  // 运行测试
  instance.exports.run_test()

  // 验证日志
  expect(logBuffer).toContain("Test started")
  expect(logBuffer).toContain("Fetching data")

  // 验证调用
  expect(logBuffer.length).toBeGreaterThan(0)
})
```

**WASI Mock**:

```rust
// tests/wasi_mock.rs
use wasi_common::pipe::{ReadPipe, WritePipe};
use wasmtime::*;
use wasmtime_wasi::{WasiCtxBuilder, sync::WasiCtxBuilder as SyncWasiCtxBuilder};

#[test]
fn test_with_mock_filesystem() -> Result<()> {
    // 创建虚拟输入
    let stdin = ReadPipe::from(b"test input data\n");
    let stdout = WritePipe::new_in_memory();
    let stderr = WritePipe::new_in_memory();

    // 构建 WASI 上下文
    let wasi = WasiCtxBuilder::new()
        .stdin(Box::new(stdin))
        .stdout(Box::new(stdout.clone()))
        .stderr(Box::new(stderr.clone()))
        .build();

    // 创建引擎和 Store
    let engine = Engine::default();
    let mut store = Store::new(&engine, wasi);

    // 加载模块
    let module = Module::from_file(&engine, "target/wasm32-wasi/release/myapp.wasm")?;

    // 创建 Linker
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::add_to_linker(&mut linker, |s| s)?;

    // 实例化
    let instance = linker.instantiate(&mut store, &module)?;

    // 运行主函数
    let run = instance.get_typed_func::<(), ()>(&mut store, "_start")?;
    run.call(&mut store, ())?;

    // 验证输出
    let stdout_contents = stdout.try_into_inner()
        .expect("stdout reference still held")
        .into_inner();
    let output = String::from_utf8(stdout_contents)?;

    assert!(output.contains("expected output"));

    Ok(())
}
```

---

## 🚀 持续集成测试

**完整 GitHub Actions 工作流**:

```yaml
# .github/workflows/test.yml
name: Comprehensive Testing

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  unit-tests:
    name: Unit Tests
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        rust: [stable, nightly]

    steps:
      - uses: actions/checkout@v3

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: ${{ matrix.rust }}
          target: wasm32-wasi
          override: true

      - name: Cache cargo
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/registry
            ~/.cargo/git
            target
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

      - name: Run unit tests
        run: |
          cargo test --target wasm32-wasi
          cargo test --lib

      - name: Upload test results
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: test-results-${{ matrix.os }}
          path: target/test-results/

  integration-tests:
    name: Integration Tests
    runs-on: ubuntu-latest
    needs: unit-tests

    steps:
      - uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: "20"

      - name: Install dependencies
        run: npm ci

      - name: Build WASM
        run: wasm-pack build --target web

      - name: Run integration tests
        run: npm run test:integration

  browser-tests:
    name: Browser Tests
    runs-on: ubuntu-latest
    needs: unit-tests

    steps:
      - uses: actions/checkout@v3

      - name: Install browsers
        run: npx playwright install --with-deps

      - name: Run Playwright tests
        run: npx playwright test

      - name: Upload Playwright report
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: playwright-report
          path: playwright-report/

  performance-tests:
    name: Performance Tests
    runs-on: ubuntu-latest
    needs: unit-tests

    steps:
      - uses: actions/checkout@v3

      - name: Run benchmarks
        run: cargo bench --target wasm32-wasi

      - name: Compare with baseline
        run: |
          cargo bench --target wasm32-wasi -- --save-baseline current
          # 与主分支对比
          git fetch origin main
          git checkout origin/main
          cargo bench --target wasm32-wasi -- --save-baseline main
          git checkout -
          cargo bench --target wasm32-wasi -- --baseline main

  coverage:
    name: Code Coverage
    runs-on: ubuntu-latest
    needs: [unit-tests, integration-tests]

    steps:
      - uses: actions/checkout@v3

      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin

      - name: Generate coverage
        run: |
          cargo tarpaulin --target wasm32-wasi \
            --out Xml \
            --output-dir ./coverage

      - name: Upload to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: ./coverage/cobertura.xml
          flags: unittests
          name: codecov-umbrella
```

---

## 📁 测试数据管理

**Fixture 目录结构**:

```text
tests/
├── fixtures/
│   ├── valid_inputs/
│   │   ├── simple.json
│   │   ├── complex.json
│   │   ├── edge_case.bin
│   │   └── large_data.bin
│   ├── invalid_inputs/
│   │   ├── corrupted.bin
│   │   ├── malformed.json
│   │   └── empty.bin
│   ├── expected_outputs/
│   │   ├── simple_output.json
│   │   ├── complex_output.json
│   │   └── processed.bin
│   └── snapshots/
│       ├── render_v1.png
│       └── transform_v1.json
└── integration/
    └── test_with_fixtures.rs
```

**测试数据生成器**:

```python
# scripts/generate_test_data.py
import struct
import random
import json
from pathlib import Path

def generate_binary_data(size, pattern='random'):
    """生成二进制测试数据"""
    data = bytearray(size)

    if pattern == 'random':
        for i in range(size):
            data[i] = random.randint(0, 255)
    elif pattern == 'sequential':
        for i in range(size):
            data[i] = i % 256
    elif pattern == 'zeros':
        pass  # 已经是零
    elif pattern == 'ones':
        for i in range(size):
            data[i] = 0xFF

    return data

def generate_json_data(complexity='simple'):
    """生成 JSON 测试数据"""
    if complexity == 'simple':
        return {"value": 42, "name": "test"}

    elif complexity == 'complex':
        return {
            "users": [
                {"id": i, "name": f"User{i}", "active": bool(i % 2)}
                for i in range(100)
            ],
            "metadata": {
                "version": "1.0",
                "timestamp": 1234567890,
                "tags": ["test", "data", "generated"]
            }
        }

    elif complexity == 'nested':
        def create_nested(depth):
            if depth == 0:
                return {"leaf": "value"}
            return {"nested": create_nested(depth - 1)}

        return create_nested(10)

def main():
    fixtures_dir = Path("tests/fixtures")

    # 生成二进制数据
    for size in [100, 1000, 10000, 100000]:
        for pattern in ['random', 'sequential', 'zeros']:
            data = generate_binary_data(size, pattern)
            output = fixtures_dir / f"valid_inputs/{pattern}_{size}.bin"
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(data)

    # 生成 JSON 数据
    for complexity in ['simple', 'complex', 'nested']:
        data = generate_json_data(complexity)
        output = fixtures_dir / f"valid_inputs/{complexity}.json"
        output.write_text(json.dumps(data, indent=2))

    print("✅ Test data generated successfully")

if __name__ == '__main__':
    main()
```

---

## 🎯 最佳实践

### 测试金字塔

**比例分配**:

| 测试类型 | 比例 | 数量示例 | 运行时间 |
| :--- | :--- | :--- | :--- || 单元测试 | 70%  | 700+     | 秒级     |
| 集成测试 | 20%  | 200+     | 分钟级   |
| E2E 测试 | 10%  | 100+     | 小时级   |

**实施策略**:

```text
1. 单元测试 (70%)
   ├─ 纯函数逻辑
   ├─ 数据结构操作
   ├─ 算法实现
   └─ 边界条件

2. 集成测试 (20%)
   ├─ WASM ↔ JavaScript 交互
   ├─ 模块间通信
   ├─ API 调用
   └─ 数据流测试

3. E2E 测试 (10%)
   ├─ 完整用户流程
   ├─ 跨浏览器测试
   ├─ 性能测试
   └─ 回归测试
```

### 测试先行 (TDD)

**Red-Green-Refactor 循环**:

```rust
// 步骤 1: Red - 写失败的测试
#[test]
fn test_fibonacci() {
    assert_eq!(fibonacci(0), 0);
    assert_eq!(fibonacci(1), 1);
    assert_eq!(fibonacci(10), 55);
}

// 步骤 2: Green - 最小实现
fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

// 步骤 3: Refactor - 优化实现
fn fibonacci(n: u32) -> u32 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..n {
        let temp = a;
        a = b;
        b = temp + b;
    }
    a
}
```

### 测试命名约定

**清晰的命名**:

```rust
#[test]
fn test_add_positive_numbers() { /* ... */ }

#[test]
fn test_add_negative_numbers() { /* ... */ }

#[test]
fn test_add_zero() { /* ... */ }

#[test]
fn test_add_overflow() { /* ... */ }
```

**BDD 风格**:

```rust
#[test]
fn given_empty_input_when_processing_then_returns_empty() { /* ... */ }

#[test]
fn given_valid_json_when_parsing_then_returns_object() { /* ... */ }
```

### 测试隔离

**每个测试应该独立**:

```rust
#[test]
fn test_independent_1() {
    let mut state = create_fresh_state();
    // 测试逻辑
    assert_eq!(state.value, 42);
}

#[test]
fn test_independent_2() {
    let mut state = create_fresh_state();
    // 完全独立的测试
    assert_eq!(state.value, 42);
}
```

---

## 📚 参考资源

### 官方文档

- 📖 [wasm-bindgen-test](https://rustwasm.github.io/wasm-bindgen/wasm-bindgen-test/)
- 📖 [Playwright Documentation](https://playwright.dev/)
- 📖 [Vitest Guide](https://vitest.dev/)
- 📖 [Criterion.rs](https://bheisler.github.io/criterion.rs/)

### 测试工具

- 🔧 [wasm-pack test](https://rustwasm.github.io/wasm-pack/)
- 🔧 [cargo-fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html)
- 🔧 [cargo-tarpaulin](https://github.com/xd009642/tarpaulin)

### 相关文档

- 📄 [开发工具链](./09.1_Development_Toolchain.md) - 测试工具详解
- 📄 [调试技术](./09.3_Debugging_Techniques.md) - 调试与问题定位
- 📄 [CI/CD 集成](./09.4_CICD_Integration.md) - 持续集成配置

---

**文档版本**: v1.0.0
**维护者**: c12_wasm 团队
**最后更新**: 2025-12-11
