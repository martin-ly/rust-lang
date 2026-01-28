# C12 WASM Tests

本目录包含了完整的测试套件，涵盖所有功能模块。

## 📚 测试文件列表

| 测试文件                                                   | 描述                 | 测试数量 | 运行环境 |
| ---------------------------------------------------------- | -------------------- | -------- | -------- |
| [basic_tests.rs](./basic_tests.rs)                         | 基础功能测试         | 30+      | Native   |
| [wasi_tests.rs](./wasi_tests.rs)                           | WASI 功能测试        | 15+      | WASI     |
| [design_patterns_tests.rs](./design_patterns_tests.rs)     | 设计模式测试         | 12+      | Native   |
| [rust_192_features_tests.rs](./rust_192_features_tests.rs) | Rust 1.92.0 特性测试 | 10+      | Native   |

## 🚀 运行测试

### 运行所有测试（Native环境）

```bash
# 运行所有本地测试
cargo test

# 运行特定测试文件
cargo test --test basic_tests
cargo test --test design_patterns_tests
cargo test --test rust_192_features_tests

# 运行特定测试函数
cargo test test_add_function
cargo test test_factory_pattern

# 显示测试输出
cargo test -- --nocapture

# 显示测试详细信息
cargo test -- --test-threads=1 --nocapture
```

### 运行 WASI 测试

```bash
# 添加 WASI 目标（首次运行）
rustup target add wasm32-wasi

# 运行 WASI 测试
cargo test --target wasm32-wasi --test wasi_tests

# 使用 WasmEdge 运行
cargo build --target wasm32-wasi --tests
wasmedge target/wasm32-wasi/debug/deps/wasi_tests-*.wasm

# 使用 Wasmtime 运行
wasmtime target/wasm32-wasi/debug/deps/wasi_tests-*.wasm
```

### 运行浏览器测试（wasm-bindgen-test）

```bash
# 安装 wasm-pack（首次运行）
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 运行浏览器测试
wasm-pack test --headless --firefox
wasm-pack test --headless --chrome

# 在浏览器中运行（需要手动操作）
wasm-pack test --firefox
wasm-pack test --chrome
```

## 📊 测试覆盖率

### 生成测试覆盖率报告

```bash
# 安装 tarpaulin（首次运行）
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --out Html --output-dir ./coverage

# 查看报告
# 浏览器打开 ./coverage/index.html
```

### 使用 llvm-cov

```bash
# 安装 llvm-cov（首次运行）
cargo install cargo-llvm-cov

# 生成覆盖率
cargo llvm-cov --html

# 查看报告
cargo llvm-cov --open
```

## 🔍 测试详情

### basic_tests.rs - 基础功能测试

测试 lib.rs 中的所有基础功能：

- ✅ 基础示例 (add, greet, sum_array)
- ✅ 字符串操作 (reverse, palindrome, count_words)
- ✅ 数组操作 (average, max, filter, reverse)
- ✅ 复杂类型 (Counter, Person)
- ✅ 性能优化示例
- ✅ 错误处理

**运行命令**：

```bash
cargo test --test basic_tests
```

**重点测试用例**：

- `test_add_function` - 测试基础加法
- `test_is_palindrome` - 测试回文检测
- `test_counter_increment` - 测试计数器递增
- `test_safe_divide` - 测试错误处理

### wasi_tests.rs - WASI 功能测试

测试 WASI 相关功能：

- ✅ 文件读写操作
- ✅ 文件复制操作
- ✅ 命令行参数处理
- ✅ 文本处理功能
- ✅ 边界情况处理

**运行命令**：

```bash
cargo test --target wasm32-wasi --test wasi_tests
```

**重点测试用例**：

- `test_read_write_file` - 测试文件读写
- `test_copy_file` - 测试文件复制
- `test_text_processor` - 测试文本处理
- `test_file_processing_workflow` - 集成测试

**注意事项**：

- WASI 测试只能在 wasm32-wasi 目标下运行
- 需要文件系统访问权限
- 测试会创建临时文件，运行后会自动清理

### design_patterns_tests.rs - 设计模式测试

测试各种设计模式的实现：

- ✅ 工厂模式 (Factory Pattern)
- ✅ 建造者模式 (Builder Pattern)
- ✅ 单例模式 (Singleton Pattern)
- ✅ 观察者模式 (Observer Pattern)
- ✅ 策略模式 (Strategy Pattern)
- ✅ 适配器模式 (Adapter Pattern)

**运行命令**：

```bash
cargo test --test design_patterns_tests
```

**重点测试用例**：

- `test_factory_pattern` - 测试工厂模式
- `test_builder_pattern` - 测试建造者模式
- `test_strategy_pattern_bubble_sort` - 测试策略模式
- `test_patterns_integration` - 模式集成测试

### rust_192_features_tests.rs - Rust 1.92.0 特性测试

测试 Rust 1.92.0 新特性：

- ✅ let-else 模式
- ✅ return-position impl Trait
- ✅ 迭代器优化
- ✅ 性能特性

**运行命令**：

```bash
cargo test --test rust_192_features_tests
```

**重点测试用例**：

- `test_let_else_with_some` - 测试 let-else 成功情况
- `test_let_else_with_none` - 测试 let-else 失败情况
- `test_impl_trait_return` - 测试 impl Trait 返回
- `test_iterator_chaining` - 测试迭代器链式调用

## 🐛 调试测试

### 查看测试输出

```bash
# 显示 println! 输出
cargo test -- --nocapture

# 显示成功的测试
cargo test -- --show-output

# 运行单个测试并显示输出
cargo test test_add_function -- --nocapture
```

### 测试失败时的调试

```bash
# 使用 --verbose 查看详细信息
cargo test --verbose

# 只运行失败的测试
cargo test --lib

# 使用 rust-gdb 调试
rust-gdb --args target/debug/deps/basic_tests-*
```

### 性能分析

```bash
# 使用 criterion 进行基准测试
cargo bench

# 使用 flamegraph 生成火焰图
cargo flamegraph --test basic_tests
```

## 📝 编写测试的最佳实践

### 1. 测试命名规范

```rust
#[test]
fn test_<function_name>_<scenario>() {
    // 测试代码
}

// 示例
#[test]
fn test_add_positive_numbers() { }

#[test]
fn test_add_negative_numbers() { }

#[test]
fn test_add_zero() { }
```

### 2. AAA 模式（Arrange-Act-Assert）

```rust
#[test]
fn test_example() {
    // Arrange - 准备测试数据
    let input = vec![1, 2, 3];

    // Act - 执行测试
    let result = sum_array(&input);

    // Assert - 验证结果
    assert_eq!(result, 6);
}
```

### 3. 边界情况测试

```rust
#[test]
fn test_edge_cases() {
    // 空输入
    assert_eq!(sum_array(&[]), 0);

    // 单个元素
    assert_eq!(sum_array(&[42]), 42);

    // 负数
    assert_eq!(sum_array(&[-1, -2, -3]), -6);
}
```

### 4. 错误处理测试

```rust
#[test]
fn test_error_handling() {
    let result = safe_divide(10.0, 0.0);
    assert!(result.is_err());
}

#[test]
#[should_panic(expected = "division by zero")]
fn test_panic() {
    let _ = 10 / 0;
}
```

## 🔧 持续集成

### GitHub Actions 配置

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
        with:
          toolchain: stable

      # Native 测试
      - name: Run tests
        run: cargo test

      # WASI 测试
      - name: Add WASI target
        run: rustup target add wasm32-wasi

      - name: Run WASI tests
        run: cargo test --target wasm32-wasi

      # 覆盖率
      - name: Generate coverage
        run: |
          cargo install cargo-tarpaulin
          cargo tarpaulin --out Xml

      - name: Upload coverage
        uses: codecov/codecov-action@v2
```

## 📚 参考资源

- [Rust 测试指南](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [wasm-bindgen 测试](https://rustwasm.github.io/wasm-bindgen/wasm-bindgen-test/index.html)
- [WASI 测试最佳实践](https://github.com/bytecodealliance/wasmtime/blob/main/docs/WASI-tutorial.md)

---

**最后更新**: 2025-12-11
**测试框架版本**: Rust 1.92.0+ / Edition 2024
**总测试数**: 70+
