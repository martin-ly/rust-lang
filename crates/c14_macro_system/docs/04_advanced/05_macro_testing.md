# 宏测试策略

> **学习目标**：掌握全面测试声明式宏和过程宏的方法，确保宏的正确性和健壮性。

---

## 📖 目录

- [宏测试策略](#宏测试策略)
  - [📖 目录](#-目录)
  - [测试基础](#测试基础)
    - [为什么测试宏很重要？](#为什么测试宏很重要)
    - [测试金字塔](#测试金字塔)
    - [测试类型](#测试类型)
  - [声明式宏测试](#声明式宏测试)
    - [1. 基本单元测试](#1-基本单元测试)
    - [2. 测试不同模式](#2-测试不同模式)
    - [3. 测试重复模式](#3-测试重复模式)
    - [4. 测试边界情况](#4-测试边界情况)
    - [5. 测试代码生成](#5-测试代码生成)
  - [过程宏测试](#过程宏测试)
    - [1. 单元测试基础](#1-单元测试基础)
    - [2. 使用 `trybuild` 测试](#2-使用-trybuild-测试)
      - [成功测试用例](#成功测试用例)
      - [失败测试用例](#失败测试用例)
    - [3. 测试复杂场景](#3-测试复杂场景)
    - [4. 属性宏测试](#4-属性宏测试)
    - [5. Function-like 宏测试](#5-function-like-宏测试)
  - [集成测试](#集成测试)
    - [1. 跨模块测试](#1-跨模块测试)
    - [2. 与其他 crate 集成](#2-与其他-crate-集成)
    - [3. 实际使用场景测试](#3-实际使用场景测试)
  - [错误测试](#错误测试)
    - [1. 测试编译错误](#1-测试编译错误)
    - [2. 测试运行时错误](#2-测试运行时错误)
    - [3. 测试错误恢复](#3-测试错误恢复)
  - [回归测试](#回归测试)
    - [1. 快照测试](#1-快照测试)
    - [2. 版本兼容性测试](#2-版本兼容性测试)
    - [3. 已知问题测试](#3-已知问题测试)
  - [性能测试](#性能测试)
    - [1. 编译时间测试](#1-编译时间测试)
    - [2. 宏展开性能](#2-宏展开性能)
    - [3. 增量编译测试](#3-增量编译测试)
  - [测试自动化](#测试自动化)
    - [1. CI/CD 配置](#1-cicd-配置)
    - [2. 测试矩阵](#2-测试矩阵)
    - [3. 覆盖率报告](#3-覆盖率报告)
  - [测试最佳实践](#测试最佳实践)
    - [1. 测试组织](#1-测试组织)
    - [2. 测试命名约定](#2-测试命名约定)
    - [3. 测试文档](#3-测试文档)
    - [4. 测试覆盖率目标](#4-测试覆盖率目标)
    - [5. 持续测试](#5-持续测试)
  - [测试检查清单](#测试检查清单)
    - [开发阶段](#开发阶段)
    - [集成阶段](#集成阶段)
    - [发布前](#发布前)
  - [测试工具总结](#测试工具总结)
  - [总结](#总结)
  - [相关资源](#相关资源)

---

## 测试基础

### 为什么测试宏很重要？

宏在编译时执行，错误可能：

- 难以调试
- 影响范围广
- 错误消息不清晰
- 破坏性强

```text
未测试的宏 → 生产环境编译失败 → 😱
充分测试的宏 → 及早发现问题 → ✅
```

### 测试金字塔

```text
      /\           单元测试 (70%)
     /  \          - 测试单个规则
    /────\         - 测试边界情况
   /      \        
  /────────\       集成测试 (20%)
 /          \      - 测试实际使用场景
/────────────\     - 测试与其他代码交互
                   
                   端到端测试 (10%)
                   - 测试完整项目
                   - 性能测试
```

### 测试类型

| 测试类型 | 目标 | 工具 |
|---------|------|------|
| **单元测试** | 测试单个宏规则 | `#[test]` |
| **集成测试** | 测试实际使用 | `tests/` 目录 |
| **编译失败测试** | 验证错误消息 | `trybuild` |
| **展开测试** | 验证生成代码 | `cargo-expand` |
| **性能测试** | 测试编译时间 | 自定义脚本 |

---

## 声明式宏测试

### 1. 基本单元测试

```rust
macro_rules! add {
    ($a:expr, $b:expr) => {
        $a + $b
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_add_basic() {
        assert_eq!(add!(2, 3), 5);
        assert_eq!(add!(0, 0), 0);
        assert_eq!(add!(-1, 1), 0);
    }
    
    #[test]
    fn test_add_expressions() {
        assert_eq!(add!(1 + 1, 2 + 2), 6);
        assert_eq!(add!(2 * 3, 4), 10);
    }
    
    #[test]
    fn test_add_variables() {
        let x = 5;
        let y = 10;
        assert_eq!(add!(x, y), 15);
    }
}
```

### 2. 测试不同模式

```rust
macro_rules! create_var {
    ($name:ident = $value:expr) => {
        let $name = $value;
    };
    ($name:ident: $type:ty = $value:expr) => {
        let $name: $type = $value;
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_pattern_1() {
        create_var!(x = 42);
        assert_eq!(x, 42);
    }
    
    #[test]
    fn test_pattern_2() {
        create_var!(y: i64 = 100);
        assert_eq!(y, 100i64);
    }
}
```

### 3. 测试重复模式

```rust
macro_rules! sum {
    () => { 0 };
    ($single:expr) => { $single };
    ($first:expr, $($rest:expr),+) => {
        $first + sum!($($rest),+)
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sum_empty() {
        assert_eq!(sum!(), 0);
    }
    
    #[test]
    fn test_sum_single() {
        assert_eq!(sum!(5), 5);
    }
    
    #[test]
    fn test_sum_multiple() {
        assert_eq!(sum!(1, 2, 3, 4, 5), 15);
    }
    
    #[test]
    fn test_sum_expressions() {
        assert_eq!(sum!(1 + 1, 2 * 2, 3 - 1), 8);
    }
}
```

### 4. 测试边界情况

```rust
macro_rules! safe_index {
    ($arr:expr, $idx:expr) => {
        if $idx < $arr.len() {
            Some($arr[$idx])
        } else {
            None
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_valid_index() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(safe_index!(arr, 0), Some(1));
        assert_eq!(safe_index!(arr, 4), Some(5));
    }
    
    #[test]
    fn test_invalid_index() {
        let arr = [1, 2, 3];
        assert_eq!(safe_index!(arr, 3), None);
        assert_eq!(safe_index!(arr, 100), None);
    }
    
    #[test]
    fn test_empty_array() {
        let arr: [i32; 0] = [];
        assert_eq!(safe_index!(arr, 0), None);
    }
}
```

### 5. 测试代码生成

```rust
macro_rules! generate_struct {
    ($name:ident { $($field:ident: $type:ty),* }) => {
        struct $name {
            $($field: $type),*
        }
        
        impl $name {
            fn new($($field: $type),*) -> Self {
                Self { $($field),* }
            }
        }
    };
}

#[cfg(test)]
mod tests {
    generate_struct!(Person {
        name: String,
        age: u32
    });
    
    #[test]
    fn test_generated_struct() {
        let person = Person::new("Alice".to_string(), 30);
        assert_eq!(person.name, "Alice");
        assert_eq!(person.age, 30);
    }
}
```

---

## 过程宏测试

### 1. 单元测试基础

```rust
// my_macro/src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let expanded = quote! {
        impl MyTrait for #name {
            fn my_method(&self) -> &'static str {
                stringify!(#name)
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 测试辅助函数
#[cfg(test)]
pub fn derive_my_trait(input: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    my_derive(input.into()).into()
}
```

```rust
// my_macro/tests/derive_tests.rs
use my_macro::derive_my_trait;
use quote::quote;
use syn;

#[test]
fn test_simple_struct() {
    let input = quote! {
        struct MyStruct {
            field: i32,
        }
    };
    
    let output = derive_my_trait(input);
    
    // 解析输出以验证其有效性
    let parsed: syn::File = syn::parse2(output).expect("Failed to parse output");
    
    // 验证生成了一个 impl 块
    assert_eq!(parsed.items.len(), 1);
}

#[test]
fn test_output_contains_impl() {
    let input = quote! {
        struct Test;
    };
    
    let output = derive_my_trait(input);
    let output_str = output.to_string();
    
    assert!(output_str.contains("impl MyTrait for Test"));
    assert!(output_str.contains("fn my_method"));
}
```

### 2. 使用 `trybuild` 测试

`trybuild` 是测试过程宏的最佳工具：

```rust
// my_macro/tests/ui.rs
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    
    // 测试成功编译的情况
    t.pass("tests/ui/pass/*.rs");
    
    // 测试应该失败的情况
    t.compile_fail("tests/ui/fail/*.rs");
}
```

#### 成功测试用例

```rust
// tests/ui/pass/basic.rs
use my_macro::MyDerive;

#[derive(MyDerive)]
struct Simple {
    field: i32,
}

fn main() {
    let s = Simple { field: 42 };
    assert_eq!(s.my_method(), "Simple");
}
```

```rust
// tests/ui/pass/generic.rs
use my_macro::MyDerive;

#[derive(MyDerive)]
struct Generic<T> {
    value: T,
}

fn main() {
    let g = Generic { value: 42 };
    assert_eq!(g.my_method(), "Generic");
}
```

#### 失败测试用例

```rust
// tests/ui/fail/enum_not_supported.rs
use my_macro::MyDerive;

#[derive(MyDerive)]
enum NotSupported {
    Variant,
}

fn main() {}
```

```text
// tests/ui/fail/enum_not_supported.stderr
error: MyDerive only supports structs
 --> tests/ui/fail/enum_not_supported.rs:3:10
  |
3 | #[derive(MyDerive)]
  |          ^^^^^^^^
```

### 3. 测试复杂场景

```rust
// tests/complex_tests.rs
use my_macro::Builder;
use quote::quote;

#[test]
fn test_builder_with_options() {
    let input = quote! {
        struct Config {
            host: String,
            port: u16,
            #[builder(default)]
            timeout: u64,
        }
    };
    
    let output = derive_builder(input);
    
    // 验证输出包含正确的方法
    let output_str = output.to_string();
    assert!(output_str.contains("fn host"));
    assert!(output_str.contains("fn port"));
    assert!(output_str.contains("fn timeout"));
    assert!(output_str.contains("fn build"));
}

#[test]
fn test_builder_usage() {
    #[derive(Builder)]
    struct User {
        name: String,
        age: u32,
    }
    
    let user = User::builder()
        .name("Alice".to_string())
        .age(30)
        .build()
        .unwrap();
    
    assert_eq!(user.name, "Alice");
    assert_eq!(user.age, 30);
}
```

### 4. 属性宏测试

```rust
// my_macro/src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn trace(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = &input.sig.ident;
    let body = &input.block;
    let sig = &input.sig;
    
    let expanded = quote! {
        #sig {
            println!("Entering {}", stringify!(#name));
            let result = (|| #body)();
            println!("Exiting {}", stringify!(#name));
            result
        }
    };
    
    TokenStream::from(expanded)
}

// tests/attribute_tests.rs
#[test]
fn test_trace_attribute() {
    #[trace]
    fn example() -> i32 {
        42
    }
    
    assert_eq!(example(), 42);
}
```

### 5. Function-like 宏测试

```rust
// my_macro/src/lib.rs
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    // 解析和生成 SQL 查询
    // ...
}

// tests/function_like_tests.rs
#[test]
fn test_sql_macro() {
    let query = sql!(SELECT id, name FROM users WHERE age > 18);
    
    // 验证查询结构
    assert_eq!(query.table(), "users");
    assert_eq!(query.columns(), vec!["id", "name"]);
}
```

---

## 集成测试

### 1. 跨模块测试

```rust
// tests/integration_test.rs
use my_macro::{MyDerive, Builder};

#[derive(MyDerive, Builder)]
struct Combined {
    field1: String,
    field2: i32,
}

#[test]
fn test_combined_derives() {
    let obj = Combined::builder()
        .field1("test".to_string())
        .field2(42)
        .build()
        .unwrap();
    
    assert_eq!(obj.my_method(), "Combined");
    assert_eq!(obj.field1, "test");
}
```

### 2. 与其他 crate 集成

```rust
// tests/external_integration.rs
use my_macro::MyDerive;
use serde::{Serialize, Deserialize};

#[derive(MyDerive, Serialize, Deserialize)]
struct IntegratedStruct {
    data: String,
}

#[test]
fn test_with_serde() {
    let obj = IntegratedStruct {
        data: "test".to_string(),
    };
    
    let json = serde_json::to_string(&obj).unwrap();
    let deserialized: IntegratedStruct = serde_json::from_str(&json).unwrap();
    
    assert_eq!(deserialized.data, "test");
    assert_eq!(deserialized.my_method(), "IntegratedStruct");
}
```

### 3. 实际使用场景测试

```rust
// tests/real_world_test.rs
use my_macro::Builder;

#[derive(Builder)]
struct ServerConfig {
    host: String,
    port: u16,
    #[builder(default = 10)]
    max_connections: usize,
}

#[test]
fn test_server_config_realistic() {
    let config = ServerConfig::builder()
        .host("localhost".to_string())
        .port(8080)
        .build()
        .unwrap();
    
    assert_eq!(config.host, "localhost");
    assert_eq!(config.port, 8080);
    assert_eq!(config.max_connections, 10); // 默认值
}

#[test]
fn test_server_config_full() {
    let config = ServerConfig::builder()
        .host("0.0.0.0".to_string())
        .port(443)
        .max_connections(1000)
        .build()
        .unwrap();
    
    assert_eq!(config.max_connections, 1000);
}
```

---

## 错误测试

### 1. 测试编译错误

使用 `trybuild` 验证错误消息：

```rust
// tests/ui/fail/missing_field.rs
use my_macro::Builder;

#[derive(Builder)]
struct Incomplete {
    required: String,
}

fn main() {
    // 应该失败：缺少 required 字段
    let _ = Incomplete::builder().build();
}
```

```text
// tests/ui/fail/missing_field.stderr
error[E0308]: mismatched types
  --> tests/ui/fail/missing_field.rs:8:13
   |
8  |     let _ = Incomplete::builder().build();
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected `Result<Incomplete, &str>`, found `()`
```

### 2. 测试运行时错误

```rust
#[test]
#[should_panic(expected = "Field 'required_field' is missing")]
fn test_builder_panics_on_missing_field() {
    #[derive(Builder)]
    struct Test {
        required_field: String,
    }
    
    let _ = Test::builder()
        .build()
        .expect("Should panic");
}
```

### 3. 测试错误恢复

```rust
#[test]
fn test_error_recovery() {
    #[derive(Builder)]
    struct Config {
        value: i32,
    }
    
    let result = Config::builder().build();
    
    assert!(result.is_err());
    assert_eq!(
        result.unwrap_err(),
        "Field 'value' is required"
    );
}
```

---

## 回归测试

### 1. 快照测试

```rust
// tests/snapshot_tests.rs
use insta::assert_snapshot;

#[test]
fn test_macro_output_snapshot() {
    let input = quote! {
        struct Example {
            field: String,
        }
    };
    
    let output = derive_my_macro(input);
    
    // 第一次运行会创建快照
    // 后续运行会与快照比较
    assert_snapshot!(output.to_string());
}
```

### 2. 版本兼容性测试

```rust
// tests/version_compat.rs
#[cfg(feature = "v1_api")]
#[test]
fn test_v1_compatibility() {
    // 测试旧版本 API
}

#[cfg(feature = "v2_api")]
#[test]
fn test_v2_compatibility() {
    // 测试新版本 API
}
```

### 3. 已知问题测试

```rust
#[test]
#[ignore] // 暂时忽略
fn test_known_issue_123() {
    // 这是一个已知问题的回归测试
    // Issue: https://github.com/user/repo/issues/123
    
    #[derive(MyMacro)]
    struct ProblematicCase {
        // 特定会导致问题的配置
    }
}
```

---

## 性能测试

### 1. 编译时间测试

```rust
// benches/compile_time.rs
use std::process::Command;
use std::time::Instant;

#[test]
fn benchmark_compile_time() {
    let start = Instant::now();
    
    let status = Command::new("cargo")
        .args(&["build", "--release"])
        .status()
        .expect("Failed to run cargo build");
    
    let duration = start.elapsed();
    
    assert!(status.success());
    println!("Compile time: {:?}", duration);
    
    // 设置合理的编译时间上限
    assert!(duration.as_secs() < 60, "Compilation took too long");
}
```

### 2. 宏展开性能

```rust
// tests/expansion_performance.rs
#[test]
fn test_large_scale_expansion() {
    // 测试生成大量代码的性能
    macro_rules! generate_many {
        ($($n:expr),*) => {
            $(
                fn $n() -> i32 { $n }
            )*
        };
    }
    
    // 生成1000个函数
    generate_many!(
        0, 1, 2, 3, /* ... */ 999
    );
}
```

### 3. 增量编译测试

```bash
#!/bin/bash
# scripts/test_incremental.sh

# 首次完整编译
cargo clean
time cargo build

# 修改单个文件
touch src/lib.rs

# 增量编译
time cargo build

# 比较两次编译时间
```

---

## 测试自动化

### 1. CI/CD 配置

```yaml
# .github/workflows/test.yml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          
      - name: Run tests
        run: cargo test --all-features
        
      - name: Run UI tests
        run: cargo test --test ui
        
      - name: Check macro expansion
        run: |
          cargo install cargo-expand
          cargo expand --lib > /dev/null
```

### 2. 测试矩阵

```yaml
strategy:
  matrix:
    rust: [stable, beta, nightly]
    os: [ubuntu-latest, macos-latest, windows-latest]
    
steps:
  - name: Test on ${{ matrix.os }} with ${{ matrix.rust }}
    run: cargo +${{ matrix.rust }} test
```

### 3. 覆盖率报告

```yaml
- name: Generate coverage
  run: |
    cargo install cargo-tarpaulin
    cargo tarpaulin --out Xml
    
- name: Upload coverage
  uses: codecov/codecov-action@v1
```

---

## 测试最佳实践

### 1. 测试组织

```text
my_macro/
├── src/
│   └── lib.rs          # 宏实现
├── tests/
│   ├── unit/           # 单元测试
│   │   ├── basic.rs
│   │   └── advanced.rs
│   ├── integration/    # 集成测试
│   │   └── full_usage.rs
│   └── ui/             # UI 测试
│       ├── pass/       # 应该成功的测试
│       └── fail/       # 应该失败的测试
└── benches/            # 性能测试
    └── compile_time.rs
```

### 2. 测试命名约定

```rust
#[test]
fn test_<feature>_<scenario>_<expected_outcome>() {
    // 例如：
    // test_builder_missing_field_returns_error()
    // test_derive_on_struct_generates_impl()
    // test_macro_with_generics_compiles()
}
```

### 3. 测试文档

```rust
/// 测试 Builder 宏在缺少必需字段时的行为
///
/// # 测试场景
/// - 定义一个包含必需字段的结构体
/// - 尝试构建时不提供该字段
///
/// # 预期结果
/// - build() 返回 Err
/// - 错误消息指明缺少的字段
#[test]
fn test_builder_required_field_validation() {
    // 测试代码
}
```

### 4. 测试覆盖率目标

```text
目标覆盖率：
├─ 单元测试: > 80%
├─ 集成测试: > 60%
├─ 错误路径: 100%
└─ 边界情况: 100%
```

### 5. 持续测试

```rust
// 使用 cargo-watch 进行持续测试
// cargo install cargo-watch
// cargo watch -x test
```

---

## 测试检查清单

### 开发阶段

- [ ] 为每个宏规则编写单元测试
- [ ] 测试所有边界情况
- [ ] 测试空输入情况
- [ ] 测试与其他宏的组合

### 集成阶段

- [ ] 在实际项目中测试
- [ ] 测试与常用 crate 的兼容性
- [ ] 验证错误消息清晰
- [ ] 检查编译时间是否合理

### 发布前

- [ ] 所有测试通过
- [ ] UI 测试覆盖常见错误
- [ ] 文档包含使用示例
- [ ] CI/CD 配置正确
- [ ] 覆盖率达标

---

## 测试工具总结

| 工具 | 用途 | 适用场景 |
|------|------|----------|
| `#[test]` | 基本单元测试 | 声明式宏、辅助函数 |
| `trybuild` | UI 测试 | 过程宏错误消息 |
| `cargo-expand` | 展开验证 | 检查生成代码 |
| `insta` | 快照测试 | 回归测试 |
| `criterion` | 性能基准 | 编译时性能 |
| `cargo-tarpaulin` | 覆盖率 | CI/CD集成 |

---

## 总结

全面的宏测试策略应该包括：

- **单元测试**：测试单个规则和模式
- **集成测试**：测试实际使用场景
- **UI 测试**：使用 `trybuild` 验证错误
- **性能测试**：监控编译时间
- **自动化**：CI/CD 持续测试
- **文档**：清晰的测试文档

通过系统化的测试，你可以确保宏的正确性、健壮性和可维护性！

## 相关资源

- [03_macro_debugging.md](./03_macro_debugging.md) - 调试技巧
- [02_code_generation.md](./02_code_generation.md) - 代码生成
- [../05_practice/02_best_practices.md](../05_practice/02_best_practices.md) - 最佳实践
