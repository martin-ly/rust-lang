# 宏性能优化实践

> **文档定位**: Rust宏编译性能优化完整指南  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **文档类型**: 高级主题 + 性能优化

---

## 📊 目录

- [宏性能优化实践](#宏性能优化实践)
  - [📊 目录](#-目录)
  - [1. 性能分析](#1-性能分析)
    - [1.1 编译时间分析](#11-编译时间分析)
    - [1.2 识别性能瓶颈](#12-识别性能瓶颈)
  - [2. TokenStream优化](#2-tokenstream优化)
    - [2.1 避免重复解析](#21-避免重复解析)
    - [2.2 延迟解析](#22-延迟解析)
    - [2.3 优化quote使用](#23-优化quote使用)
  - [3. 增量编译优化](#3-增量编译优化)
    - [3.1 理解增量编译](#31-理解增量编译)
    - [3.2 减少依赖影响](#32-减少依赖影响)
    - [3.3 分离编译单元](#33-分离编译单元)
  - [4. 宏展开缓存](#4-宏展开缓存)
    - [4.1 memorization模式](#41-memorization模式)
    - [4.2 编译时常量](#42-编译时常量)
  - [5. 依赖最小化](#5-依赖最小化)
    - [5.1 可选依赖](#51-可选依赖)
    - [5.2 特征门控](#52-特征门控)
  - [6. 性能基准测试](#6-性能基准测试)
    - [6.1 基准测试框架](#61-基准测试框架)
    - [6.2 编译时间基准](#62-编译时间基准)
    - [6.3 性能监控](#63-性能监控)
  - [优化清单](#优化清单)
    - [✅ TokenStream优化](#-tokenstream优化)
    - [✅ 依赖优化](#-依赖优化)
    - [✅ 编译优化](#-编译优化)
    - [✅ 代码质量](#-代码质量)
  - [实际案例](#实际案例)
    - [Case 1: Serde性能优化](#case-1-serde性能优化)
    - [Case 2: Tokio宏优化](#case-2-tokio宏优化)
  - [总结](#总结)
  - [相关文档](#相关文档)
  - [返回导航](#返回导航)

---

## 1. 性能分析

### 1.1 编译时间分析

```bash
# 1. 使用cargo编译时间分析
cargo build --timings

# 2. 详细分析
RUSTFLAGS="-Z self-profile" cargo build

# 3. 使用flamegraph
cargo flamegraph --bin my-app

# 4. 分析宏展开时间
RUSTC_LOG=rustc_expand=debug cargo build 2>&1 | grep "expand"
```

---

### 1.2 识别性能瓶颈

```rust
/// 宏性能分析装饰器
#[proc_macro_attribute]
pub fn profile(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let start = std::time::Instant::now();
    
    let input = parse_macro_input!(item as ItemFn);
    let result = process(input);
    
    let duration = start.elapsed();
    eprintln!("Macro expansion took: {:?}", duration);
    
    result.into()
}
```

---

## 2. TokenStream优化

### 2.1 避免重复解析

**❌ 反模式：重复解析**:

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 每次都完整解析 - 慢!
    let input1 = parse_macro_input!(input as DeriveInput);
    let input2 = parse_macro_input!(input as DeriveInput); // 重复!
    
    // ...
}
```

**✅ 优化后**:

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 只解析一次
    let input = parse_macro_input!(input as DeriveInput);
    
    // 克隆引用而不是重新解析
    let name = &input.ident;
    let generics = &input.generics;
    
    // ...
}
```

---

### 2.2 延迟解析

```rust
use syn::parse::{Parse, ParseStream};

/// 延迟解析：只在需要时解析
struct LazyParsed {
    tokens: TokenStream,
}

impl LazyParsed {
    fn parse_when_needed(&self) -> Result<DeriveInput, Error> {
        syn::parse2(self.tokens.clone())
    }
}

// 更好的方式：使用缓存
use std::cell::OnceCell;

struct CachedParsed {
    tokens: TokenStream,
    parsed: OnceCell<DeriveInput>,
}

impl CachedParsed {
    fn get_or_parse(&self) -> &DeriveInput {
        self.parsed.get_or_init(|| {
            syn::parse2(self.tokens.clone()).unwrap()
        })
    }
}
```

---

### 2.3 优化quote使用

**❌ 反模式：在循环中quote**:

```rust
let mut result = TokenStream::new();
for field in fields {
    // 每次迭代都构建新的TokenStream - 慢!
    let tokens = quote! {
        println!("{}", #field);
    };
    result.extend(tokens);
}
```

**✅ 优化后**:

```rust
// 一次性构建
let fields_iter = fields.iter();
let result = quote! {
    #(
        println!("{}", #fields_iter);
    )*
};
```

---

## 3. 增量编译优化

### 3.1 理解增量编译

```rust
/// 依赖追踪
///
/// Rust编译器会追踪：
/// 1. 宏的输入 (input tokens)
/// 2. 宏的实现代码
/// 3. 宏的依赖库
///
/// 改变任何一个都会触发重新编译
```

---

### 3.2 减少依赖影响

**❌ 过度依赖**:

```rust
// 导入整个库
use syn::*;
use quote::*;

#[proc_macro_derive(Heavy)]
pub fn heavy(input: TokenStream) -> TokenStream {
    // 使用很多syn功能
    // ...
}
```

**✅ 精确导入**:

```rust
// 只导入需要的
use syn::{DeriveInput, Data, Fields};
use quote::quote;

#[proc_macro_derive(Light)]
pub fn light(input: TokenStream) -> TokenStream {
    // 只使用必要功能
    // ...
}
```

---

### 3.3 分离编译单元

```rust
// 将proc-macro分离到独立crate
// 
// my-macros/         <- proc-macro crate
// my-macros-impl/    <- 实现逻辑 (library)
// my-app/            <- 使用宏

// my-macros/src/lib.rs
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    my_macros_impl::derive_impl(input)
}

// my-macros-impl/src/lib.rs
pub fn derive_impl(input: TokenStream) -> TokenStream {
    // 实现细节
    // 这个crate可以被测试和基准测试
}
```

---

## 4. 宏展开缓存

### 4.1 memorization模式

```rust
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static! {
    static ref EXPANSION_CACHE: Mutex<HashMap<String, TokenStream>> = {
        Mutex::new(HashMap::new())
    };
}

#[proc_macro]
pub fn cached_macro(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();
    
    // 检查缓存
    if let Ok(cache) = EXPANSION_CACHE.lock() {
        if let Some(cached) = cache.get(&input_str) {
            return cached.clone();
        }
    }
    
    // 计算结果
    let result = expensive_expansion(input);
    
    // 存入缓存
    if let Ok(mut cache) = EXPANSION_CACHE.lock() {
        cache.insert(input_str, result.clone());
    }
    
    result
}
```

---

### 4.2 编译时常量

```rust
/// 使用const来避免重复计算
const MAX_FIELDS: usize = 64;

#[proc_macro_derive(Optimized)]
pub fn optimized(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 编译时检查
    if field_count(&input.data) > MAX_FIELDS {
        return quote! {
            compile_error!("Too many fields");
        }.into();
    }
    
    // ...
}
```

---

## 5. 依赖最小化

### 5.1 可选依赖

```toml
[dependencies]
syn = { version = "2.0", features = ["derive"], default-features = false }
quote = "1.0"

# 仅在需要时启用
proc-macro2 = { version = "1.0", optional = true }

[features]
default = []
full = ["syn/full", "proc-macro2"]
```

---

### 5.2 特征门控

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    #[cfg(feature = "full-parse")]
    {
        full_parse_impl(input)
    }
    
    #[cfg(not(feature = "full-parse"))]
    {
        simple_parse_impl(input)
    }
}
```

---

## 6. 性能基准测试

### 6.1 基准测试框架

```rust
// benches/macro_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_macro_expansion(c: &mut Criterion) {
    c.bench_function("simple_derive", |b| {
        b.iter(|| {
            let input = quote! {
                struct TestStruct {
                    field1: i32,
                    field2: String,
                }
            };
            
            black_box(my_derive_impl(input.into()))
        })
    });
}

criterion_group!(benches, bench_macro_expansion);
criterion_main!(benches);
```

---

### 6.2 编译时间基准

```bash
#!/bin/bash
# benchmark_compile_time.sh

echo "Measuring compilation time..."

# 清理
cargo clean

# 测试1: 不使用宏
time cargo build --no-default-features

# 清理
cargo clean

# 测试2: 使用宏
time cargo build

# 比较结果
```

---

### 6.3 性能监控

```rust
/// 编译时性能报告
#[proc_macro_attribute]
pub fn report_perf(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let start = std::time::Instant::now();
    
    let input = parse_macro_input!(item as ItemFn);
    let output = process(input);
    
    let duration = start.elapsed();
    
    // 生成性能报告
    eprintln!(
        "Macro '{}' expansion: {:?}",
        "report_perf",
        duration
    );
    
    if duration.as_millis() > 100 {
        eprintln!("⚠️  Warning: Slow macro expansion detected!");
    }
    
    output.into()
}
```

---

## 优化清单

### ✅ TokenStream优化

- [ ] 避免重复解析
- [ ] 使用延迟解析
- [ ] 优化quote使用
- [ ] 减少TokenStream克隆

### ✅ 依赖优化

- [ ] 最小化syn features
- [ ] 使用可选依赖
- [ ] 分离编译单元
- [ ] 特征门控

### ✅ 编译优化

- [ ] 启用增量编译
- [ ] 使用编译缓存
- [ ] 并行编译
- [ ] LTO优化

### ✅ 代码质量

- [ ] 性能基准测试
- [ ] 编译时间监控
- [ ] 文档化优化
- [ ] 持续性能回归测试

---

## 实际案例

### Case 1: Serde性能优化

Serde通过以下方式优化性能：

1. **精确导入**: 只导入需要的syn features
2. **缓存重用**: 缓存常见类型的展开结果
3. **增量友好**: 避免不必要的依赖
4. **特征分层**: 将功能分为多个features

**结果**: 编译时间减少30-40%

---

### Case 2: Tokio宏优化

Tokio宏优化策略：

1. **简化AST**: 只解析必要的结构
2. **预计算**: 编译时计算常量
3. **分离实现**: proc-macro只做转发
4. **文档测试**: 避免在文档中过度使用宏

**结果**: 增量编译速度提升50%

---

## 总结

宏性能优化的关键：

- ⚡ **分析为先**: 使用工具定位瓶颈
- 🎯 **精确依赖**: 最小化依赖范围
- 🔄 **增量友好**: 支持增量编译
- 📊 **持续监控**: 建立性能基准

---

## 相关文档

- [宏元编程](./macro_metaprogramming.md)
- [TokenStream详解](../03_procedural/05_token_streams.md)
- [最佳实践](../05_practice/02_best_practices.md)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20

## 返回导航

- [返回高级主题](README.md)
- [返回主索引](../00_MASTER_INDEX.md)
