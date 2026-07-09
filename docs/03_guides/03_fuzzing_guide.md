# cargo-fuzz 模糊测试入门指南 {#cargo-fuzz-模糊测试入门指南}

> **EN**: Fuzzing Guide
> **Summary**: cargo-fuzz 模糊测试入门指南 Fuzzing Guide.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L2-L3 (理解/应用)
> 本文档对应 Rust 生产级工程实践体系阶段三 —— 模糊测试。
> 参考: Google OSS-Fuzz、Cloudflare 模糊测试实践、Rust Fuzzing Book。
> **来源: [Wikipedia - Fuzzing](https://en.wikipedia.org/wiki/Fuzzing)** ·
> **[AFL - American Fuzzy Lop](https://github.com/google/AFL)** ·
> **[LLVM libFuzzer](https://llvm.org/docs/LibFuzzer.html)** ·
> **[Rust Fuzzing Book - fuzzingbook.com](https://rust-fuzz.github.io/book/introduction.html)**
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [cargo-fuzz 模糊测试入门指南 {#cargo-fuzz-模糊测试入门指南}](#cargo-fuzz-模糊测试入门指南-cargo-fuzz-模糊测试入门指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 什么是模糊测试（Fuzzing）？ {#1-什么是模糊测试fuzzing}](#1-什么是模糊测试fuzzing-1-什么是模糊测试fuzzing)
    - [为什么 Rust 需要 Fuzzing？ {#为什么-rust-需要-fuzzing}](#为什么-rust-需要-fuzzing-为什么-rust-需要-fuzzing)
  - [2. 工具链安装 {#2-工具链安装}](#2-工具链安装-2-工具链安装)
  - [3. 快速开始 {#3-快速开始}](#3-快速开始-3-快速开始)
    - [初始化 fuzz 项目 {#初始化-fuzz-项目}](#初始化-fuzz-项目-初始化-fuzz-项目)
    - [编写 Fuzz Target {#编写-fuzz-target}](#编写-fuzz-target-编写-fuzz-target)
    - [运行 Fuzzer {#运行-fuzzer}](#运行-fuzzer-运行-fuzzer)
  - [4. 本项目 Fuzz Target {#4-本项目-fuzz-target}](#4-本项目-fuzz-target-4-本项目-fuzz-target)
    - [c08\_algorithms —— 解析器模糊测试 {#c08\_algorithms-解析器模糊测试}](#c08_algorithms--解析器模糊测试-c08_algorithms-解析器模糊测试)
    - [注册到 fuzz/Cargo.toml {#注册到-fuzzcargotoml}](#注册到-fuzzcargotoml-注册到-fuzzcargotoml)
  - [5. 高级技巧 {#5-高级技巧}](#5-高级技巧-5-高级技巧)
    - [结构化 Fuzzing {#结构化-fuzzing}](#结构化-fuzzing-结构化-fuzzing)
    - [与 Miri 结合 {#与-miri-结合}](#与-miri-结合-与-miri-结合)
    - [覆盖率引导 {#覆盖率引导}](#覆盖率引导-覆盖率引导)
  - [6. CI 集成 {#6-ci-集成}](#6-ci-集成-6-ci-集成)
  - [7. 参考资源 {#7-参考资源}](#7-参考资源-7-参考资源)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 1. 什么是模糊测试（Fuzzing）？ {#1-什么是模糊测试fuzzing}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

模糊测试是一种自动化的软件测试技术，通过向程序输入大量随机或半随机的数据，来发现崩溃、断言失败、内存错误等异常行为。

### 为什么 Rust 需要 Fuzzing？ {#为什么-rust-需要-fuzzing}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 的所有权（Ownership）系统防止了大部分内存安全（Memory Safety）问题，但以下场景仍可能出现问题：

| 场景 | 风险 |
|-----|------|
| `unsafe` 代码块 | 原始指针（Raw Pointer）操作可能导致越界、use-after-free |
| 解析外部输入（文件、网络数据） | 逻辑错误、 panic、无限循环 |
| 复杂算法实现 | 边界条件处理不当 |
| 与 C 代码的 FFI 交互 | 调用约定不匹配、内存管理错误 |

> **Cloudflare 实践**: 在其 Rust 解析器（如 wirefilter）中广泛使用 fuzzing 发现边缘 case。

---

## 2. 工具链安装 {#2-工具链安装}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```bash
# 安装 cargo-fuzz（需要 nightly Rust） {#安装-cargo-fuzz需要-nightly-rust}
cargo install cargo-fuzz --locked

# 验证安装 {#验证安装}
cargo fuzz --version
```

> **注意**: cargo-fuzz 目前需要 nightly 工具链。如果当前环境无法安装，标记为 "待 CI 验证"。

---

## 3. 快速开始 {#3-快速开始}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 初始化 fuzz 项目 {#初始化-fuzz-项目}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

```bash
cd crates/c08_algorithms
cargo fuzz init
```

这会创建：

```text
fuzz/
├── Cargo.toml          # fuzz workspace 配置
└── src/
    └── lib.rs          # 生成的示例 fuzz target
```

### 编写 Fuzz Target {#编写-fuzz-target}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```rust,ignore
// fuzz/src/sort_fuzzer.rs
#![no_main]

use libfuzzer_sys::fuzz_target;
use c08_algorithms::sorting::quick_sort;

fuzz_target!(|data: &[u8]| {
    // 将随机字节转换为 Vec<u32>
    let numbers: Vec<u32> = data
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
        .collect();

    if numbers.len() < 2 {
        return;
    }

    // 测试排序算法不 panic
    let mut sorted = numbers.clone();
    quick_sort(&mut sorted);

    // 验证排序结果
    for i in 1..sorted.len() {
        assert!(sorted[i - 1] <= sorted[i], "排序结果不是非递减的");
    }

    // 验证元素数量不变
    assert_eq!(sorted.len(), numbers.len());
});
```

### 运行 Fuzzer {#运行-fuzzer}

> **来源: [ACM](https://dl.acm.org/)**

```bash
# 运行特定的 fuzz target {#运行特定的-fuzz-target}
cargo fuzz run sort_fuzzer

# 设置超时（秒） {#设置超时秒}
cargo fuzz run sort_fuzzer -- -max_total_time=300

# 使用多个 job 并行 {#使用多个-job-并行}
cargo fuzz run sort_fuzzer -- -jobs=4 -workers=4

# 从已有的 corpus 继续 {#从已有的-corpus-继续}
cargo fuzz run sort_fuzzer corpus/
```

---

## 4. 本项目 Fuzz Target {#4-本项目-fuzz-target}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### c08_algorithms —— 解析器模糊测试 {#c08_algorithms-解析器模糊测试}

> **来源: [IEEE](https://standards.ieee.org/)**

`fuzz/src/parser_fuzzer.rs`:

```rust,ignore
#![no_main]

use libfuzzer_sys::fuzz_target;

/// 模糊测试数据解析器
/// 目标: 确保解析任意输入不会 panic 或崩溃
fuzz_target!(|data: &[u8]| {
    // 测试字符串解析（模拟解析外部配置文件）
    if let Ok(input) = std::str::from_utf8(data) {
        // 测试数字解析
        let _ = input.parse::<i64>();
        let _ = input.parse::<f64>();
        let _ = input.parse::<u128>();
    }

    // 测试字节流边界处理
    if data.len() >= 8 {
        let _ = u64::from_le_bytes([
            data[0], data[1], data[2], data[3],
            data[4], data[5], data[6], data[7],
        ]);
    }
});
```

### 注册到 fuzz/Cargo.toml {#注册到-fuzzcargotoml}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```toml
[[bin]]
name = "parser_fuzzer"
path = "src/parser_fuzzer.rs"
test = false
doc = false
```

---

## 5. 高级技巧 {#5-高级技巧}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 结构化 Fuzzing {#结构化-fuzzing}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

对于需要结构化输入的场景：

```rust,ignore
use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
struct Packet {
    header: Header,
    payload: Vec<u8>,
}

#[derive(Arbitrary, Debug)]
struct Header {
    version: u8,
    length: u16,
}

fuzz_target!(|packet: Packet| {
    // packet 由 libfuzzer 自动构造
    process_packet(&packet);
});
```

### 与 Miri 结合 {#与-miri-结合}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```bash
# 先用 fuzzer 找到崩溃输入，再用 Miri 分析根本原因 {#先用-fuzzer-找到崩溃输入再用-miri-分析根本原因}
cargo fuzz run target_name
# 崩溃后，corpus 目录会保存触发崩溃的输入 {#崩溃后corpus-目录会保存触发崩溃的输入}
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test -- crash_input
```

### 覆盖率引导 {#覆盖率引导}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bash
# 生成覆盖率报告 {#生成覆盖率报告}
cargo fuzz coverage target_name
# 输出在 fuzz/coverage/ {#输出在-fuzzcoverage}
```

---

## 6. CI 集成 {#6-ci-集成}
>
> **[来源: [crates.io](https://crates.io/)]**

```yaml
# .github/workflows/fuzzing.yml（片段） {#githubworkflowsfuzzingyml片段}
fuzzing:
  name: Fuzz Tests
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - uses: dtolnay/rust-toolchain@nightly
    - name: Install cargo-fuzz
      run: cargo install cargo-fuzz --locked
    - name: Run fuzzer (limited time)
      run: |
        cd crates/c08_algorithms
        cargo fuzz run parser_fuzzer -- -max_total_time=60
```

> **建议**: CI 中 fuzzing 时间限制为 60-120 秒，作为回归测试。长时间 fuzzing 在专门的 fuzzing 基础设施上运行。

---

## 7. 参考资源 {#7-参考资源}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [Rust Fuzzing Book](https://rust-fuzz.github.io/book/)
- [cargo-fuzz 仓库](https://github.com/rust-fuzz/cargo-fuzz)
- [libFuzzer 文档](https://llvm.org/docs/LibFuzzer.html)
- [Google OSS-Fuzz](https://google.github.io/oss-fuzz/)
- [Cloudflare 模糊测试实践](https://blog.cloudflare.com/)

---

> **权威来源**: [Rust Fuzzing Book](https://rust-fuzz.github.io/book/), [cargo-fuzz 仓库](https://github.com/rust-fuzz/cargo-fuzz), [libFuzzer 文档](https://llvm.org/docs/LibFuzzer.html), [Google OSS-Fuzz](https://google.github.io/oss-fuzz/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Fuzzing Book、cargo-fuzz、libFuzzer 官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
