# cargo-fuzz 模糊测试入门指南

> 本文档对应 Rust 生产级工程实践体系阶段三 —— 模糊测试。
> 参考: Google OSS-Fuzz、Cloudflare 模糊测试实践、Rust Fuzzing Book。

---

## 1. 什么是模糊测试（Fuzzing）？

模糊测试是一种自动化的软件测试技术，通过向程序输入大量随机或半随机的数据，来发现崩溃、断言失败、内存错误等异常行为。

### 为什么 Rust 需要 Fuzzing？

Rust 的所有权系统防止了大部分内存安全问题，但以下场景仍可能出现问题：

| 场景 | 风险 |
|-----|------|
| `unsafe` 代码块 | 原始指针操作可能导致越界、use-after-free |
| 解析外部输入（文件、网络数据） | 逻辑错误、 panic、无限循环 |
| 复杂算法实现 | 边界条件处理不当 |
| 与 C 代码的 FFI 交互 | 调用约定不匹配、内存管理错误 |

> **Cloudflare 实践**: 在其 Rust 解析器（如 wirefilter）中广泛使用 fuzzing 发现边缘 case。

---

## 2. 工具链安装

```bash
# 安装 cargo-fuzz（需要 nightly Rust）
cargo install cargo-fuzz --locked

# 验证安装
cargo fuzz --version
```

> **注意**: cargo-fuzz 目前需要 nightly 工具链。如果当前环境无法安装，标记为 "待 CI 验证"。

---

## 3. 快速开始

### 初始化 fuzz 项目

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

### 编写 Fuzz Target

```rust
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

### 运行 Fuzzer

```bash
# 运行特定的 fuzz target
cargo fuzz run sort_fuzzer

# 设置超时（秒）
cargo fuzz run sort_fuzzer -- -max_total_time=300

# 使用多个 job 并行
cargo fuzz run sort_fuzzer -- -jobs=4 -workers=4

# 从已有的 corpus 继续
cargo fuzz run sort_fuzzer corpus/
```

---

## 4. 本项目 Fuzz Target

### c08_algorithms —— 解析器模糊测试

`fuzz/src/parser_fuzzer.rs`:

```rust
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

### 注册到 fuzz/Cargo.toml

```toml
[[bin]]
name = "parser_fuzzer"
path = "src/parser_fuzzer.rs"
test = false
doc = false
```

---

## 5. 高级技巧

### 结构化 Fuzzing

对于需要结构化输入的场景：

```rust
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

### 与 Miri 结合

```bash
# 先用 fuzzer 找到崩溃输入，再用 Miri 分析根本原因
cargo fuzz run target_name
# 崩溃后，corpus 目录会保存触发崩溃的输入
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test -- crash_input
```

### 覆盖率引导

```bash
# 生成覆盖率报告
cargo fuzz coverage target_name
# 输出在 fuzz/coverage/
```

---

## 6. CI 集成

```yaml
# .github/workflows/fuzzing.yml（片段）
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

## 7. 参考资源

- [Rust Fuzzing Book](https://rust-fuzz.github.io/book/)
- [cargo-fuzz 仓库](https://github.com/rust-fuzz/cargo-fuzz)
- [libFuzzer 文档](https://llvm.org/docs/LibFuzzer.html)
- [Google OSS-Fuzz](https://google.github.io/oss-fuzz/)
- [Cloudflare 模糊测试实践](https://blog.cloudflare.com/fuzzing-rust/)
