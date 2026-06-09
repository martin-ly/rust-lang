# `-C jump-tables=bool` 编译器优化指南

> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **稳定版本**: Rust 1.93.0（原 `-Zno-jump-tables`），1.96.0+ 持续可用
> **适用版本**: 1.93.0+ (MSRV 1.96.0)
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

---

## 目录

- [`-C jump-tables=bool` 编译器优化指南](#-c-jump-tablesbool-编译器优化指南)
  - [目录](#目录)
  - [一、什么是跳转表 (Jump Tables)](#一什么是跳转表-jump-tables)
    - [工作原理](#工作原理)
    - [跳转表的优缺点](#跳转表的优缺点)
  - [二、`-C jump-tables=bool` 语法](#二-c-jump-tablesbool-语法)
    - [配置位置](#配置位置)
  - [三、使用场景](#三使用场景)
    - [场景 1：Spectre 缓解](#场景-1spectre-缓解)
    - [场景 2：分支预测优化](#场景-2分支预测优化)
    - [场景 3：嵌入式系统](#场景-3嵌入式系统)
  - [四、对性能的影响](#四对性能的影响)
    - [基准测试建议](#基准测试建议)
    - [典型结果](#典型结果)
  - [五、常见配置模式](#五常见配置模式)
    - [模式 1：安全关键构建](#模式-1安全关键构建)
    - [模式 2：与 PGO 配合](#模式-2与-pgo-配合)
    - [模式 3：条件编译中的选择](#模式-3条件编译中的选择)
  - [六、参考](#六参考)
    - [相关文档](#相关文档)

---

## 一、什么是跳转表 (Jump Tables)

> **[来源: Rust Compiler Documentation]**
> **[来源: Wikipedia - Branch Table]**

**跳转表 (Jump Table)** 是编译器优化 `match` / `switch` 语句的一种技术。
当分支较多且条件值密集时，编译器会生成一个指针数组（表），通过索引直接跳转到对应的分支代码，而不是逐一比较。

### 工作原理

```rust
match opcode {
    0 => add(),
    1 => sub(),
    2 => mul(),
    3 => div(),
    _ => unknown(),
}
```

**使用跳转表**：

```asm
; 通过 opcode 索引跳转表
lea rax, [jump_table]
jmp [rax + rdi * 8]

jump_table:
    dq add
    dq sub
    dq mul
    dq div
```

**不使用跳转表（线性比较）**：

```asm
cmp rdi, 0
je add
cmp rdi, 1
je sub
cmp rdi, 2
je mul
; ...
```

### 跳转表的优缺点

| 维度 | 使用跳转表 | 不使用跳转表 |
|------|-----------|-------------|
| **分支预测** | 间接跳转，预测困难 | 条件跳转，预测较易 |
| **代码大小** | 紧凑（密集分支） | 可能较大 |
| **Spectre 安全** | 易受 Spectre v2 影响 | 相对安全 |
| **cache 友好性** | 需要读取跳转表 | 顺序执行 |

---

## 二、`-C jump-tables=bool` 语法

Rust 1.93.0 将 `-Zno-jump-tables` 稳定化为 `-C jump-tables=bool`：

```bash
# 启用跳转表（默认）
rustc -C jump-tables=true src/main.rs

# 禁用跳转表
rustc -C jump-tables=false src/main.rs
```

### 配置位置

| 位置 | 示例 |
|------|------|
| 命令行 | `rustc -C jump-tables=false ...` |
| Cargo | `RUSTFLAGS="-C jump-tables=false" cargo build` |
| `.cargo/config.toml` | `[build] rustflags = ["-C", "jump-tables=false"]` |

---

## 三、使用场景

### 场景 1：Spectre 缓解

在高度安全敏感的环境中，禁用跳转表可减少 Spectre v2（分支目标注入）攻击面：

```bash
# 安全关键构建
RUSTFLAGS="-C jump-tables=false" cargo build --release
```

### 场景 2：分支预测优化

当 `match` 的分支值分布不均匀（少数高频分支），线性比较配合分支预测可能优于跳转表：

```rust
// 高频分支在前，低频在后
match error_code {
    0 => "OK",           // 90% 概率
    1 => "NotFound",     // 8% 概率
    2 => "Permission",   // 1% 概率
    // ... 其他极少出现
}
```

```bash
# 测试禁用跳转表后的性能
RUSTFLAGS="-C jump-tables=false" cargo bench
```

### 场景 3：嵌入式系统

资源受限的嵌入式系统可能希望禁用跳转表以节省代码空间或避免间接跳转的开销：

```toml
# .cargo/config.toml (嵌入式)
[target.thumbv7em-none-eabihf]
rustflags = ["-C", "jump-tables=false"]
```

---

## 四、对性能的影响

### 基准测试建议

```bash
# 1. 默认配置（启用跳转表）
cargo bench -- baseline

# 2. 禁用跳转表
RUSTFLAGS="-C jump-tables=false" cargo bench -- no-jt

# 3. 对比结果
cargo bench -- baseline no-jt
```

### 典型结果

| 场景 | 启用跳转表 | 禁用跳转表 |
|------|-----------|-----------|
| 密集 `match`（如字节码解释器） | 通常更快 | 可能慢 5-15% |
| 稀疏 `match`（如错误码处理） | 可能更慢 | 可能更快 |
| 安全关键代码 | 标准 | 减少 Spectre 风险 |

---

## 五、常见配置模式

### 模式 1：安全关键构建

```toml
# Cargo.toml
[profile.security-critical]
inherits = "release"
rustflags = ["-C", "jump-tables=false", "-C", "opt-level=3"]
```

### 模式 2：与 PGO 配合

```bash
# 1. 训练阶段（默认配置收集 profile）
cargo build --release
./target/release/app --training-data

# 2. 最终构建（根据 profile 决定）
# 通常 PGO 会自动处理跳转表优化，无需手动干预
```

### 模式 3：条件编译中的选择

```rust
#[cfg(feature = "no-jump-tables")]
const _: () = {
    // 编译时提示
    println!("cargo:rustc-env=RUSTFLAGS=-C jump-tables=false");
};
```

---

## 六、参考

> **[来源: Rust Compiler Documentation]**
> **[来源: LLVM Documentation]**

| 资源 | 链接 |
|------|------|
| Rust 1.93.0 Release Notes | <https://releases.rs/docs/1.93.0/> |
| rustc 代码生成选项 | <https://doc.rust-lang.org/rustc/codegen-options/index.html> |
| Spectre v2 缓解 | <https://spectreattack.com/> |
| LLVM Jump Tables | <https://llvm.org/docs/LangRef.html> |

### 相关文档

- [Rust 1.93 特性速查表](../02_reference/quick_reference/02_rust_190_to_193_features_cheatsheet.md)
- [Rust 版本跟踪](../../concept/07_future/05_rust_version_tracking.md)
- [性能调优指南](../05_guides/05_performance_tuning_guide.md)
