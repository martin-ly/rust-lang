# Rust 1.97 特性速查表 {#rust-197-特性速查表}

> **EN**: Rust 1.97 Features Cheatsheet
> **Summary**: Rust 1.97.0（2026-07-09 stable）特性速查。完整说明与代码示例参见 `concept/07_future/00_version_tracking/rust_1_97_stabilized.md`。
> **权威来源**: [`concept/07_future/00_version_tracking/rust_1_97_stabilized.md`](../../../concept/07_future/00_version_tracking/rust_1_97_stabilized.md)
>
> **分级**: [A]
> **Bloom 层级**: L2
> **版本**: Rust 1.97.0
> **更新日期**: 2026-07-10
> **适用版本**: stable 1.97.0+
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [参考级]

---

## 语言

| 特性 | 说明 |
|:---|:---|
| `must_use` 扩展 | `Result<T, Uninhabited>` / `ControlFlow<Uninhabited, T>` 等价于 `T` 触发 `must_use` |
| `dead_code_pub_in_binary` | 新增 allow-by-default lint，标记二进制中未使用的 `pub` 条目 |
| target features | `div32`、`lam-bh`、`lamcas`、`ld-seq-sa`、`scq` 稳定 |
| `cfg(target_has_atomic_primitive_alignment)` | 检测原子类型与原始整数类型对齐是否相等 |
| import `self` 放宽 | 更多场景允许 trailing `self` |

## 标准库

| 特性 | 说明 |
|:---|:---|
| `Default for RepeatN` | `std::iter::RepeatN` 可默认构造为空迭代器 |
| `Copy for ffi::FromBytesUntilNulError` | 该错误类型可复制 |
| `Send for std::fs::File` on UEFI | UEFI 目标上的 `File` 实现 `Send` |
| 整数位查询 | `isolate_highest_one` / `isolate_lowest_one` / `highest_one` / `lowest_one` / `bit_width` |
| `NonZero` 位查询 | 与整数类型对应的位操作方法 |
| `char::is_control` const | 控制字符判断可在 `const` 上下文使用 |

## 平台

| 特性 | 说明 |
|:---|:---|
| `nvptx64-nvidia-cuda` 基线提升 | 最低 SM 从 Maxwell/Pascal 提升至 Volta（sm_70），PTX ISA 6.0 → 7.0 |

## Cargo

| 特性 | 说明 |
|:---|:---|
| `build.warnings` | 统一控制本地包 lint 警告级别（如 `deny`） |
| `resolver.lockfile-path` | 指定 lockfile 路径 |
| `cargo clean --target-dir` | 对非 Cargo target 目录报错 |
| `-m` | `cargo --manifest-path` 的简写 |
| `crates-io` | 移除 `curl` 依赖 |

## Rustdoc

| 特性 | 说明 |
|:---|:---|
| `--emit` | 输出格式控制稳定 |
| `--remap-path-prefix` | 路径前缀替换稳定 |

## 兼容性注意

- v0 symbol mangling 默认启用。
- `pin!` 阻止隐式 deref coercion。
- 空 `#[export_name = ""]` 报错。
- `std::char` 常量与函数被弃用。
- Windows `WSAESHUTDOWN` 映射为 `io::ErrorKind::BrokenPipe`。

---

> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-10
> **状态**: ✅ 已对齐 Rust 1.97.0 stable
