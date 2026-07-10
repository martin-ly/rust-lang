# Rust 1.97.0 内容对齐完成报告

**日期**: 2026-07-11
**分析范围**: 项目 `concept/07_future/00_version_tracking/rust_1_97_stabilized.md`、`crates/*/src/rust_197_features.rs` 与权威来源对比
**状态**: ✅ 已完成 Rust 1.97.0 全项目内容对齐，9 大质量门全部通过
**权威来源**:

- [Rust 1.97.0 Release Blog](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/)
- [releases.rs 1.97.0](https://releases.rs/docs/1.97.0/)
- [Rust Standard Library Docs](https://doc.rust-lang.org/std/)
- [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)

---

## 1. 执行摘要

项目已完成 Rust 1.97.0 的全部内容对齐工作：

1. ✅ **Symbol mangling v0** 已在 `rust_1_97_stabilized.md` 中新增独立章节（§2.7），包含迁移建议与 debugger/profiler 影响说明。
2. ✅ **Linker output no longer hidden** 已在 `rust_1_97_stabilized.md` 中新增独立章节（§2.8），明确说明 `linker_messages` 是**不受 `warnings` lint group 控制的特殊 lint**。
3. ✅ **Cargo `build.warnings`** 已补充 `CARGO_BUILD_WARNINGS` 环境变量、仅作用于 local packages、与 `--keep-going` 组合的 CI 模板。
4. ✅ **NonZero 位查询方法** 的返回类型已修正：`bit_width()` 返回 `NonZero<u32>`，示例已改为 `.get()`。
5. ✅ 所有 `rust_197_features.rs` 模块已完成重构：移除 `#[cfg(nightly)]` 分支，直接调用 Rust 1.97.0 stable API；1.98+ 预览内容已迁移至 `rust_198_features.rs`。
6. ✅ **"fallback `{float}` to `f32`"** 语言变化已在 `rust_1_97_stabilized.md` §2.6 中补充。

---

## 2. 权威特性清单（来源：blog + releases.rs）

| # | 特性 | 分类 | 项目状态 |
|---|------|------|----------|
| 1 | Symbol mangling v0 enabled by default | Compiler | ✅ 已独立成节 |
| 2 | Cargo `build.warnings` config | Cargo | ✅ 已覆盖完整语义 |
| 3 | Linker output no longer hidden (`linker_messages` lint) | Compiler | ✅ 已独立成节 |
| 4 | `Default for RepeatN` | Std API | ✅ 已覆盖 |
| 5 | `Copy for ffi::FromBytesUntilNulError` | Std API | ✅ 已覆盖 |
| 6 | `Send for std::fs::File` on UEFI | Std API | ✅ 已覆盖 |
| 7 | `<{integer}>::isolate_highest_one` / `isolate_lowest_one` / `highest_one` / `lowest_one` / `bit_width` | Std API | ✅ 已覆盖 |
| 8 | `NonZero<{integer}>::isolate_highest_one` / `isolate_lowest_one` / `highest_one` / `lowest_one` / `bit_width` | Std API | ✅ 已覆盖，返回类型已修正 |
| 9 | `char::is_control` const stable | Std API | ✅ 已覆盖 |
| 10 | `must_use` on `Result<T, !>` / `ControlFlow<!, T>` | Language | ✅ 已覆盖 |
| 11 | `dead_code_pub_in_binary` lint | Language | ✅ 已覆盖 |
| 12 | `div32`, `lam-bh`, `lamcas`, `ld-seq-sa`, `scq` target features | Language | ✅ 已覆盖 |
| 13 | `cfg(target_has_atomic_primitive_alignment)` | Language | ✅ 已覆盖 |
| 14 | Allow trailing `self` in imports | Language | ✅ 已覆盖 |
| 15 | nvptx64-nvidia-cuda baseline update | Platform | ✅ 已覆盖 |
| 16 | Cargo `resolver.lockfile-path` | Cargo | ✅ 已覆盖 |
| 17 | `cargo clean --target-dir` validation | Cargo | ✅ 已覆盖 |
| 18 | `cargo -m` shorthand | Cargo | ✅ 已覆盖 |
| 19 | `crates-io` remove `curl` dependency | Cargo | ✅ 已覆盖 |
| 20 | Rustdoc `--emit` / `--remap-path-prefix` | Rustdoc | ✅ 已覆盖 |
| 21 | `pin!` blocks deref coercions | Compatibility | ✅ 已覆盖 |
| 22 | Empty `#[export_name]` rejected | Compatibility | ✅ 已覆盖 |
| 23 | `f32: From<{float}>` future compat warning | Compatibility | ✅ 已覆盖 |
| 24 | `WSAESHUTDOWN` → `BrokenPipe` on Windows | Compatibility | ✅ 已覆盖 |
| 25 | Fallback `{float}` to `f32` in some cases | Language | ✅ 已覆盖 |
| 26 | `std::char` constants/functions deprecated | Compatibility | ✅ 已覆盖 |
| 27 | `varargs_without_pattern` lint in deps | Compatibility | ✅ 已覆盖 |
| 28 | Reject generic args to module path segments | Compatibility | ✅ 已覆盖 |
| 29 | Invalid macho `link_section` error | Compatibility | ✅ 已覆盖 |
| 30 | Certain `enum` encodings changed | Compatibility | ✅ 已覆盖 |
| 31 | Validate `#[link_name]` / `#[link(name)]` | Compatibility | ✅ 已覆盖 |

---

## 3. 关键修复详情

### 3.1 `rust_197_features.rs` 重构

所有 `crates/*/src/rust_197_features.rs` 文件已完成重构：

- 移除了所有 `#[cfg(nightly)]` / `#[cfg(not(nightly))]` 分支。
- Rust 1.97.0 已稳定的 API 直接调用。
- 1.98+ 预览内容迁移到同目录 `rust_198_features.rs`。
- 例外：`Box::as_ptr` 经验证在 Rust 1.97.0 stable 仍为 nightly-only（`feature box_as_ptr`），未在 `rust_197_features.rs` 中直接调用；相关演示保留在 `rust_198_features.rs`。

受影响的 crate 包括：c01-c04、c05-c07、c08_algorithms、c09-c12、c13_embedded、common 等。

### 3.2 `rust_1_97_stabilized.md` 内容补齐

| 章节 | 内容 | 状态 |
|------|------|------|
| §2.6 | `{float}` 在未约束时回退到 `f32` | ✅ 新增，含代码示例与迁移建议 |
| §2.7 | v0 symbol mangling 默认启用 | ✅ 新增独立章节，含 debugger/profiler 影响与迁移表格 |
| §2.8 | 链接器输出默认显示 (`linker_messages` lint) | ✅ 新增独立章节，明确不受 `warnings` group 控制 |
| §5.1 | Cargo `build.warnings` | ✅ 补充 `CARGO_BUILD_WARNINGS`、local-only 语义、`--keep-going` 模板 |
| §4.5 | NonZero 位查询 | ✅ 返回类型修正为 `NonZero<u32>`，示例改为 `.get()` |

---

## 4. 质量门验证结果

运行 `bash scripts/run_quality_gates.sh`，全部 9 大质量门通过：

1. ✅ `cargo check --workspace`
2. ✅ `cargo test --workspace --quiet`
3. ✅ `cargo clippy --workspace -- -D warnings`
4. ✅ `cargo audit --no-fetch`
5. ✅ `cargo vet --locked`
6. ✅ `mdbook build`
7. ✅ `python scripts/kb_auditor.py --link-check`（死链 0，跨层问题 0）
8. ✅ `python scripts/detect_content_overlap.py`（潜在重复 0）
9. ✅ `python scripts/add_bilingual_annotations.py --mode check-only`（缺少 EN/Summary 0，未覆盖术语 0）

> 注：`proc-macro-error2 v2.0.1` 报告 future-incompat 警告，这是上游依赖问题，不影响当前构建与质量门结果。

---

## 5. 结论

Rust 1.97.0 全项目内容对齐已完成。项目文档、代码示例、crate 实现均与 Rust 1.97.0 stable 权威来源保持一致，所有 CI 质量门均已通过。
