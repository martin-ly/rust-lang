# Rust 1.98.0 稳定特性

> **EN**: Rust 1.98.0 Stabilized Features
> **Summary**: Rust 1.98.0 于 2026-08-20 进入 stable 通道。本文档按官方发布笔记汇总已稳定的语言、标准库、Cargo、Rustdoc 与目标平台变更；2026-07-16 起基于 1.98.0 beta 实测预填充，稳定发布后最终核对。
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [综述级]
> **权威来源**: 本文件为 `concept/` 权威页（Rust 1.98 稳定特性的 canonical 汇总；稳定生效日为 2026-08-20，此前以 [`rust_1_98_preview.md`](rust_1_98_preview.md) 为周期跟踪入口）。
> **Rust 版本**: **1.98.0 stable**（预计 2026-08-20；当前基于 beta 分支实测）
> **最后更新**: 2026-07-16
> **状态**: 🧪 **beta 已冻结，stable 前预填充**；1.98.0 已于 2026-07-03 分支进入 beta
>
> **权威来源**:
>
> · [Rust 1.98.0 Release Notes (beta)](https://releases.rs/docs/1.98.0/) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [RFC Book](https://rust-lang.github.io/rfcs/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
> **后置概念**: [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md) · [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)

---

## 0. 1.98 特性矩阵

> **状态图例**：✅ = 已稳定（beta 实测或 release notes 确认） · 🧪 = RFC 已合并/实现跟踪中 · ⏳ = nightly/FCP 未排期

| # | 特性 | 1.98.0 状态 | 稳定后归属节 | 跟踪链接 |
|:---:|:---|:---|:---|:---|
| 1 | `Panic[Hook]Info` 中 `Location<'_>` 生命周期改为 `'static` | ✅ stabilized in 1.98 beta | §1.1 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 2 | mingw-w64 C 工具链更新 | ✅ stabilized in 1.98 beta | §1.2 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 3 | 移除 Solaris 上 `File::lock` 实现（语义错误） | ✅ stabilized in 1.98 beta | §1.3 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 4 | 移除 `-Zemscripten-wasm-eh` | ✅ stabilized in 1.98 beta | §1.4 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 5 | Named `Fn` trait parameters（RFC #3955） | 🧪 RFC merged（2026-07-08） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3955-named-fn-trait-parameters.html) |
| 6 | `#![register_{attribute,lint}_tool]`（RFC #3808） | 🧪 RFC merged（2026-06-10） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3808-register-tool.html) |
| 7 | `todo!()` 不再触发 `unreachable_code`（RFC #3928） | 🧪 RFC merged（2026-06-25） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3928-todo-overreach.html) |
| 8 | Public/Private Dependencies（RFC #3516） | 🧪 RFC merged，Cargo 实现跟踪中 | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3516-public-private-dependencies.html) |
| 9 | Safety Tags（RFC #3842） | ⏳ FCP / 讨论中 | §3 | [rfcs#3842](https://github.com/rust-lang/rfcs/pull/3842) |
| 10 | Pin Ergonomics（`&pin mut` / `&pin const`） | ⏳ nightly only | §4 | [预览页](../02_preview_features/14_pin_ergonomics_preview.md) |
| 11 | Async Drop | ⏳ nightly only | §4 | [预览页](../02_preview_features/22_async_drop_preview.md) |
| 12 | Return Type Notation（RTN） | ⏳ nightly only | §4 | [预览页](../02_preview_features/09_return_type_notation_preview.md) |

---

## 1. stabilized-in-beta 特性（4 项，随 1.98.0 稳定）

以下 4 项已随 1.98.0 beta 分支（2026-07-03 切分）合入，将于 2026-08-20 转 stable。

### 1.1 `Panic[Hook]Info` 中 `Location<'_>` 生命周期改为 `'static`

**状态**: ✅ stabilized in 1.98 beta（2026-08-20 转正）
**来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)
**相关概念**: [panic 与 abort](../../01_foundation/08_error_handling/03_panic_and_abort.md) · [生命周期](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)

#### 变更动机

`std::panic::PanicHookInfo`（旧名 `PanicInfo`）的 `location()` 方法原先返回 `Option<&Location<'_>>`，其中 `Location` 的生命周期与 `PanicHookInfo` 借用绑定。这导致自定义 panic hook 难以把 `Location` 存储到 `'static` 上下文（如日志队列、全局状态）。

1.98.0 将返回类型改为 `Option<&'static Location<'static>>`，使 panic 位置信息本身具有 `'static` 生命周期，便于跨线程传递和长期存储。

#### 迁移影响

- 已有代码若显式标注 `Location<'_>` 生命周期，需要更新为 `'static`。
- 大多数仅打印 `location()` 的代码无需改动。

#### 示例

```rust,ignore
use std::panic;

panic::set_hook(Box::new(|info| {
    if let Some(loc) = info.location() {
        // Rust 1.98+: loc 是 &'static Location<'static>
        log_static(loc);
    }
}));

fn log_static(loc: &'static std::panic::Location<'static>) {
    // 可安全存入全局日志队列
    eprintln!("panic at {}:{}", loc.file(), loc.line());
}
```

#### 迁移注意

```rust,ignore
// 假设旧代码显式依赖 Location<'_>
fn old_hook(info: &std::panic::PanicHookInfo) {
    let loc: Option<&std::panic::Location<'_>> = info.location();
    // Rust 1.98+ 下 info.location() 实际返回 Option<&'static Location<'static>>，
    // 此显式标注仍可通过编译，但无法把 loc 当作 'static 使用；
    // 若需要 'static，直接省略显式生命周期让类型自行推断即可。
}
```

### 1.2 mingw-w64 C 工具链更新

**状态**: ✅ stabilized in 1.98 beta（2026-08-20 转正）
**来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)
**相关概念**: [工具链](../../06_ecosystem/00_toolchain/01_toolchain.md) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

#### 变更内容

Rust 1.98.0 更新了 Windows GNU 目标（`x86_64-pc-windows-gnu`、`i686-pc-windows-gnu`）捆绑的 mingw-w64/GCC 工具链版本。主要影响：

- 链接行为更贴近上游 mingw-w64 当前版本；
- 异常模型（SEH vs DWARF）与 C++ ABI 兼容性改善；
- 部分旧版 Windows 下的边缘行为可能变化。

#### 迁移检查清单

- [ ] 在 `x86_64-pc-windows-gnu` 目标上重新运行 CI；
- [ ] 检查 C/C++ 依赖的链接是否仍通过；
- [ ] 若使用自定义 mingw-w64 安装，确认版本不低于 Rust 捆绑版本。

### 1.3 移除 Solaris 上 `File::lock` 实现（语义错误）

**状态**: ✅ stabilized in 1.98 beta（2026-08-20 转正）
**来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)
**相关概念**: [并发模式](../../03_advanced/00_concurrency/03_concurrency_patterns.md) · [进程与 IPC](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md)

#### 变更细节

Solaris/Illumos 上 `std::fs::File::lock` 的原实现基于 `fcntl`，但其语义与 Rust `File::lock` 要求的「进程级互斥锁」不一致（Solaris `fcntl` 锁在特定文件描述符/进程组合下行为有偏差）。为避免错误的安全保证，1.98.0 移除了 Solaris 上的该实现。

#### 行为变化

- 在 Solaris/Illumos 上，`File::lock` 现在会返回错误或不支持；
- 依赖文件锁的 Solaris 程序需要改用平台特定 API（如 `flock` 包装）。

#### 受影响平台

- `sparcv9-sun-solaris`
- `x86_64-pc-solaris`
- 相关 Illumos 目标

### 1.4 移除 `-Zemscripten-wasm-eh`

**状态**: ✅ stabilized in 1.98 beta（2026-08-20 转正）
**来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)
**相关概念**: [WebAssembly](../../06_ecosystem/11_domain_applications/03_webassembly.md) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

#### 变更细节

`-Zemscripten-wasm-eh` 是一个 nightly 编译器标志，用于在 `wasm32-unknown-emscripten` 目标上启用实验性的 WebAssembly 异常处理。随着上游 LLVM 和 Emscripten 对异常处理支持路径的变化，该标志已过时，1.98.0 正式移除。

#### 迁移路径

- 若仍在使用 `-Zemscripten-wasm-eh`，升级到 1.98.0 后编译器会报错「未知选项」；
- 改用 Emscripten 原生的异常处理配置（如 `-sWASM_EXCEPTIONS` / `-sDISABLE_EXCEPTION_CATCHING`）；
- 具体参数取决于 Emscripten 版本，建议查阅 [Emscripten 文档](https://emscripten.org/docs/introducing_emscripten/index.html)。

---

## 2. RFC merged 跟踪项（实现中，未必随 1.98 稳定）

> 以下为 RFC 已合并、实现与稳定化落在 1.98+ 周期的条目；稳定时逐一确认是否实际进入 1.98.0，未进入者留在 preview 页继续跟踪。

### 2.1 Named `Fn` trait parameters（RFC #3955）

**状态**: 🧪 RFC merged（2026-07-08），实现跟踪中
**来源**: [RFC Book](https://rust-lang.github.io/rfcs/3955-named-fn-trait-parameters.html)
**相关概念**: [Closures](../../02_intermediate/04_types_and_conversions/02_closure_types.md) · [Async Closures](../../03_advanced/01_async/07_async_closures.md)

允许为 `Fn`/`FnMut`/`FnOnce` 家族 trait 的参数命名，改善高阶回调 API 的可读性与文档：

```rust,ignore
// 未来可能的语法（以最终稳定版为准）
trait Processor: Fn(input: i32) -> i32 {}
```

### 2.2 `#![register_{attribute,lint}_tool]`（RFC #3808）

**状态**: 🧪 RFC merged（2026-06-10），实现跟踪中
**来源**: [RFC Book](https://rust-lang.github.io/rfcs/3808-register-tool.html)
**相关概念**: [过程宏](../../03_advanced/03_proc_macros/01_macros.md) · [Unsafe](../../03_advanced/02_unsafe/01_unsafe.md)

允许 crate 注册第三方属性/lint 工具名称，避免与内置属性冲突。对 Rust for Linux、自定义 lint 框架等场景尤为重要。

### 2.3 `todo!()` 不再触发 `unreachable_code`（RFC #3928）

**状态**: 🧪 RFC merged（2026-06-25），实现跟踪中
**来源**: [RFC Book](https://rust-lang.github.io/rfcs/3928-todo-overreach.html)
**相关概念**: [panic 与 abort](../../01_foundation/08_error_handling/03_panic_and_abort.md)

当前 `todo!()` 会同时触发 `unused` 和 `unreachable_code` lint。RFC #3928 修正为：`todo!()` 只保留 `unused`，不再错误地报 `unreachable_code`，因为它明确表达「尚未实现」，而非「不可达」。

### 2.4 Public/Private Dependencies（RFC #3516）

**状态**: 🧪 RFC merged，Cargo 实现跟踪中
**来源**: [RFC Book](https://rust-lang.github.io/rfcs/3516-public-private-dependencies.html)
**相关概念**: [Cargo 依赖解析](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) · [SemVer](../../07_future/02_preview_features/27_cargo_semver_checks_preview.md)

Cargo 将支持在依赖中标记 `public = true/false`，以区分「依赖类型出现在公共 API 中」与「仅内部使用」。这将提升 `cargo-semver-checks` 等工具的准确性，并可能改变 feature 统一策略。

---

## 3. FCP / 讨论中（1.98 窗口内观察）

### 3.1 Safety Tags（RFC #3842）

**状态**: ⏳ FCP / 讨论中
**来源**: [rfcs#3842](https://github.com/rust-lang/rfcs/pull/3842)
**相关概念**: [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Safety Tags 预览](../02_preview_features/03_safety_tags_preview.md)

`#[safety(...)]` 属性旨在为 unsafe 相关构造提供机器可读的语义标注，供 Miri、Kani、BorrowSanitizer 等工具消费。RFC 仍在 FCP 阶段，1.98 稳定可能性低。

---

## 4. nightly only 跟踪项（1.98 不预期稳定）

> 以下条目稳定化路径在 1.99+，本页仅登记状态行；跟踪正文维护在 preview 页与各自预览页。

| 特性 | 状态 | 深度文档 |
|:---|:---|:---|
| Pin Ergonomics（`&pin mut` / `&pin const`） | nightly only | [14_pin_ergonomics_preview.md](../02_preview_features/14_pin_ergonomics_preview.md) |
| Async Drop | nightly only | [22_async_drop_preview.md](../02_preview_features/22_async_drop_preview.md) |
| Return Type Notation（RTN） | nightly only | [09_return_type_notation_preview.md](../02_preview_features/09_return_type_notation_preview.md) |

---

## 5. 升级 1.98.0 检查清单

- [ ] 在 Windows GNU 目标上验证 mingw-w64 更新后的链接行为；
- [ ] 若自定义 panic hook 存储 `Location`，确认生命周期升级后的类型；
- [ ] 若目标平台包含 Solaris/Illumos，检查 `File::lock` 替代方案；
- [ ] 若使用 Emscripten WASM 异常处理，移除 `-Zemscripten-wasm-eh`；
- [ ] 运行 `cargo test --workspace` 与 `cargo clippy --workspace` 确认无新增 lint。

---

## 6. 维护日志

- **2026-07-14**: 建立骨架，迁移自 `rust_1_98_preview.md` 特性矩阵。
- **2026-07-16**: 基于 1.98.0 beta 分支预填充 §1–§4；状态更新为「beta 已冻结，stable 前预填充」。
- **2026-08-20（预计）**: 1.98.0 stable 发布后最终核对官方 release notes，移除 beta 标注。

---

## 7. 来源与延伸阅读

- [Rust 1.98.0 Release Notes (beta)](https://releases.rs/docs/1.98.0/)
- [Rust Forge — Release Versions](https://forge.rust-lang.org/)
- [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
- [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)
- [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)
