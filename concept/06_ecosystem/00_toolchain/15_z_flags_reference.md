# rustc / Cargo `-Z` 不稳定选项参考清单

> **EN**: rustc and Cargo `-Z` Unstable Flags Reference

> **Summary**: A categorized, source-verified reference of the most-used unstable `-Z` flags for rustc and Cargo: build, diagnostics/profiling, sanitizers/hardening, dependency visibility, and type-system frontiers, each with status, purpose, and authoritative source.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **实测环境**: `-Z` 选项实测环境为 rustc 1.99.0-nightly 375b1431b 2026-07-10 / cargo 同版 nightly
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页（`-Z` 选项系统化清单的唯一深度解释）。
> **前置概念**: [rustc Driver 与 Stable MIR](10_rustc_driver_and_stable_mir.md) · [LLVM 后端与代码生成](09_llvm_backend_and_codegen.md) · [编译器测试体系](13_compiler_testing.md)
> **后置概念**: [交叉编译与 target 平台支持](../05_systems_and_embedded/02_cross_compilation.md) · [Target Tier 平台支持全景](../05_systems_and_embedded/10_target_tier_platform_support.md) · [Rust vs C++（工具链标志哲学对比：`-Z` 夜间选项 vs `-fsanitize`/`-march`）](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

> **来源**: `rustc +nightly -Z help` 与 `cargo +nightly -Z help` 实测输出（2026-07-12，234 个 rustc `-Z` 选项）· [The Rust Unstable Book — Compiler flags](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags.html) · [Cargo — Unstable Features](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html) · [rustc-dev-guide — How to build and run](https://rustc-dev-guide.rust-lang.org/building/how-to-build-and-run.html)（以上外链均 curl 200 实测 2026-07-12）
> **国际权威来源（2026-07-13 补录）**: **P1** [Bae et al. — RUDRA: Finding Memory Safety Bugs in Rust at the Ecosystem Scale（SOSP 2021）](https://dl.acm.org/doi/10.1145/3477132.3483570)（基于 rustc 内部表示的静态分析代表工作） · **P2** [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)（编译器团队官方博客；curl 实测 2026-07-13，ACM 反爬注记同前页）

---

## 一、`-Z` 是什么：定位与纪律

`-Z` 选项是 rustc / Cargo 的**不稳定（unstable）命令行接口**：只在 nightly 工具链上可用，无稳定性保证，名称、语义、默认值可在任何版本变更或删除。稳定版 rustc 遇到 `-Z` 直接报错：

```text
$ rustc -Z help
error: the option `Z` is only accepted on the nightly compiler
```

（rustc 1.97.0 stable 实测。）

| 纪律 | 说明 |
|:---|:---|
| **不入生产构建** | `-Z` 不得出现在需要稳定工具链复现的构建脚本中；CI 若用 `-Z`，必须钉死 nightly 版本（如 `nightly-2026-07-10`） |
| **以 `-Z help` 为准** | 文档滞后于实现；本页每条均已对照 `rustc/cargo +nightly -Z help` 实测存在性 |
| **内部选项不承诺可用** | Unstable Book 对无 tracking issue 的选项标注 “likely internal to the compiler”（如 `-Z threads`、`-Z mir-enable-passes`） |
| **与 `-C` 区分** | `-C` 是稳定的 codegen 选项（如 `-C target-feature`）；`-Z` 覆盖构建流程、诊断、实验特性 |

启用方式：

```bash
# rustc 直接调用
rustc +nightly -Ztime-passes main.rs

# 经 Cargo 传给 rustc
RUSTFLAGS="-Ztime-passes" cargo +nightly build

# Cargo 自身的 -Z（需 [unstable] 或命令行）
cargo +nightly build -Zbuild-std=core,alloc --target x86_64-unknown-none
```

---

## 二、构建类（Build）

| 选项 | 状态 | 用途 | 出处 |
|:---|:---:|:---|:---|
| `cargo -Z build-std=core,alloc,std` | nightly | **std-aware Cargo**：把标准库作为 crate 图的一部分从源码编译；`no_std` 目标、`-Z build-std` 是 nvptx64 等目标的必需路径（见 [Target Tier 平台支持全景](../05_systems_and_embedded/10_target_tier_platform_support.md) §nvptx64） | [Cargo Unstable — build-std](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-std)（wg-cargo-std-aware） |
| `cargo -Z build-std-features=...` | nightly | 配置随 `build-std` 编译的标准库自身 feature（如 `panic_immediate_abort`） | [Cargo Unstable](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-std-features) |
| `cargo -Z build-analysis` | nightly | 把构建度量（耗时、重建原因）以 JSONL 持久化到 `$CARGO_HOME/log/`，配 `cargo report sessions/timings/rebuilds` 查询历史构建；稳定工具链上仅告警不报错，可常驻 config | [Cargo Unstable — build-analysis](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-analysis)（tracking #15844） |
| `-Z binary-dep-depinfo` | nightly（rustc + cargo 同名） | dep-info 文件跟踪二进制依赖（sysroot、crate 依赖产物），使构建系统能感知二进制输入变化 | `rustc -Z help` 实测；[Cargo Unstable](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#binary-dep-depinfo) |
| `-Z codegen-backend=<path>` | nightly | 指定 codegen 后端动态库（如 Cranelift `rustc_codegen_cranelift`），是替换 LLVM 后端的入口 | `rustc -Z help` 实测；见 [LLVM 后端与代码生成](09_llvm_backend_and_codegen.md) |
| `-Z dylib-lto` | nightly | 对 dylib crate 类型启用 LTO | `rustc -Z help` 实测 |
| `-Z share-generics` | nightly | 当前 crate 共享泛型实例化（单态化（Monomorphization）去重），减小二进制体积、代价是链接时耦合 | [Unstable Book — share-generics](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/share-generics.html) |
| `-Z threads=N` | nightly（内部） | rustc 前端并行线程池大小；并行 rustc 的官方入口 | [Unstable Book — threads](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/threads.html)（无 tracking issue，标注 internal） |
| `-Z no-parallel-backend` | nightly | 保留 codegen-units 与 ThinLTO 但令 LLVM 串行执行，用于隔离并行后端 bug | [Unstable Book — no-parallel-backend](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/no-parallel-backend.html) |
| `-Z embed-metadata=no` | nightly | 不在 rlib/dylib 中嵌入 crate 元数据（减小产物；下游将无法链接） | `rustc -Z help` 实测 |

---

## 三、诊断与性能分析类（Diagnostics & Profiling）

| 选项 | 状态 | 用途 | 出处 |
|:---|:---:|:---|:---|
| `-Z time-passes` | nightly | 打印每个编译 pass 的耗时；`-Z time-passes-format=json` 输出机器可读格式 | [Unstable Book — time-passes](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/time-passes.html) |
| `-Z self-profile` | nightly | rustc 内部 profiler，产出 `.events/.string_data/.string_index` 三件套，用 [measureme](https://github.com/rust-lang/measureme) 的 `summarize`/`crox`/`inferno` 分析；`-Z self-profile-events` 控制事件集 | [Unstable Book — self-profile](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/self-profile.html) |
| `-Z print-type-sizes` | nightly | 打印每个类型的布局（size/align/字段偏移），排查内存膨胀的第一工具 | [Unstable Book — print-type-sizes](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/print-type-sizes.html) |
| `-Z print-mono-items` | nightly | 打印单态化收集结果（哪些泛型（Generics）实例被 codegen） | `rustc -Z help` 实测 |
| `-Z dump-mir=<filter>` | nightly | 把 MIR 按 pass 转储到 `mir_dump/`；`-Z dump-mir-graphviz` 另出 `.dot` | `rustc -Z help` 实测；见 [编译器测试体系](13_compiler_testing.md) |
| `-Z llvm-time-trace` | nightly | 从 LLVM 侧产出 JSON 时间轨迹（Chrome trace 格式） | `rustc -Z help` 实测 |
| `-Z treat-err-as-bug[=N]` | nightly | 把第 N 个错误当作 ICE 处理（带内部栈回溯），用于诊断编译器自身 | `rustc -Z help` 实测 |
| `-Z eagerly-emit-delayed-bugs` | nightly | 延迟 bug 立即报错而非暂存，便于定位 | `rustc -Z help` 实测 |
| `-Z deduplicate-diagnostics=no` | nightly | 关闭相同诊断去重 | `rustc -Z help` 实测 |
| `-Z annotate-moves[=limit]` | nightly | 为编译器生成的 move/copy 发射调试信息，使 profiler 可见隐式拷贝 | `rustc -Z help` 实测 |
| `-Z move-size-limit=N` | nightly | `large_assignments` lint 的触发阈值（字节） | `rustc -Z help` 实测 |
| `-Z mir-enable-passes=+P,-Q` | nightly（内部，**可启用已知 unsound pass**） | 强制开/关指定 MIR pass，覆盖一切其他检查 | [Unstable Book — mir-enable-passes](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/mir-enable-passes.html) |

---

## 四、Sanitizer 与安全加固类（Sanitizers & Hardening）

`-Z sanitizer=<name>` 是 sanitizer 家族的总开关，支持的值分两类（[Unstable Book — sanitizer](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/sanitizer.html)，tracking #39699 / #89653）：

- **测试/模糊测试用**：`address`、`hwaddress`、`kernel-hwaddress`、`leak`、`memory`、`thread`
- **生产环境加固用**：`cfi`（Control Flow Integrity）、`kcfi`（Kernel CFI）、`shadow-call-stack`、`memtag`

| 选项 | 状态 | 用途 | 出处 |
|:---|:---:|:---|:---|
| `-Z sanitizer=<name>` | nightly | 启用指定 sanitizer 插桩（通常配 `-C target-feature` 与 nightly 构建 std） | [Unstable Book — sanitizer](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/sanitizer.html) |
| `-Z sanitizer-recover=<list>` | nightly | 指定 sanitizer 检出后恢复执行而非中止 | `rustc -Z help` 实测 |
| `-Z sanitizer-memory-track-origins[=N]` | nightly | MemorySanitizer 的未初始化值来源追踪 | `rustc -Z help` 实测 |
| `-Z sanitizer-cfi-{generalize-pointers,normalize-integers,canonical-jump-tables}` | nightly | CFI 类型泛化/归一化/规范跳转表，调节 CFI 严格度与兼容性的权衡 | `rustc -Z help` 实测 |
| `-Z sanitizer-kcfi-arity` | nightly | KCFI 参数数量（arity）指示 | `rustc -Z help` 实测 |
| `-Z cf-protection=<none\|branch\|return\|full>` | nightly | 控制流架构保护插桩（x86 CET / IBT+SHSTK） | `rustc -Z help` 实测 |
| `-Z stack-protector=<strategy>` | nightly | 栈粉碎保护策略（`rustc --print stack-protector-strategies` 列出可选值） | `rustc -Z help` 实测 |
| `-Z branch-protection=<opts>` | nightly | AArch64 BTI（分支目标识别）与指针认证（PAC）选项 | `rustc -Z help` 实测 |
| `-Z direct-access-external-data` | nightly | 外部数据符号用直接访问还是 GOT 间接（无位置无关代码场景） | `rustc -Z help` 实测 |

---

## 五、依赖可见性类（Dependency Visibility）

| 选项 | 状态 | 用途 | 出处 |
|:---|:---:|:---|:---|
| `cargo -Z public-dependency` | nightly | 依赖可在 `Cargo.toml` 标记 `public = true/false`；启用后 Cargo 向 rustc 传递附加信息，使 `exported_private_dependencies` lint 能区分 public/private 依赖（供“私有依赖泄漏到公共 API”场景的诊断，RFC 3516 体系） | [Cargo Unstable — public-dependency](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#public-dependency)（tracking #44663） |

> **边界**：`cargo-features = ["public-dependency"]` 的旧启用方式已废弃并将移除；现在用 `-Z public-dependency` 或 `[unstable]` 配置。

---

## 六、类型系统与实验前沿类（Frontiers）

| 选项 | 状态 | 用途 | 出处 |
|:---|:---:|:---|:---|
| `-Z next-solver[=coherence]` | nightly | 启用下一代 trait solver（`-Z next-solver=coherence` 仅在 coherence 检查中启用） | [Unstable Book — next-solver](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/next-solver.html) |
| `-Z polonius[=legacy]` | nightly | 启用基于 Polonius 的借用（Borrowing）检查器（NLL 之后的位置敏感借用分析） | [Unstable Book — polonius](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/polonius.html) |
| `-Z autodiff=Enable,...` | nightly | Enzyme 自动微分（`std::autodiff` 的编译器侧开关；`PrintTA/PrintAA/NoPostopt` 等子选项调试 AD 过程） | `rustc -Z help` 实测 |
| `-Z contract-checks` | nightly | 为契约（contract）前/后置条件发射运行时（Runtime）检查 | `rustc -Z help` 实测 |
| `-Z allow-features=<list>` | nightly | 白名单：只允许列出的 language feature 被启用（限制依赖中 `#![feature]` 的 blast radius） | [Unstable Book — allow-features](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/allow-features.html) |
| `-Z assume-incomplete-release` | nightly | 令 `cfg(version)` 把当前版本视为未完成发布（版本门槛逻辑的测试工具） | `rustc -Z help` 实测 |

---

## 七、入口选项：`-Z unstable-options`

`-Z unstable-options` 本身不开启功能，而是**解锁 rustc 命令行上的不稳定选项语法**（如 `--check-cfg` 的部分不稳定形式、`--emit` 的实验值）。它是“meta 开关”：先 `-Z unstable-options`，其后的不稳定 CLI 选项才被接受（[Unstable Book — unstable-options](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/unstable-options.html)）。

---

## 八、选用判定

```text
需求                              → 首选 -Z
─────────────────────────────────────────────────
no_std / 自定义 target 构建 std    → cargo -Z build-std
分析"为什么重建了"                  → cargo -Z build-analysis（+ cargo report rebuilds）
编译慢，找耗时 pass                 → -Z time-passes（粗）→ -Z self-profile（细）
类型/结构体太大                     → -Z print-type-sizes / -Z move-size-limit
内存安全测试                        → -Z sanitizer=address（+ nightly build-std）
生产加固                            → -Z cf-protection / -Z stack-protector / -Z sanitizer=cfi
泛型体积膨胀                        → -Z share-generics / -Z print-mono-items
私有依赖泄漏到公共 API              → cargo -Z public-dependency
替换 codegen 后端（Cranelift）      → -Z codegen-backend
限制 nightly feature 使用面         → -Z allow-features
```

> **权威来源索引**
>
> | 来源 | 可信度 | 说明 |
> |:---|:---:|:---|
> | `rustc +nightly -Z help` / `cargo +nightly -Z help`（2026-07-12 实测，rustc 234 项） | ✅ 一级 | 选项存在性与帮助文本的最终事实源 |
> | [The Rust Unstable Book — Compiler flags](https://doc.rust-lang.org/nightly/unstable-book/compiler-flags.html) | ✅ 一级 | 各选项的专页文档与 tracking issue |
> | [Cargo — Unstable Features](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html) | ✅ 一级 | Cargo 侧 `-Z`（build-std/build-analysis/public-dependency 等） |
> | [rustc-dev-guide — How to build and run](https://rustc-dev-guide.rust-lang.org/building/how-to-build-and-run.html) | ✅ 一级 | 编译器开发场景下 `-Z` 的使用上下文 |
> | [measureme](https://github.com/rust-lang/measureme) | ✅ 二级 | self-profile 数据分析工具链 |
> **受众**: [进阶]
> **内容分级**: [综述级]

## ⚠️ 反例与陷阱

本节以 stable 工具链上使用 `-Z` 旗标为反例，展示不稳定选项的通道门禁。

### 反例：stable rustc 拒绝 `-Z` 旗标（rustc 1.97.0 实测）

```console
$ rustc -Ztime-passes main.rs
error: the option `-Z` is only accepted on the nightly channel of rustc
```

`-Z` 系列旗标（编译器内部调试/实验选项）刻意不承诺稳定性，stable 通道在参数解析阶段即拒绝。

### ✅ 修正：nightly 工具链或 stable 等价手段

```console
cargo +nightly rustc -- -Ztime-passes      # 显式 nightly
cargo build --timings                      # stable 等价的构建耗时报告
```

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((rustc / Cargo -Z 不稳定选项参考清单))
    一、-Z 是什么定位与纪律
    二、构建类Build
    四、Sanitizer
    五、依赖可见性类Dependency
    六、类型系统与实验前沿类Frontiers
```
