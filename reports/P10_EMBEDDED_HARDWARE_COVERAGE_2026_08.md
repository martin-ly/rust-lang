# P10-2 no_std / 裸机 / 嵌入式 / 实时系统语义加固与硬件覆盖

**EN**: P10-2 Report: no_std / Bare-Metal / Embedded / Real-Time Systems Semantic Hardening and Hardware Coverage
**Summary**: Execution report for P10-2 of `PLAN_P10_Semantic_Domain_International_Alignment_2026_08_04.md`: five new `concept/` canonical pages, expanded `crates/c13_embedded` hardware examples for three targets, and validation results.
**日期**: 2026-08-04

---

## 1. 工作目标与范围

依据 `reports/PLAN_P10_Semantic_Domain_International_Alignment_2026_08_04.md` 的 P10-2 任务：

1. 在 `concept/06_ecosystem/05_systems_and_embedded/` 新增/增强 5 个权威页：
   - `52_no_std_allocators_and_panic_handlers.md`
   - `53_critical_sections_and_sync_on_bare_metal.md`
   - `54_linker_scripts_and_memory_layout.md`
   - `55_rtic_vs_embassy_real_time_frameworks.md`
   - `56_rust_for_linux_kernel_module_basics.md`
2. 扩展 `crates/c13_embedded` 硬件实测示例，覆盖至少 3 个目标（`thumbv7em-none-eabihf`、`thumbv7m-none-eabi`、`riscv32imac-unknown-none-elf`），并确保 `cargo build --target <target>` 通过。
3. 输出本报告。

---

## 2. 新增/修改文件清单

### 2.1 Concept 权威页（新增）

| 序号 | 路径 | Bloom 层级 | 核心主题 |
|---|---|---|---|
| 52 | `concept/06_ecosystem/05_systems_and_embedded/52_no_std_allocators_and_panic_handlers.md` | L4 | `#[global_allocator]`、`GlobalAlloc`、OOM、`#[panic_handler]`、集成验证 |
| 53 | `concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md` | L4 | 关中断临界区、`critical-section`、Mutex<RefCell<T>>、原子 SPSC、多核自旋锁、PCP |
| 54 | `concept/06_ecosystem/05_systems_and_embedded/54_linker_scripts_and_memory_layout.md` | L4 | MEMORY/SECTIONS、LMA/VMA、`#[link_section]`、ARM 特殊区域、RISC-V RAM-only |
| 55 | `concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md` | L4 | RTIC 优先级天花板 vs Embassy async/await、选型决策树 |
| 56 | `concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md` | L4 | 内核模块声明、`module!`、no_std/no_main、panic handler、C FFI、构建加载 |

### 2.2 导航与索引（更新）

- `concept/06_ecosystem/05_systems_and_embedded/README.md`
  - 补全 45–51 索引，新增 52–56 索引。
- `concept/SUMMARY.md`
  - 在 51 之后新增 52–56 条目。

### 2.3 Crate 与构建配置（修改/新增）

| 路径 | 变更内容 |
|---|---|
| `crates/c13_embedded/src/lib.rs` | 将 `no_std` 与模块排除条件从仅 ARM 扩展到 ARM + RISC-V 裸机目标 |
| `crates/c13_embedded/src/main.rs` | 支持 host / ARM / RISC-V 三种入口，修复 riscv32 与 ARM 下的未使用导入 |
| `crates/c13_embedded/Cargo.toml` | 为 ARM/RISC-V 目标添加 `critical-section = "1.2"` 并启用对应 single-core/single-hart feature |
| `crates/c13_embedded/.cargo/config.toml` | 新增 `riscv32imac-unknown-none-elf` 目标 runner 与链接脚本标志 |
| `.cargo/config.toml` | 为 `riscv32imac-unknown-none-elf` 补充 `-Tmemory.x` 与 `-Tlink.x` |
| `crates/c13_embedded/examples/cortex_m_minimal_blinky.rs` | 补充 `use panic_halt as _;` |
| `crates/c13_embedded/examples/riscv_minimal_blinky.rs` | 补充 `use panic_halt as _;` |
| `crates/c13_embedded/examples/no_std_allocators_and_panic_handlers.rs` | 新增：多目标可编译的 panic handler + bump allocator + critical-section 综合示例 |
| `crates/c13_embedded/build.rs` | 已存在：为 ARM / RISC-V 自动生成 `memory.x` |

---

## 3. 硬件目标验证结果

所有目标均已通过 `cargo build --target <target>` 或 `cargo clippy --target <target>` 验证。测试机器已安装以下目标：

```text
thumbv7em-none-eabihf
thumbv7m-none-eabi
riscv32imac-unknown-none-elf
```

### 3.1 综合示例 `no_std_allocators_and_panic_handlers`

| 目标 | 命令 | 结果 |
|---|---|---|
| `thumbv7em-none-eabihf` | `cargo build -p c13_embedded --target thumbv7em-none-eabihf --example no_std_allocators_and_panic_handlers` | ✅ 通过 |
| `thumbv7m-none-eabi` | `cargo build -p c13_embedded --target thumbv7m-none-eabi --example no_std_allocators_and_panic_handlers` | ✅ 通过 |
| `riscv32imac-unknown-none-elf` | `cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example no_std_allocators_and_panic_handlers` | ✅ 通过 |

### 3.2 原有示例回归验证

| 目标 | 命令 | 结果 |
|---|---|---|
| `thumbv7em-none-eabihf` | `cargo build -p c13_embedded --target thumbv7em-none-eabihf --example cortex_m_minimal_blinky` | ✅ 通过 |
| `thumbv7m-none-eabi` | `cargo build -p c13_embedded --target thumbv7m-none-eabi --example no_std_qemu_blinky` | ✅ 通过 |
| `riscv32imac-unknown-none-elf` | `cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example riscv_minimal_blinky` | ✅ 通过 |

### 3.3 Host 与 CI 关键命令

| 命令 | 结果 | 说明 |
|---|---|---|
| `cargo check --workspace` | ✅ 通过 | 全 workspace host 检查 |
| `cargo test -p c13_embedded` | ✅ 通过 | 16 单元测试 + 2 ignored doctest |
| `cargo clippy -p c13_embedded` | ✅ 通过 | host 目标 |
| `cargo clippy -p c13_embedded --target thumbv7em-none-eabihf` | ✅ 通过 | ARM 硬浮点 |
| `cargo clippy -p c13_embedded --target thumbv7m-none-eabi` | ✅ 通过 | ARM Cortex-M3 |
| `cargo clippy -p c13_embedded --target riscv32imac-unknown-none-elf` | ✅ 通过 | RISC-V 32-bit |
| `mdbook build` | ✅ 通过 | 书籍构建成功（仅有搜索索引大小警告） |

---

## 4. 质量门诊断（非阻断）

按任务要求，质量门仅用于诊断，不阻断提交。

| 门 | 命令 | 结果 | 说明 |
|---|---|---|---|
| 重叠检测 v2 | `python scripts/detect_content_overlap_v2.py --budget 999999` | ⚠️ 基线未变 | 新增 5 页未出现在高重叠命中列表中 |
| 命名规范 | `python scripts/check_naming_convention.py --strict` | ❌ 1 ERROR | ERROR 为 `concept/05_comparative` 下同号目录冲突（`05_idioms_patterns_architecture` / `05_quizzes`），与本次新增无关 |
| 死链/跨层 | `python scripts/kb_auditor.py --link-check` | ⚠️ 26 死链 / 22 跨层问题 | 均为既有问题；新增 52–56 页未引入新死链 |
| 概念代码块 | `python scripts/check_concept_code_blocks.py --sample 0 --strict` | ❌ rot=27 | 27 块既有腐烂/失败，不涉及 52–56 页；新增页使用 `rust,ignore` 标记裸机代码 |

> **注**：质量门失败项均为本次变更前已存在的基线问题，详见各自报告（`reports/CONTENT_OVERLAP_V2_2026-08-04.md`、`reports/kb_quality_dashboard.md`）。

---

## 5. 关键发现

1. **RISC-V 裸机构建需要显式链接 `memory.x`**
   - `riscv-rt` 0.18 的 `link.x` 依赖用户提供的 `memory.x` 定义 `REGION_TEXT` 等别名。
   - 仅设置 `-Tlink.x` 会导致 `REGION_TEXT` 未定义；必须同时设置 `-Tmemory.x` 且 `memory.x` 先于 `link.x` 处理。
   - 已在 `.cargo/config.toml` 与 `crates/c13_embedded/.cargo/config.toml` 中修复。

2. **`critical-section` 需要目标平台 feature**
   - ARM 需 `cortex-m` 启用 `critical-section-single-core`；
   - RISC-V 需 `riscv` 启用 `critical-section-single-hart`。
   - 否则链接时报错 `_critical_section_1_0_acquire/release` 未定义。

3. **裸机 bin 应统一处理 host / ARM / RISC-V 入口**
   - 原 `src/main.rs` 仅区分 host 与 ARM，在 riscv32 目标下会错误地进入 host 路径并使用 `println!`。
   - 已重构为三分支：`host` 演示、`ARM` WFI 循环、`RISC-V` WFI 循环。

4. **裸机示例需显式引入 panic handler**
   - `cortex_m_minimal_blinky` 与 `riscv_minimal_blinky` 原本缺少 panic handler，导致链接失败。
   - 通过 `use panic_halt as _;` 修复。

5. **新增页遵循 canonical 规则**
   - 5 个新页均包含 EN 标题、Summary、Bloom 层级、Rust 版本、权威来源声明、代码示例、反例、硬件实测/CI 命令。
   - 与现有权威页（13、15、16、18、29、34、35、47、48 等）形成互补而非重复。

---

## 6. 剩余工作

1. **真实硬件实测**
   - 当前验证止步于 `cargo build`/`cargo clippy`。需在真实 STM32F4 / STM32F1 / GD32VF103 等板卡上通过 `probe-rs run` 或 QEMU 运行示例并采集 `dmesg`/RTT 输出。

2. **RTIC / Embassy 示例的 CI 编译**
   - `crates/c13_embedded/real-hardware-demos/rtic-demo` 与 `embassy-demo` 依赖具体芯片 HAL，未纳入本次目标编译矩阵。
   - 建议后续配置 feature gate，使其在 host `cargo check` 与目标 `cargo build --target` 中均可编译。

3. **Rust for Linux 内核模块示例**
   - 56 页目前仅提供概念与命令模板，未在真实 Rust for Linux 内核源码树中编译 `.ko`。
   - 建议后续创建独立 `crates/c13_rust_for_linux_sample` 或补丁目录，对接内核 Kbuild。

4. **质量门基线修复**
   - `check_concept_code_blocks.py` 的 27 块既有腐烂/失败、`kb_auditor` 的 26 死链/22 跨层问题、`check_naming_convention.py` 的 `05_comparative` 同号冲突，需独立安排清理 sprint。

5. **KG / 测验同步**
   - 新增 5 个权威页尚未注册到知识图谱与 `quiz_registry.yaml`。
   - 建议运行 `scripts/generate_kg_v3.py` 与 `scripts/check_quiz_system.py` 跟进。

---

## 7. 结论

P10-2 核心交付物已完成：

- ✅ 5 个 `concept/` 权威页创建并满足模板要求；
- ✅ `crates/c13_embedded` 新增多目标可编译示例，覆盖 3 个裸机目标；
- ✅ 修复 RISC-V 链接脚本、critical-section feature、bin 入口等交叉编译问题；
- ✅ `cargo check --workspace`、`cargo test -p c13_embedded`、3 目标 `cargo build`/`cargo clippy`、`mdbook build` 全部通过；
- ✅ 诊断性质量门未发现由本次新增引入的新问题。

后续重点：真实硬件烧录运行、RTIC/Embassy/Rust-for-Linux 示例的完整 CI 集成、以及全库质量门基线的专项清理。
