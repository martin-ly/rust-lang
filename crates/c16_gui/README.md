> **权威来源**: 本文件为 `crates/c16_gui/` 的 crate 入口页。
> 通用 Rust 概念解释统一维护在 `concept/` 中；详见 [../../concept/06_ecosystem/11_domain_applications/](../../concept/06_ecosystem/11_domain_applications/)。
>
> 根据 AGENTS.md §2 Canonical 规则，`crates/` 不重复通用 Rust 概念解释；
> 如需深入学习，请前往 `concept/` 权威页。
>
# c16_gui

GUI / 跨平台 UI 生态实战示例 crate。

涵盖 Tauri、Dioxus、Leptos、egui、iced 等主流 Rust GUI/Web 框架的最小可运行示例。

## 示例

- `tauri_desktop_minimal` — Tauri 桌面应用最小示例
- `dioxus_web_minimal` — Dioxus Web 应用最小示例
- `leptos_counter` — Leptos 同构计数器
- `egui_native_minimal` — egui + eframe 原生窗口示例
- `iced_counter` — iced 声明式计数器

## 运行

```bash
cargo run --example tauri_desktop_minimal
```

> 注意：Tauri / Leptos 等示例可能依赖平台特定工具链或前端构建步骤，详见各示例文件顶部注释。
