# Rust 桌面 GUI 生态（canonical 缺口闭环页）

> **EN**: Rust Desktop GUI Ecosystem (canonical gap-closure page)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `gui` 分类（864 crates）的 canonical 生态页：egui/eframe 0.37.0 即时模式一极、Slint 1.18.1 声明式一极、iced 0.14.0 第三极，底层 winit 0.30.13/tao 0.37.1 与 wgpu 30.0.1 双收敛，wry 0.57.0 WebView 混合路线与 nwg 系停更陷阱，附 leptos/dioxus 与桌面 GUI 的边界裁决。
> **受众**: [入门→进阶]
> **内容分级**: [专题级]
> **定位**: W6 裁决产物——本库此前全库检索（`git ls-files concept` 无 gui/egui/slint 页；`egui|Slint|iced` 仅散落在 11 个他页引文）坐实 **desktop-GUI canonical 缺口**，本页为该缺口登记的 canonical 页。
> **版本事实基线**: crates.io API 2026-10-19 实查；rustc 1.99.1。

---

## 一、桌面 GUI 框架版图（crates.io 实查 2026-10-19）

| crate | 定位 | 版本（实查） | 累计下载 | 近期下载 | 活跃度判读 |
|:---|:---|:---|---:|---:|:---|
| **egui** | 即时模式（immediate mode）GUI，最活跃 | **0.37.0**（2026-10-15） | 2,696 万 | 686 万 | 一线（双周级发版） |
| **eframe** | egui 官方跨平台外壳（winit/wgpu 桌面+web） | **0.37.0**（2026-10-15） | 2,103 万 | 562 万 | 与 egui 同步 |
| **slint** | 声明式 DSL + 命令式 API，嵌入式友好（SixtyFPS 公司） | **1.18.1**（2026-09-21） | 208 万 | 72 万 | 一线 |
| **iced** | Elm 架构（消息更新模型）GUI | **0.14.0**（2025-12-07） | 303 万 | 67 万 | 活跃但发版节奏放缓 |
| **tao** | 窗口/事件/菜单系统层（Tauri 出品） | **0.37.1**（2026-09-26） | 3,984 万 | 1,566 万 | 底层事实标准之一 |
| **winit** | 窗口创建与输入事件抽象 | **0.30.13**（newest 0.31.0-beta.3，2026-09-04） | 5,917 万 | 1,266 万 | 底层事实标准 |
| **wgpu** | 跨平台 GPU 渲染 API（GUI 后端共用） | **30.0.1**（2026-08-22） | 4,199 万 | 1,351 万 | 一线 |
| **native-windows-gui** | 原生 Win32 控件绑定 | 1.0.13（2022-09-05） | 205 万 | 52 万 | **停更**——近期下载仍有 52 万，存量使用者多 |

（以上均 crates.io `/crates/<name>` 2026-10-19 实查；"近期下载" = `recent_downloads` 字段 ≈90 天窗口。）

## 二、Web 技术栈渗透桌面/全栈（同检索实查）

| crate | 定位 | 版本 | 累计 / 近期下载 |
|:---|:---|:---|---:|
| **leptos** | 全栈响应式 web 框架（RSX，signals） | **0.8.22**（newest 0.9.0-rc0，2026-10-15） | 533 万 / 144 万 |
| **dioxus** | 类 React 全栈（桌面壳 Mobile 壳齐全） | **0.7.10**（newest 0.8.0-alpha.3，2026-10-16） | 322 万 / 123 万 |
| **yew** | 类 React 纯 wasm 框架（老牌） | **0.23.0**（2026-03-10） | 508 万 / 44 万（活跃度衰减） |
| **trunk** | wasm 应用打包器 | **0.21.14**（newest 0.22.0-rc.3，2026-10-16） | 123 万 / 14 万 |
| **wry** | 系统 WebView 封装（Tauri 出品，桌面混合壳） | **0.57.0**（2026-09-08） | 4,060 万 / 1,573 万 |

Tauri 栈（tao + wry + tray-icon 0.26.1/2026-10-07 实查）是「WebView 混合桌面壳」路线的事实代表；Dioxus 0.8 线在推「同一框架覆盖桌面原生壳」路线。

## 三、格局判读（canonical 结论）

1. **两强格局**：即时模式 egui（下载量断层第一，工具类/调试面板/游戏工具链默认选择）vs 声明式 Slint（嵌入式 HMI 首选）；Elm 派 iced 居第三梯队。
2. **Rust GUI 没有"官方答案"是结构性的**——生态在"保留模式 vs 即时模式"、"原生控件 vs 自绘"、"纯 Rust vs WebView 混合"三轴上各自选边，无单一框架通吃；这与 C++ Qt 或 C# WPF 的单极格局不同，是本页最重要的生态事实断言。
3. **底层收敛**：窗口层收敛到 winit/tao，GPU 层收敛到 wgpu——上层框架之争不改变底层双标准。
4. **停更陷阱**：native-windows-gui（2022 停更但仍有月级下载）、makepad-widget（0.1.0/2019，实查仅 3,677 累计下载——makepad 实为 makepad-widgets monorepo 形态，不在 crates.io 主线上发布）——选型时"crates.io 版本旧 ≠ 项目死"与"crates.io 在架 ≠ 活跃"两个反例都成立。

## 四、canonical 缺口登记（本页裁决）

- **已闭环**：desktop-GUI canonical 缺口（本页 + 30_chrono_vs_jiff 同批登记）。
- **仍开放**：computer-vision canonical 缺口——实查 `git ls-files concept` 无 vision/image 页；候选锚：`image 0.25.10`（2.19 亿累计/6,361 万近期，图像编解码事实标准）、`imageproc 0.27.0`（1,412 万/288 万）、`opencv 0.101.1`（500 万/157 万，绑定层）、`resvg/usvg 0.48.1`（SVG 光栅化事实标准，3,136 万/1,150 万）。是否建页归下一波 D 轨道裁决（W8）。

## 五、来源索引

- crates.io API `/crates/<name>` 逐 crate 实查（P0，2026-10-19）：egui/eframe/iced/slint/slint-build/dioxus/leptos/yew/trunk/native-windows-gui/tao/wry/tray-icon/winit/wgpu/image/imageproc/opencv/resvg/usvg/makepad-widget。
- [winit docs.rs](https://docs.rs/winit/latest/winit/)（窗口抽象层 API 口径——事件循环/`WindowAttributes`/跨平台后端清单，「底层 winit 收敛」论断的依据，2026-10-19 核验）。
- [rustc platform support — wasm32-unknown-unknown](https://doc.rust-lang.org/rustc/platform-support/wasm32-unknown-unknown.html)（P0：官方 tier 2 目标页——yew/trunk 纯 wasm 路线与 GUI-to-wasm 移植线的 rustc 官方依据，2026-10-19 核验）。
- [emilk/egui](https://github.com/emilk/egui) · [slint-slint/slint](https://slint.dev) · [iced](https://iced.rs)（P1 项目主页）。
- 学术锚（2026-10-20 arXiv API 实核）：[Can LLMs Test Terminal User Interfaces? (Peng, Hu, Rajan, Bissyandé et al.)](https://arxiv.org/abs/2608.03743)（2026-08-04 提交）——197 个真实 TUI 应用的界面测试实证：Rust 侧 TUI 库高度收敛于 ratatui（可识别项目中 78%），且仅 12% 测试代码触及界面层。本页「GUI/TUI 是接口家族不同形态（GUI 暴露 accessibility 树、TUI 只有字符网格）」的口径依据；同时登记 **TUI/ratatui canonical 缺口**——concept/ 全库无 TUI 生态页，建页归下一波 D 轨道裁决。
- 交叉页：`02_game_ecs.md`/`05_game_development.md`/`15_game_engine_internals.md`（W7 游戏锚，wgpu/winit 共用）、`05_systems_and_embedded/07_embedded_graphics.md`（嵌入式侧图形）。
