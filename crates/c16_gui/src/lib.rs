//! # c16_gui - GUI / 跨平台 UI 生态实战示例
//!
//! 本 crate 聚焦 Rust 现代 GUI 与跨平台 UI 生态，提供 Tauri、Dioxus、Leptos、
//! egui、iced 五个主流框架的最小可检查示例。示例代码位于 [`examples/`](./examples)
//! 目录，运行时不实际渲染窗口，仅用于展示各框架的核心 API 与编程模型。
//!
//! ## 模块组织
//!
//! - [`desktop`] - Tauri 桌面应用核心逻辑抽象
//! - [`web_components`] - Dioxus / Leptos 组件模型示例
//! - [`immediate_gui`] - egui 即时模式 GUI 工具函数
//! - [`declarative_gui`] - iced 声明式 Elm 架构工具函数

#![allow(clippy::type_complexity)]

/// Tauri 桌面应用相关抽象与工具。
pub mod desktop {
    /// 演示 Tauri 命令处理器签名。
    ///
    /// # 参数
    /// - `name`: 要问候的对象
    ///
    /// # 返回值
    /// 返回问候字符串。
    #[tauri::command]
    pub fn greet(name: &str) -> String {
        format!("Hello, {name}!")
    }
}

/// Web 组件模型示例（Dioxus / Leptos）。
pub mod web_components {
    /// Leptos 计数器组件使用的状态类型。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct CounterState {
        /// 当前计数值。
        pub value: i32,
    }

    impl CounterState {
        /// 创建初始状态。
        pub const fn new(initial: i32) -> Self {
            Self { value: initial }
        }

        /// 递增计数器。
        pub fn increment(&mut self) {
            self.value += 1;
        }

        /// 递减计数器。
        pub fn decrement(&mut self) {
            self.value -= 1;
        }
    }
}

/// egui 即时模式 GUI 辅助函数。
pub mod immediate_gui {
    /// 在 UI 上显示问候标签。
    pub fn show_greeting(ui: &mut egui::Ui, name: &str) {
        ui.label(format!("Hello, {name}!"));
    }

    /// 在 UI 上显示计数器与控制按钮。
    pub fn counter_controls(ui: &mut egui::Ui, count: &mut i32) {
        ui.horizontal(|ui| {
            if ui.button("-").clicked() {
                *count -= 1;
            }
            ui.label(count.to_string());
            if ui.button("+").clicked() {
                *count += 1;
            }
        });
    }
}

/// iced 声明式 Elm 架构辅助函数。
pub mod declarative_gui {
    /// iced 计数器消息枚举。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum CounterMessage {
        /// 递增。
        Increment,
        /// 递减。
        Decrement,
    }

    /// 更新计数器状态。
    pub fn update_counter(value: &mut i32, message: CounterMessage) {
        match message {
            CounterMessage::Increment => *value += 1,
            CounterMessage::Decrement => *value -= 1,
        }
    }
}
