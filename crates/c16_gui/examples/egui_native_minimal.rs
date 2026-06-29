//! 最小 egui 原生窗口示例（使用 eframe）。
//!
//! 本示例展示 eframe 0.34 + egui 0.34 的 `App` trait 实现。`cargo check` 时
//! 不实际运行事件循环；真实运行时会弹出原生窗口。

use eframe::egui;

/// 最小应用状态。
#[derive(Default)]
struct MinimalApp {
    /// 计数器值。
    count: i32,
    /// 用户输入文本。
    name: String,
}

impl eframe::App for MinimalApp {
    fn ui(&mut self, ui: &mut egui::Ui, _frame: &mut eframe::Frame) {
        ui.heading("egui Native Minimal");
        ui.horizontal(|ui| {
            ui.label("Name: ");
            ui.text_edit_singleline(&mut self.name);
        });
        ui.horizontal(|ui| {
            if ui.button("-").clicked() {
                self.count -= 1;
            }
            ui.label(format!("Count: {}", self.count));
            if ui.button("+").clicked() {
                self.count += 1;
            }
        });
    }
}

fn main() {
    // 仅展示 App 实现，不实际启动原生窗口。
    println!("egui native minimal example defined (not running).");
    let _app = MinimalApp::default();
    let _options = eframe::NativeOptions::default();
}
