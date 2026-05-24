//! # GUI 生态演示 —— egui 即时模式计算器
//!
//! 本示例使用 [egui](https://github.com/emilk/egui) 和 [eframe](https://docs.rs/eframe)
//! 构建一个跨平台的即时模式 GUI 计算器，展示 Rust GUI 开发的核心概念。
//!
//! ## 运行
//!
//! ```bash
//! cargo run -p c08_algorithms --example gui_calculator_demo
//! ```
//!
//! [来源: egui GitHub / egui.rs](https://egui.rs/)

use eframe::{App, Frame, NativeOptions};
use egui::{CentralPanel, TextStyle, Ui, Vec2};

/// 计算器应用状态
#[derive(Default)]
struct CalculatorApp {
    display: String,
    current_input: String,
    operator: Option<char>,
    accumulator: f64,
    should_clear: bool,
}

impl CalculatorApp {
    fn new() -> Self {
        Self {
            display: "0".to_string(),
            current_input: String::new(),
            operator: None,
            accumulator: 0.0,
            should_clear: false,
        }
    }

    /// 处理数字输入
    fn input_digit(&mut self, digit: char) {
        if self.should_clear {
            self.current_input.clear();
            self.should_clear = false;
        }
        if self.current_input == "0" && digit != '.' {
            self.current_input = digit.to_string();
        } else {
            self.current_input.push(digit);
        }
        self.display = self.current_input.clone();
    }

    /// 处理运算符
    fn input_operator(&mut self, op: char) {
        if !self.current_input.is_empty() {
            let value: f64 = self.current_input.parse().unwrap_or(0.0);
            self.accumulator = value;
        }
        self.operator = Some(op);
        self.should_clear = true;
        self.display = format!("{} {}", self.accumulator, op);
    }

    /// 计算结果
    fn calculate(&mut self) {
        if self.current_input.is_empty() || self.operator.is_none() {
            return;
        }
        let current: f64 = self.current_input.parse().unwrap_or(0.0);
        let result = match self.operator {
            Some('+') => self.accumulator + current,
            Some('-') => self.accumulator - current,
            Some('*') => self.accumulator * current,
            Some('/') => {
                if current == 0.0 {
                    self.display = "Error: ÷0".to_string();
                    self.current_input.clear();
                    self.operator = None;
                    self.should_clear = true;
                    return;
                }
                self.accumulator / current
            }
            _ => current,
        };
        self.display = format_result(result);
        self.accumulator = result;
        self.current_input = result.to_string();
        self.operator = None;
        self.should_clear = true;
    }

    /// 清除所有状态
    fn clear(&mut self) {
        self.display = "0".to_string();
        self.current_input.clear();
        self.operator = None;
        self.accumulator = 0.0;
        self.should_clear = false;
    }
}

impl App for CalculatorApp {
    fn ui(&mut self, ui: &mut Ui, _frame: &mut Frame) {
        // 设置默认字体大小
        let ctx = ui.ctx();
        let mut style = (*ctx.global_style()).clone();
        style
            .text_styles
            .insert(TextStyle::Button, egui::FontId::proportional(24.0));
        style
            .text_styles
            .insert(TextStyle::Heading, egui::FontId::proportional(36.0));
        ctx.set_global_style(style);

        CentralPanel::default().show_inside(ui, |ui| {
            ui.vertical_centered(|ui| {
                ui.heading("🧮 Rust 计算器");
                ui.label("egui 即时模式 GUI 演示");
                ui.add_space(20.0);

                // 显示屏
                ui.group(|ui| {
                    ui.set_min_width(280.0);
                    ui.set_min_height(60.0);
                    ui.vertical_centered(|ui| {
                        ui.label(egui::RichText::new(&self.display).size(36.0).monospace());
                    });
                });

                ui.add_space(10.0);

                // 按钮网格
                let button_size = Vec2::new(65.0, 55.0);

                // 第 1 行: C / ± / % / ÷
                ui.horizontal(|ui| {
                    if ui.add_sized(button_size, egui::Button::new("C")).clicked() {
                        self.clear();
                    }
                    if ui.add_sized(button_size, egui::Button::new("±")).clicked()
                        && let Ok(val) = self.display.parse::<f64>()
                    {
                        let neg = -val;
                        self.display = format_result(neg);
                        self.current_input = neg.to_string();
                    }
                    if ui.add_sized(button_size, egui::Button::new("%")).clicked()
                        && let Ok(val) = self.display.parse::<f64>()
                    {
                        let pct = val / 100.0;
                        self.display = format_result(pct);
                        self.current_input = pct.to_string();
                    }
                    if ui.add_sized(button_size, egui::Button::new("÷")).clicked() {
                        self.input_operator('/');
                    }
                });

                // 第 2 行: 7 8 9 ×
                ui.horizontal(|ui| {
                    for digit in ['7', '8', '9'] {
                        if ui
                            .add_sized(button_size, egui::Button::new(digit.to_string()))
                            .clicked()
                        {
                            self.input_digit(digit);
                        }
                    }
                    if ui.add_sized(button_size, egui::Button::new("×")).clicked() {
                        self.input_operator('*');
                    }
                });

                // 第 3 行: 4 5 6 -
                ui.horizontal(|ui| {
                    for digit in ['4', '5', '6'] {
                        if ui
                            .add_sized(button_size, egui::Button::new(digit.to_string()))
                            .clicked()
                        {
                            self.input_digit(digit);
                        }
                    }
                    if ui.add_sized(button_size, egui::Button::new("−")).clicked() {
                        self.input_operator('-');
                    }
                });

                // 第 4 行: 1 2 3 +
                ui.horizontal(|ui| {
                    for digit in ['1', '2', '3'] {
                        if ui
                            .add_sized(button_size, egui::Button::new(digit.to_string()))
                            .clicked()
                        {
                            self.input_digit(digit);
                        }
                    }
                    if ui.add_sized(button_size, egui::Button::new("+")).clicked() {
                        self.input_operator('+');
                    }
                });

                // 第 5 行: 0 . =
                ui.horizontal(|ui| {
                    if ui
                        .add_sized(Vec2::new(134.0, 55.0), egui::Button::new("0"))
                        .clicked()
                    {
                        self.input_digit('0');
                    }
                    if ui.add_sized(button_size, egui::Button::new(".")).clicked()
                        && !self.current_input.contains('.')
                    {
                        self.input_digit('.');
                    }
                    if ui.add_sized(button_size, egui::Button::new("=")).clicked() {
                        self.calculate();
                    }
                });

                ui.add_space(20.0);
                ui.label(
                    egui::RichText::new("Rust 1.95.0 + egui 0.34 + eframe 0.34")
                        .size(12.0)
                        .color(ui.visuals().weak_text_color()),
                );
            });
        });
    }
}

/// 格式化计算结果，去除多余的小数位
fn format_result(value: f64) -> String {
    if value.fract() == 0.0 {
        format!("{:.0}", value)
    } else {
        let s = format!("{:.10}", value);
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    }
}

fn main() {
    let options = NativeOptions {
        viewport: eframe::egui::ViewportBuilder::default()
            .with_inner_size([320.0, 480.0])
            .with_resizable(false),
        ..Default::default()
    };

    eframe::run_native(
        "Rust GUI Calculator",
        options,
        Box::new(|_cc| Ok(Box::new(CalculatorApp::new()))),
    )
    .expect("eframe 运行失败");
}
