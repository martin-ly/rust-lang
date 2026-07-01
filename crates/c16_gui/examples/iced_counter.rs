//! 最小 Iced 计数器示例。
//!
//! 本示例展示 Iced 0.14 的 Elm 架构：`Model`、`Message`、`update`、`view`。
//! `cargo check` 时不启动窗口；真实运行时会创建跨平台 GUI。

use iced::Element;
use iced::widget::{button, column, text};

/// 应用状态。
#[derive(Default)]
struct Counter {
    /// 当前计数值。
    value: i32,
}

/// 用户交互消息。
#[derive(Debug, Clone, Copy)]
enum Message {
    /// 递增。
    Increment,
    /// 递减。
    Decrement,
}

impl Counter {
    /// 初始化应用状态。
    fn new() -> Self {
        Self::default()
    }

    /// 根据消息更新状态。
    fn update(&mut self, message: Message) {
        match message {
            Message::Increment => self.value += 1,
            Message::Decrement => self.value -= 1,
        }
    }

    /// 渲染视图。
    fn view(&self) -> Element<'_, Message> {
        column![
            text(self.value),
            button("+").on_press(Message::Increment),
            button("-").on_press(Message::Decrement),
        ]
        .into()
    }
}

fn main() {
    // 仅展示 Model/Message/update/view，不实际启动 Iced 应用。
    println!("Iced counter example defined (not running).");
    let mut counter = Counter::new();
    counter.update(Message::Increment);
    let _element = counter.view();
}
