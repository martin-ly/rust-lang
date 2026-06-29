//! 最小 Dioxus Web 组件示例。
//!
//! 本示例展示 Dioxus 0.7 的函数式组件与 `rsx!` 宏。在真实 Web 应用中，
//! 会调用 `dioxus_web::launch(App)`；此处为最小可检查示例，不实际启动渲染。

use dioxus::prelude::*;

/// 最小问候组件。
#[component]
fn Greeting(name: String) -> Element {
    rsx! {
        div {
            h1 { "Hello, {name}" }
            p { "Welcome to Dioxus Web." }
        }
    }
}

/// 计数器组件，演示局部状态。
#[component]
fn Counter() -> Element {
    let mut count = use_signal(|| 0);

    rsx! {
        div {
            button { onclick: move |_| count += 1, "+" }
            p { "Count: {count}" }
            button { onclick: move |_| count -= 1, "-" }
        }
    }
}

fn main() {
    // 仅展示组件定义，不实际启动 Web 渲染。
    println!("Dioxus web minimal example defined (not launching).");
    let _element = VNode::empty();
}
