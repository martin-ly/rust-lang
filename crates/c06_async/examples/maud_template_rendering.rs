//! Maud 模板渲染示例
//!
//! 展示 Maud 的编译期 HTML 宏 `html!`，通过 Rust 表达式直接构造类型安全的 Markup。
//!
//! 运行：
//! ```bash
//! cargo run -p c06_async --example maud_template_rendering
//! ```

use maud::{Markup, html};

fn page(title: &str, name: &str, items: &[&str]) -> Markup {
    html! {
        html {
            head { title { (title) } }
            body {
                h1 { "Hello, " (name) "!" }
                ul {
                    @for item in items {
                        li { (item) }
                    }
                }
            }
        }
    }
}

fn main() {
    let markup = page(
        "Maud Demo",
        "Maud",
        &["type-safe", "compile-time", "Rust-native"],
    );
    println!("{}", markup.into_string());
}
