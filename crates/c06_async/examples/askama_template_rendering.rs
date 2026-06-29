//! Askama 模板渲染示例
//!
//! 展示 Askama 的编译期模板派生、上下文数据注入与 HTML 渲染。
//! 模板使用 `source` 内联，无需额外模板文件。
//!
//! 运行：
//! ```bash
//! cargo run -p c06_async --example askama_template_rendering
//! ```

use askama::Template;

#[derive(Template)]
#[template(
    source = r#"<!DOCTYPE html>
<html>
<head><title>{{ title }}</title></head>
<body>
  <h1>Hello, {{ name }}!</h1>
  <ul>
  {% for item in items %}
    <li>{{ item }}</li>
  {% endfor %}
  </ul>
</body>
</html>"#,
    ext = "html"
)]
struct PageTemplate<'a> {
    title: &'a str,
    name: &'a str,
    items: &'a [&'a str],
}

fn main() {
    let tpl = PageTemplate {
        title: "Askama Demo",
        name: "Askama",
        items: &["type-safe", "compiled", "Jinja-like"],
    };

    match tpl.render() {
        Ok(html) => println!("{html}"),
        Err(e) => eprintln!("render error: {e}"),
    }
}
