# 模板引擎

> **核心库**: tera, askama, handlebars  
> **适用场景**: HTML模板、邮件模板、代码生成

---

## 📋 核心库

| 库 | 类型 | 特点 | 推荐度 |
|-----|------|------|--------|
| **tera** | 运行时 | 类Jinja2 | ⭐⭐⭐⭐⭐ |
| **askama** | 编译时 | 类型安全 | ⭐⭐⭐⭐⭐ |
| **handlebars** | 运行时 | 简单 | ⭐⭐⭐⭐ |

---

## 🎨 tera

```rust
use tera::{Tera, Context};

fn main() {
    let mut tera = Tera::new("templates/**/*").unwrap();
    let mut context = Context::new();
    context.insert("name", "World");
    
    let result = tera.render("hello.html", &context).unwrap();
    println!("{}", result);
}
```

---

## ⚡ askama

```rust
use askama::Template;

#[derive(Template)]
#[template(path = "hello.html")]
struct HelloTemplate {
    name: String,
}

fn main() {
    let hello = HelloTemplate { name: "World".to_string() };
    println!("{}", hello.render().unwrap());
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
