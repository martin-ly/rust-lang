# Tera/Askama 模板引擎形式化分析

> **主题**: 模板渲染的类型安全
>
> **形式化框架**: 上下文绑定 + HTML转义
>
> **参考**: Tera Documentation; Askama Documentation

---

## 目录

- [Tera/Askama 模板引擎形式化分析](#teraaskama-模板引擎形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Tera运行时](#2-tera运行时)
    - [定理 2.1 (动态模板)](#定理-21-动态模板)
    - [定理 2.2 (模板继承)](#定理-22-模板继承)
  - [3. Askama编译时](#3-askama编译时)
    - [定理 3.1 (类型检查)](#定理-31-类型检查)
  - [4. 转义安全](#4-转义安全)
    - [定理 4.1 (自动转义)](#定理-41-自动转义)
  - [5. 反例](#5-反例)
    - [反例 5.1 (XSS注入)](#反例-51-xss注入)
    - [反例 5.2 (模板注入)](#反例-52-模板注入)

---

## 1. 引言

模板引擎对比:

- **Tera**: Django风格，运行时编译
- **Askama**: 编译时生成，类型安全

---

## 2. Tera运行时

### 定理 2.1 (动态模板)

> 模板运行时加载，上下文动态绑定。

```rust
let mut context = Context::new();
context.insert("name", &user.name);
context.insert("items", &items);

let rendered = tera.render("template.html", &context)?;
```

∎

### 定理 2.2 (模板继承)

> 块覆盖实现模板继承。

```html
<!-- base.html -->
{% block content %}{% endblock %}

<!-- child.html -->
{% extends "base.html" %}
{% block content %}Child content{% endblock %}
```

∎

---

## 3. Askama编译时

### 定理 3.1 (类型检查)

> Askama在编译时验证模板字段。

```rust
#[derive(Template)]
#[template(path = "hello.html")]
struct HelloTemplate<'a> {
    name: &'a str,  // 编译时检查模板使用此字段
}
```

**优势**:

- 字段缺失编译错误
- 零运行时开销
- 类型安全

∎

---

## 4. 转义安全

### 定理 4.1 (自动转义)

> 默认HTML转义防止XSS。

```rust
// 输入: <script>alert('xss')</script>
// 输出: &lt;script&gt;alert(&#x27;xss&#x27;)&lt;/script&gt;
```

**安全**:

```html
{{ user_input }}        <!-- 自动转义 -->
{{ user_input|safe }}   <!-- 显式不转义，危险! -->
```

∎

---

## 5. 反例

### 反例 5.1 (XSS注入)

```rust
// 危险: 使用|safe过滤器
let html = format!("<div>{}</div>", user_input);
template.render(Context::new().insert("content", &html|safe));

// 正确: 让模板自动转义
```

### 反例 5.2 (模板注入)

```rust
// 危险: 用户输入作为模板
tera.render_str(&user_input, &context)?;  // SSTI风险!

// 正确: 仅使用预定义模板
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
