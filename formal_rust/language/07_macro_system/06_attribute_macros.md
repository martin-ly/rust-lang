# 属性宏设计

## 1. 属性宏语法与结构

- 使用 #[proc_macro_attribute] 标注，定义 fn(attr: TokenStream, item: TokenStream) -> TokenStream
- 可修饰函数、结构体、模块等

## 2. TokenStream处理

- 解析attr参数与item代码，生成或修改AST
- 常用库：syn、quote

## 3. 工程案例

### 3.1 日志自动注入属性宏

```rust
use proc_macro::TokenStream;
#[proc_macro_attribute]
pub fn log(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析item，自动插入日志代码
    item
}
```

### 3.2 自动实现特质属性宏

```rust
use proc_macro::TokenStream;
#[proc_macro_attribute]
pub fn auto_impl(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 生成特质实现
    item
}
```

## 4. 最佳实践

- 明确参数语义，避免歧义
- 错误处理友好，避免panic
- 文档注释说明用法与限制

## 5. 批判性分析

- 属性宏极大提升了代码自动化能力，但调试与安全性需关注
- 未来可提升IDE集成与静态分析能力

## 6. 参数解析与自动化测试

- 建议使用syn::parse解析attr参数，提升健壮性
- 结合trybuild/macrotest为属性宏编写测试用例

## 7. 复杂工程案例

### 7.1 自动注册路由属性宏

```rust
#[proc_macro_attribute]
pub fn auto_route(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析item，自动生成路由注册代码
    item
}
```

## 8. 未来展望（补充）

- 属性宏IDE集成、参数静态分析与安全性工具将持续完善
