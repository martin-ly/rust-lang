# 过程宏理论

## 1. 过程宏类型

- 包括函数式宏、属性宏、派生宏
- 统一接口：fn(TokenStream) -> TokenStream

## 2. TokenStream处理

- 过程宏以TokenStream为输入输出，需解析、修改、生成代码
- 常用库：syn（解析AST）、quote（生成代码）

## 3. 类型安全与限制

- 过程宏本身不保证类型安全，需开发者手动校验
- 错误处理需返回编译期友好信息

## 4. 工程案例

### 4.1 自定义派生宏

```rust
use proc_macro::TokenStream;
#[proc_macro_derive(MyDebug)]
pub fn my_debug(input: TokenStream) -> TokenStream {
    // 解析AST，生成Debug实现
    input
}
```

### 4.2 属性宏实现

```rust
use proc_macro::TokenStream;
#[proc_macro_attribute]
pub fn my_attr(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 修改item代码
    item
}
```

## 5. 最佳实践

- 使用syn/quote简化AST操作
- 明确错误提示，避免panic
- 文档注释说明宏用途

## 6. 批判性分析

- 过程宏功能强大但调试难度高，需谨慎设计
- 未来可提升IDE集成与安全性分析能力

## 7. 安全性与自动化测试

- 过程宏建议结合macrotest/trybuild进行自动化测试，防止展开回归
- 错误处理应返回Span定位，便于开发者定位问题

## 8. 复杂工程案例

### 8.1 自动为枚举生成Display实现

```rust
#[proc_macro_derive(EnumDisplay)]
pub fn enum_display(input: TokenStream) -> TokenStream {
    // 解析AST，自动生成Display trait实现
    input
}
```

## 9. 未来展望（补充）

- 过程宏IDE集成、静态分析与安全性工具将成为主流
