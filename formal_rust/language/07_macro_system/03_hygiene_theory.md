# 卫生宏理论

## 1. 卫生宏定义

- 卫生宏（Hygienic Macro）自动管理标识符作用域，避免变量捕获和命名冲突。
- 形式化定义：

$$
\forall v \in \text{MacroVariables},\ \text{scope}(v) \cap \text{external\_scope}(v) = \emptyset
$$

## 2. 作用域隔离机制

- 宏展开时为内部变量分配唯一作用域ID
- Rust编译器自动重命名（gensym）防止冲突

## 3. 变量捕获与规则

- 支持ByValue、ByReference、ByMove等捕获类型
- 显式捕获规则可通过宏参数指定

## 4. 卫生性定理与证明

- 定理：若宏满足卫生性条件，则展开后无变量冲突
- 证明：见 01_formal_macro_system.md 相关章节

## 5. 工程案例

### 5.1 卫生宏避免变量污染

```rust
macro_rules! make_var {
    () => {
        let x = 42; // x作用域仅限宏内部
        println!("x in macro: {}", x);
    };
}
fn main() {
    let x = 1;
    make_var!();
    println!("x in main: {}", x);
}
```

### 5.2 非卫生宏导致冲突（对比）

- C/C++预处理器宏易污染全局命名空间，Rust卫生宏自动隔离

## 6. 批判性分析与未来展望

- Rust卫生宏极大提升了元编程安全性，但过程宏的卫生性需开发者手动保证。
- 未来可进一步自动化卫生性分析与IDE集成。

## 7. 过程宏卫生性风险与检测

- 过程宏需开发者手动管理变量作用域，易引入污染
- 建议结合syn::parse、Span::call_site等API手动隔离作用域
- 可用静态分析工具辅助检测过程宏卫生性问题

## 8. 工程案例补充

### 8.1 过程宏变量污染示例

```rust
// 错误示例：未隔离变量作用域，可能污染外部
#[proc_macro]
pub fn bad_macro(_input: TokenStream) -> TokenStream {
    quote! { let x = 42; } .into()
}
// 正确做法：使用Span::def_site确保变量仅在宏内部可见
```

## 9. 未来展望（补充）

- 过程宏卫生性自动检测与IDE集成将成为提升工程安全性的关键
- 未来可探索Rust编译器层面对过程宏卫生性的强制约束
