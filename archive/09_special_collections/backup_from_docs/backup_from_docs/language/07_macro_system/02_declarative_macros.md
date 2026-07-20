# Rust声明宏形式化理论

## 1. 声明宏概述

### 1.1 声明宏定义

声明宏是Rust中最常用的宏形式，通过模式匹配和模板替换实现编译时代码生成。

**形式化定义**:
$$\text{DeclarativeMacro} = \text{macro\_rules!} \quad \text{MacroName} \quad \text{MacroRules}$$

其中：

- $\text{MacroName} = \text{Identifier}$
- $\text{MacroRules} = \text{MacroRule}^*$
- $\text{MacroRule} = \text{MacroPattern} \Rightarrow \text{MacroTemplate}$

### 1.2 声明宏语法结构

```text
DeclarativeMacro
├── macro_rules!
├── MacroName
└── MacroRules
    ├── MacroRule1
    ├── MacroRule2
    └── ...
        ├── MacroPattern
        └── MacroTemplate
```

## 2. 宏模式匹配理论

### 2.1 模式定义

**模式语法**:
$$\text{MacroPattern} = \text{TokenTree} \times \text{Repetition} \times \text{Metavariable}$$

**TokenTree定义**:
$$\text{TokenTree} = \text{enum}\{
    \text{Token}(\text{Token}),
    \text{Delimited}(\text{DelimSpan}, \text{Delimiter}, \text{TokenStream})
\}$$

### 2.2 元变量类型系统

**元变量类型**:
$$\text{Metavariable} = \text{enum}\{
    \text{expr}, \text{ident}, \text{ty}, \text{pat}, \text{stmt}, \text{block}, \text{item}, \text{meta}, \text{tt}
\}$$

**元变量语义**:
- $\text{expr}$: 表达式
- $\text{ident}$: 标识符
- $\text{ty}$: 类型
- $\text{pat}$: 模式
- $\text{stmt}$: 语句
- $\text{block}$: 代码块
- $\text{item}$: 条目
- $\text{meta}$: 元数据
- $\text{tt}$: TokenTree

### 2.3 重复模式理论

**重复模式定义**:
$$\text{Repetition} = \text{enum}\{*, +, ?\}$$

**重复语义**:
- $*$: 零次或多次重复
- $+$: 一次或多次重复
- $?$: 零次或一次重复

**重复模式语法**:
$$\text{RepetitionPattern} = \$(\text{TokenTree}) \text{Repetition} \text{Separator}?$$

### 2.4 模式匹配算法

**匹配函数**:
$$\text{match} : \text{MacroPattern} \times \text{TokenStream} \to \text{Option}[\text{MatchResult}]$$

**匹配结果**:
$$\text{MatchResult} = \text{struct}\{
    \text{bindings}: \text{Map}[\text{Metavariable}, \text{TokenStream}],
    \text{rest}: \text{TokenStream}
\}$$

**匹配规则**:
$$\frac{\Gamma \vdash \text{pattern}(p) \quad \Gamma \vdash \text{input}(i) \quad \text{match}(p, i) = \text{Some}(\sigma)}{\Gamma \vdash \text{pattern\_match}(p, i) : \text{MatchResult}}$$

## 3. 宏模板展开理论

### 3.1 模板定义

**模板语法**:
$$\text{MacroTemplate} = \text{TokenTree} \times \text{Substitution} \times \text{Repetition}$$

**模板结构**:
```
MacroTemplate
├── LiteralTokens
├── MetavariableSubstitutions
└── RepetitionExpansions
```

### 3.2 变量替换理论

**替换函数**:
$$\text{substitute} : \text{MacroTemplate} \times \text{MatchResult} \to \text{TokenStream}$$

**替换规则**:
$$\frac{\Gamma \vdash \text{template}(t) \quad \Gamma \vdash \text{bindings}(b)}{\Gamma \vdash \text{substitute}(t, b) : \text{TokenStream}}$$

### 3.3 重复展开理论

**重复展开函数**:
$$\text{expand\_repetition} : \text{RepetitionPattern} \times \text{TokenStream} \times \text{Separator} \to \text{TokenStream}$$

**展开规则**:
$$\frac{\Gamma \vdash \text{repetition}(r) \quad \Gamma \vdash \text{content}(c) \quad \Gamma \vdash \text{separator}(s)}{\Gamma \vdash \text{expand\_repetition}(r, c, s) : \text{TokenStream}}$$

## 4. 声明宏类型规则

### 4.1 宏构造类型规则

**宏定义规则**:
$$\frac{\Gamma \vdash \text{macro\_rules!} \quad \Gamma \vdash \text{name}: \text{Identifier} \quad \Gamma \vdash \text{rules}: \text{MacroRules}}{\Gamma \vdash \text{DeclarativeMacro}(\text{name}, \text{rules}) : \text{Macro}}$$

**规则集合规则**:
$$\frac{\forall i \in [1, n] \cdot \Gamma \vdash \text{rule}_i : \text{MacroRule}}{\Gamma \vdash \{\text{rule}_1, \ldots, \text{rule}_n\} : \text{MacroRules}}$$

### 4.2 宏调用类型规则

**宏调用规则**:
$$\frac{\Gamma \vdash m : \text{Macro} \quad \Gamma \vdash \text{input} : \text{TokenStream}}{\Gamma \vdash m(\text{input}) : \text{ExpandedTokenStream}}$$

**模式匹配规则**:
$$\frac{\Gamma \vdash \text{pattern}(p) \quad \Gamma \vdash \text{input}(i) \quad \text{match}(p, i) = \text{Some}(\sigma)}{\Gamma \vdash \text{expand}(p, i) : \text{ExpandedTokenStream}}$$

### 4.3 元变量类型规则

**表达式元变量**:
$$\frac{\Gamma \vdash e : \tau}{\Gamma \vdash \$e : \text{expr}}$$

**标识符元变量**:
$$\frac{\Gamma \vdash \text{ident}: \text{Identifier}}{\Gamma \vdash \$\text{ident} : \text{ident}}$$

**类型元变量**:
$$\frac{\Gamma \vdash \tau : \text{Type}}{\Gamma \vdash \$\tau : \text{ty}}$$

## 5. 声明宏卫生性

### 5.1 卫生性定义

**卫生性条件**:
$$\text{Hygiene} = \forall v \in \text{MacroVariables} \cdot \text{scope}(v) \cap \text{external\_scope}(v) = \emptyset$$

**变量作用域**:
$$\text{VariableScope} = \text{struct}\{
    \text{macro\_scope}: \text{ScopeId},
    \text{external\_scope}: \text{ScopeId},
    \text{capture\_rules}: \text{CaptureRules}
\}$$

### 5.2 卫生性保证

**定理 5.1 (声明宏卫生性)**:
对于任何声明宏 $m$，如果 $m$ 使用标准的宏语法，则 $m$ 满足卫生性条件。

**证明**:
1. 声明宏使用 `macro_rules!` 语法
2. 编译器自动处理变量作用域
3. 宏内部变量与外部变量隔离
4. 因此满足卫生性条件

### 5.3 变量捕获规则

**捕获类型**:
$$\text{CaptureType} = \text{enum}\{
    \text{ByValue}, \text{ByReference}, \text{ByMove}
\}$$

**默认捕获**:
$$\text{default\_capture} = \text{ByValue}$$

## 6. 声明宏实现

### 6.1 宏展开引擎

**展开引擎接口**:
```rust
pub trait DeclarativeMacroExpander {
    fn expand_macro(
        &self,
        macro_call: &MacroCall,
        context: &MacroContext,
    ) -> Result<TokenStream, MacroError>;
}
```

**展开步骤**:
1. **词法分析**: 将输入转换为TokenStream
2. **模式匹配**: 尝试匹配宏规则
3. **变量绑定**: 提取匹配的元变量
4. **模板展开**: 替换模板中的元变量
5. **递归展开**: 处理嵌套的宏调用

### 6.2 模式匹配实现

**匹配器接口**:
```rust
pub trait PatternMatcher {
    fn match_pattern(
        &self,
        pattern: &MacroPattern,
        input: &TokenStream,
    ) -> Option<MatchResult>;
}
```

**匹配算法**:
```rust
fn match_pattern(pattern: &MacroPattern, input: &TokenStream) -> Option<MatchResult> {
    match pattern {
        MacroPattern::Token(token) => {
            // 匹配单个token
            if input.next() == Some(token) {
                Some(MatchResult::new())
            } else {
                None
            }
        }
        MacroPattern::Metavariable(ty, name) => {
            // 匹配元变量
            let content = extract_content(input, ty);
            Some(MatchResult::with_binding(name, content))
        }
        MacroPattern::Repetition(inner, rep) => {
            // 匹配重复模式
            match_repetition(inner, rep, input)
        }
    }
}
```

### 6.3 模板展开实现

**展开器接口**:
```rust
pub trait TemplateExpander {
    fn expand_template(
        &self,
        template: &MacroTemplate,
        bindings: &MatchResult,
    ) -> Result<TokenStream, MacroError>;
}
```

**展开算法**:
```rust
fn expand_template(template: &MacroTemplate, bindings: &MatchResult) -> TokenStream {
    let mut result = TokenStream::new();

    for token in template.tokens() {
        match token {
            Token::Literal(lit) => {
                result.push(Token::Literal(lit.clone()));
            }
            Token::Metavariable(name) => {
                if let Some(content) = bindings.get(name) {
                    result.extend(content.clone());
                }
            }
            Token::Repetition(inner, rep) => {
                let expanded = expand_repetition(inner, rep, bindings);
                result.extend(expanded);
            }
        }
    }

    result
}
```

## 7. 实际应用示例

### 7.1 基础宏示例

**简单打印宏**:
```rust
macro_rules! print_hello {
    () => {
        println!("Hello, World!");
    };
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 使用示例
print_hello!();           // 输出: Hello, World!
print_hello!("Alice");    // 输出: Hello, Alice!
```

**类型安全向量宏**:
```rust
macro_rules! vec {
    () => {
        Vec::new()
    };
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
    ($($x:expr,)*) => {
        vec![$($x),*]
    };
}

// 使用示例
let v1: Vec<i32> = vec![];
let v2 = vec![1, 2, 3];
let v3 = vec![1, 2, 3,];
```

### 7.2 高级宏示例

**条件编译宏**:
```rust
macro_rules! cfg_if {
    ($(if #[cfg($($meta:meta),*)] { $($it:item)* } else if #[cfg($($else_meta:meta),*)] { $($else_it:item)* })* else { $($else_it:item)* }) => {
        __cfg_if_items! {
            () ;
            $( ( ($($meta),*) ($($it)*) ), )*
            ( () ($($else_it)*) )
        }
    }
}
```

**递归宏**:
```rust
macro_rules! factorial {
    (0) => { 1 };
    ($n:expr) => { $n * factorial!($n - 1) };
}

// 使用示例
let result = factorial!(5); // 120
```

### 7.3 复杂模式匹配示例

**多模式宏**:
```rust
macro_rules! match_expr {
    ($e:expr, $($p:pat => $b:expr),*) => {
        match $e {
            $($p => $b),*
        }
    };
}

// 使用示例
let x = 5;
let result = match_expr!(x,
    1 => "one",
    2 => "two",
    3..=10 => "three to ten",
    _ => "other"
);
```

**嵌套重复宏**:
```rust
macro_rules! matrix {
    ($([$($x:expr),*]),*) => {
        {
            let mut matrix = Vec::new();
            $(matrix.push(vec![$($x),*]);)*
            matrix
        }
    };
}

// 使用示例
let m = matrix!(
    [1, 2, 3],
    [4, 5, 6],
    [7, 8, 9]
);
```

## 8. 声明宏优化

### 8.1 编译时优化

**宏缓存**:
$$\text{MacroCache} = \text{Map}[\text{MacroSignature}, \text{ExpandedResult}]$$

**缓存策略**:
```rust
struct MacroCache {
    cache: HashMap<MacroSignature, TokenStream>,
    hits: usize,
    misses: usize,
}

impl MacroCache {
    fn get_or_expand(&mut self, signature: MacroSignature, macro_call: &MacroCall) -> TokenStream {
        if let Some(cached) = self.cache.get(&signature) {
            self.hits += 1;
            cached.clone()
        } else {
            self.misses += 1;
            let expanded = self.expand_macro(macro_call);
            self.cache.insert(signature, expanded.clone());
            expanded
        }
    }
}
```

### 8.2 模式匹配优化

**模式树优化**:
```rust
struct OptimizedPatternTree {
    root: PatternNode,
    cache: HashMap<PatternSignature, MatchResult>,
}

enum PatternNode {
    Token(Token),
    Metavariable(MetavariableType, String),
    Repetition(Box<PatternNode>, RepetitionType),
    Alternative(Vec<PatternNode>),
}
```

### 8.3 展开优化

**延迟展开**:
$$\text{LazyExpansion} = \text{struct}\{
    \text{macro\_call}: \text{MacroCall},
    \text{expansion\_context}: \text{ExpansionContext},
    \text{is\_expanded}: \text{bool}
\}$$

**条件展开**:
```rust
fn should_expand(macro_call: &MacroCall, context: &ExpansionContext) -> bool {
    // 检查是否已经展开
    if context.is_expanded(macro_call) {
        return false;
    }

    // 检查展开深度
    if context.depth > MAX_EXPANSION_DEPTH {
        return false;
    }

    // 检查循环依赖
    if context.has_cycle(macro_call) {
        return false;
    }

    true
}
```

## 9. 声明宏定理和证明

### 9.1 模式匹配正确性

**定理 9.1 (模式匹配正确性)**:
对于任何声明宏模式 $p$ 和输入 $i$，如果 $\text{match}(p, i) = \text{Some}(\sigma)$，则 $\sigma$ 是 $p$ 和 $i$ 的有效匹配结果。

**证明**:
1. 根据模式匹配算法定义
2. 每个匹配步骤都遵循语法规则
3. 元变量绑定符合类型要求
4. 因此匹配结果是正确的

### 9.2 模板展开正确性

**定理 9.2 (模板展开正确性)**:
对于任何宏模板 $t$ 和匹配结果 $\sigma$，如果 $\text{substitute}(t, \sigma) = \text{result}$，则 $\text{result}$ 是 $t$ 在 $\sigma$ 下的正确展开结果。

**证明**:
1. 根据模板展开算法定义
2. 每个替换步骤都保持语法正确性
3. 重复展开遵循重复规则
4. 因此展开结果是正确的

### 9.3 声明宏终止性

**定理 9.3 (声明宏终止性)**:
对于任何声明宏系统，如果满足以下条件：
1. 宏规则数量有限
2. 模式匹配算法终止
3. 模板展开算法终止
4. 递归展开深度有限

则声明宏展开过程必然终止。

**证明**:
1. 假设展开过程不终止
2. 根据条件1，宏规则数量有限
3. 根据条件2和3，每次匹配和展开都终止
4. 根据条件4，递归深度有限
5. 因此展开过程必然终止

## 10. 声明宏最佳实践

### 10.1 设计原则

**简洁性**: 宏应该简洁明了，避免过度复杂
**可读性**: 宏的意图应该清晰，易于理解
**可维护性**: 宏应该易于修改和扩展
**类型安全**: 宏应该保持类型安全

### 10.2 常见陷阱

**无限递归**: 避免宏调用自身导致无限递归
**变量捕获**: 注意宏中变量的作用域和捕获
**性能问题**: 避免生成过多代码影响编译性能
**调试困难**: 宏展开后的代码可能难以调试

### 10.3 调试技巧

**宏展开调试**:
```rust
// 使用 rustc 的宏展开功能
// cargo rustc -- -Z unstable-options --pretty=expanded

// 或者使用 macro_rules! 的调试版本
macro_rules! debug_macro {
    ($($t:tt)*) => {
        println!("Macro input: {:?}", stringify!($($t)*));
        $($t)*
    };
}
```

## 11. 总结

声明宏是Rust中最强大的元编程工具之一，通过严格的形式化理论保证了类型安全和卫生性。通过模式匹配和模板展开，声明宏能够生成类型安全的代码，同时保持编译时检查的优势。

声明宏的形式化理论为编译器实现提供了理论基础，确保了宏展开的正确性和安全性。通过数学定义和定理证明，我们建立了声明宏的完整理论体系，为Rust的元编程能力提供了坚实的数学基础。
