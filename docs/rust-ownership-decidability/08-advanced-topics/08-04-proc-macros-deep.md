# Chapter 8.4: Procedural Macros Deep Dive

> "Macros are the ultimate metaprogramming tool in Rust, allowing you to extend the language itself."

Procedural macros (proc macros) are one of Rust's most powerful metaprogramming features. Unlike declarative macros (`macro_rules!`), proc macros operate on the Abstract Syntax Tree (AST) and can perform arbitrary transformations. This chapter provides a comprehensive deep dive into proc macro architecture, implementation patterns, common pitfalls, and best practices.

## 8.4.1 Proc Macro Architecture

### 8.4.1.1 The Three Types of Proc Macros

Rust provides three distinct types of procedural macros, each serving different use cases:

#### 1. Function-like Proc Macros: `#[proc_macro]`

Function-like macros are invoked with the `!` syntax, similar to declarative macros:

```rust
my_macro! { /* tokens */ }
```

These are defined as:

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // Transform input tokens into output tokens
    input
}
```

**Use Cases:**
- Custom DSLs (Domain-Specific Languages)
- Complex code generation
- Compile-time computation
- Template engines

**Example - SQL Query Verification:**

```rust
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let query = input.to_string();
    
    // Parse and validate SQL at compile time
    if let Err(e) = validate_sql(&query) {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("Invalid SQL: {}", e)
        ).to_compile_error().into();
    }
    
    // Generate the query execution code
    let expanded = quote! {
        Query { sql: #query }
    };
    
    expanded.into()
}
```

Usage:
```rust
let users = sql!(SELECT * FROM users WHERE active = true);
```

#### 2. Derive Macros: `#[proc_macro_derive]`

Derive macros automatically implement traits for types:

```rust
#[derive(MyTrait)]
struct MyStruct { ... }
```

Definition:

```rust
use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    
    let expanded = quote! {
        impl #impl_generics MyTrait for #name #ty_generics #where_clause {
            fn my_method(&self) {
                // Implementation
            }
        }
    };
    
    expanded.into()
}
```

**Use Cases:**
- Serialization/Deserialization (serde)
- Debug formatting
- Comparison traits
- Custom traits
- Builder patterns

#### 3. Attribute Macros: `#[proc_macro_attribute]`

Attribute macros transform the item they're attached to:

```rust
#[my_attribute(args)]
fn my_function() { ... }
```

Definition:

```rust
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn my_attribute(args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse attribute arguments
    let args = parse_macro_input!(args as AttributeArgs);
    
    // Parse the item being decorated
    let input = parse_macro_input!(input as ItemFn);
    
    // Transform and return
    let expanded = quote! {
        // Modified or wrapped version of input
    };
    
    expanded.into()
}
```

**Use Cases:**
- Function instrumentation (logging, timing)
- Route registration (web frameworks)
- Test fixtures
- Conditional compilation
- Code injection

### 8.4.1.2 The Compilation Model

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        PROC MACRO COMPILATION PIPELINE                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐          │
│  │   Source Code   │───▶│   TokenStream   │───▶│  Proc Macro     │          │
│  │   (.rs files)   │    │   (tokens)      │    │  Crate Build    │          │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘          │
│                                                         │                    │
│                                                         ▼                    │
│                                                ┌─────────────────┐          │
│                                                │  Compiled Proc  │          │
│                                                │  Macro Library  │          │
│                                                │  (dynamic lib)  │          │
│                                                └─────────────────┘          │
│                                                         │                    │
│  ┌─────────────────┐    ┌─────────────────┐            │                    │
│  │  Final Binary   │◀───│ Expanded Source │◀───────────┘                    │
│  │  (.exe/.so)     │    │   (AST)         │                                 │
│  └─────────────────┘    └─────────────────┘                                 │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

**Key Characteristics:**

1. **Separate Compilation**: Proc macros are compiled as a separate crate before the main crate
2. **Dynamic Loading**: The compiler loads the proc macro as a dynamic library
3. **Token-Based**: Communication happens through `TokenStream`, not AST nodes
4. **Isolation**: Proc macros run in a separate process for stability

**Theorem MACRO-ISOLATION** (Proc Macro Sandboxing):
> Proc macros execute in a sandboxed environment with restricted capabilities. They cannot:
> - Access the filesystem arbitrarily
> - Make network requests
> - Execute arbitrary code on the host
> - Access environment variables not explicitly passed

**Proof Sketch**: The proc macro is loaded as a dynamic library in a separate compiler process. The `proc_macro` crate provides limited APIs that don't expose system resources directly. The compiler controls all I/O operations.

### 8.4.1.3 Crate Structure

A proc macro crate has specific requirements:

```toml
# Cargo.toml
[package]
name = "my-proc-macro"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true  # Required!

[dependencies]
proc-macro2 = "1.0"  # Enhanced TokenStream
syn = { version = "2.0", features = ["full"] }  # Parsing
quote = "1.0"  # Code generation
```

**Critical Requirements:**

1. **`proc-macro = true`**: This flag tells Cargo this is a proc macro crate
2. **Crate Type**: Can only export proc macros, no regular public items
3. **Single Target**: Proc macro crates cannot have bin targets

```rust
// lib.rs - Proc macro entry points
use proc_macro::TokenStream;

#[proc_macro]
pub fn function_like(input: TokenStream) -> TokenStream {
    // Implementation
}

#[proc_macro_derive(MyDerive)]
pub fn derive_macro(input: TokenStream) -> TokenStream {
    // Implementation
}

#[proc_macro_attribute]
pub fn attribute_macro(args: TokenStream, input: TokenStream) -> TokenStream {
    // Implementation
}
```

## 8.4.2 Token Analysis

### 8.4.2.1 Understanding TokenStream

The `TokenStream` is the fundamental data structure for proc macros:

```rust
// proc_macro::TokenStream (from standard library)
pub struct TokenStream {
    inner: Vec<TokenTree>,
}

pub enum TokenTree {
    Group(Group),      // (...), [...], {...}
    Ident(Ident),      // foo, bar, baz
    Punct(Punct),      // +, -, *, /, etc.
    Literal(Literal),  // "string", 42, 3.14
}
```

**TokenStream Structure:**

```
Input: struct Point { x: i32, y: i32 }

TokenStream:
├── TokenTree::Ident("struct")
├── TokenTree::Ident("Point")
├── TokenTree::Group(Delimiter::Brace)
│   ├── TokenTree::Ident("x")
│   ├── TokenTree::Punct(':')
│   ├── TokenTree::Ident("i32")
│   ├── TokenTree::Punct(',')
│   ├── TokenTree::Ident("y")
│   ├── TokenTree::Punct(':')
│   └── TokenTree::Ident("i32")
```

### 8.4.2.2 Token Manipulation

**Basic Iteration:**

```rust
use proc_macro::{TokenStream, TokenTree};

fn analyze_stream(stream: TokenStream) {
    for token in stream {
        match token {
            TokenTree::Group(g) => {
                println!("Group with delimiter {:?}", g.delimiter());
                // Recursively analyze inner tokens
                analyze_stream(g.stream());
            }
            TokenTree::Ident(i) => {
                println!("Identifier: {}", i);
            }
            TokenTree::Punct(p) => {
                println!("Punctuation: {} (spacing: {:?})", 
                    p.as_char(), p.spacing());
            }
            TokenTree::Literal(l) => {
                println!("Literal: {}", l);
            }
        }
    }
}
```

**Building TokenStreams:**

```rust
use proc_macro::{TokenStream, TokenTree, Ident, Span};
use std::str::FromStr;

fn build_stream() -> TokenStream {
    let mut tokens = Vec::new();
    
    // Add identifier
    tokens.push(TokenTree::Ident(
        Ident::new("struct", Span::call_site())
    ));
    
    // Add identifier
    tokens.push(TokenTree::Ident(
        Ident::new("Point", Span::call_site())
    ));
    
    // Create from string
    let from_string: TokenStream = "{ x: i32, y: i32 }".parse().unwrap();
    
    tokens.extend(from_string);
    
    tokens.into_iter().collect()
}
```

### 8.4.2.3 Parsing with syn

The `syn` crate provides powerful parsing capabilities:

**Basic Derive Input Parsing:**

```rust
use syn::{parse_macro_input, DeriveInput, Data, Fields};
use quote::quote;

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // Parse the input into DeriveInput
    let input = parse_macro_input!(input as DeriveInput);
    
    // Extract struct name
    let struct_name = &input.ident;
    let builder_name = format_ident!("{}Builder", struct_name);
    
    // Analyze the data structure
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            Fields::Unnamed(_) => panic!("Unnamed fields not supported"),
            Fields::Unit => panic!("Unit structs not supported"),
        },
        Data::Enum(_) => panic!("Enums not supported"),
        Data::Union(_) => panic!("Unions not supported"),
    };
    
    // Generate builder methods for each field
    let builder_methods = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! {
            pub fn #name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        }
    });
    
    // Generate the builder struct
    let expanded = quote! {
        pub struct #builder_name {
            #( #fields: Option<#field_types> ),*
        }
        
        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #( #field_names: None ),*
                }
            }
            
            #(#builder_methods)*
            
            pub fn build(self) -> Result<#struct_name, String> {
                Ok(#struct_name {
                    #( #field_names: self.#field_names.ok_or_else(
                        || format!("{} not set", stringify!(#field_names))
                    )? ),*
                })
            }
        }
    };
    
    expanded.into()
}
```

**Advanced Parsing:**

```rust
use syn::{Attribute, Meta, NestedMeta, Lit, Expr};

// Parse helper attributes
fn parse_attributes(attrs: &[Attribute]) -> Result<Config, syn::Error> {
    let mut config = Config::default();
    
    for attr in attrs {
        if !attr.path.is_ident("my_trait") {
            continue;
        }
        
        let meta = attr.parse_meta()?;
        
        match meta {
            Meta::List(list) => {
                for nested in list.nested {
                    match nested {
                        NestedMeta::Meta(Meta::Path(path)) => {
                            if path.is_ident("skip") {
                                config.skip = true;
                            }
                        }
                        NestedMeta::Meta(Meta::NameValue(nv)) => {
                            if nv.path.is_ident("rename") {
                                if let Lit::Str(s) = nv.lit {
                                    config.rename = Some(s.value());
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    
    Ok(config)
}
```

### 8.4.2.4 proc_macro2: The Enhanced TokenStream

The `proc_macro2` crate provides an improved `TokenStream` that works outside the compiler:

```rust
use proc_macro2::{TokenStream, Span, Ident};
use quote::{quote, format_ident};

// Works in build scripts, tests, and main code
fn generate_code() -> TokenStream {
    let name = format_ident!("MyStruct");
    let field_name = Ident::new("field", Span::call_site());
    
    quote! {
        struct #name {
            #field_name: i32,
        }
        
        impl #name {
            fn new() -> Self {
                Self { #field_name: 0 }
            }
        }
    }
}
```

**Key Differences from proc_macro:**

| Feature | proc_macro | proc_macro2 |
|---------|------------|-------------|
| Availability | Compiler only | Anywhere |
| Span stability | Less stable | More stable |
| Testing | Difficult | Easy |
| Source maps | Limited | Better |

**Converting Between Types:**

```rust
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::TokenStream as TokenStream2;

// Into proc_macro2
let stream2: TokenStream2 = stream1.into();

// Back to proc_macro
let stream1: TokenStream1 = stream2.into();
```

## 8.4.3 Hygiene

**Theorem MACRO-HYGIENE** (Lexical Scoping Preservation):
> Well-implemented procedural macros respect lexical scoping, ensuring that identifiers generated by the macro do not accidentally capture or shadow identifiers from the macro call site, and vice versa.

### 8.4.3.1 Understanding Hygiene

Hygiene in macros ensures that identifiers maintain their proper scope:

```rust
// Without hygiene issues
macro_rules! declare_x {
    () => {
        let x = 42;
    };
}

fn main() {
    declare_x!();
    println!("{}", x); // ERROR: x not found in scope
}
```

With proc macros, we must be more careful:

```rust
use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn declare_x(input: TokenStream) -> TokenStream {
    // DANGEROUS: Creates hygiene issues
    quote! {
        let x = 42;
    }.into()
}
```

### 8.4.3.2 Span Tracking

**Def Site vs Call Site:**

```rust
use proc_macro2::Span;
use quote::quote;

// Call site span - inherits hygiene from where macro is invoked
let call_site = Span::call_site();

// Def site span - hygiene from macro definition (unstable)
// let def_site = Span::def_site();

// Mixed span - preserves context
let mixed = Span::mixed_site();
```

**Practical Hygiene:**

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::Ident;
use proc_macro2::Span;

#[proc_macro]
pub fn generate_accessor(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::Ident);
    let field_name = input.to_string();
    
    // Generate a method name with hygiene
    let method_name = format_ident!("get_{}", field_name);
    
    // Use call_site for the generated identifier
    let method_ident = Ident::new(&method_name.to_string(), Span::call_site());
    
    quote! {
        pub fn #method_ident(&self) -> &str {
            &self.#input
        }
    }.into()
}
```

### 8.4.3.3 Error Message Attribution

Proper span handling ensures errors point to the right location:

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    // Check for unsupported features
    match &input.data {
        syn::Data::Enum(e) => {
            for variant in &e.variants {
                if variant.fields.is_empty() {
                    // Error points to specific variant
                    return syn::Error::new(
                        variant.span(),
                        "Empty enum variants not supported"
                    ).to_compile_error().into();
                }
            }
        }
        _ => {}
    }
    
    // ... rest of implementation
    quote! {}.into()
}
```

**Theorem ERROR-ATTRIBUTION** (Precise Error Localization):
> Proc macros that preserve original token spans enable the compiler to generate error messages that accurately point to the source of the problem in user code, rather than pointing to macro-generated code.

## 8.4.4 Counter-Examples

The following counter-examples demonstrate common pitfalls and edge cases in proc macro development.

### Counter-Example 1: Name Capture (Hygienic Failure)

```rust
// proc_macro crate
use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn declare_variable(_input: TokenStream) -> TokenStream {
    // PROBLEM: Hardcoded identifier without hygiene
    quote! {
        let temp = 42;
    }.into()
}

// User code
fn main() {
    let temp = "hello";  // User-defined variable
    
    my_macro::declare_variable! {};  // Declares another 'temp'
    
    println!("{}", temp);  // Which 'temp'? Compiler error!
}
```

**Issue**: The macro declares a variable `temp` which may conflict with user code.

**Solution**: Use hygienic identifiers or unique naming conventions.

```rust
#[proc_macro]
pub fn declare_variable_fixed(_input: TokenStream) -> TokenStream {
    // Use a unique prefix to avoid conflicts
    quote! {
        let __my_macro_internal_temp = 42;
    }.into()
}
```

### Counter-Example 2: Shadowing in Generated Code

```rust
// PROBLEM: Generated code shadows user variables
#[proc_macro]
pub fn with_logging(input: TokenStream) -> TokenStream {
    let func: syn::ItemFn = syn::parse(input).unwrap();
    let func_name = &func.sig.ident;
    let block = &func.block;
    
    quote! {
        fn #func_name() {
            let start = std::time::Instant::now();  // Shadows user's 'start'
            let result = { #block };
            println!("Time: {:?}", start.elapsed());
            result
        }
    }.into()
}

// User code
fn main() {
    with_logging! {
        fn compute() -> i32 {
            let start = 10;  // This is shadowed!
            start + 5
        }
    }
}
```

**Issue**: Internal variable names shadow user variables.

**Solution**: Use unique internal variable names.

```rust
quote! {
    fn #func_name() {
        let __my_macro_start = std::time::Instant::now();
        let __my_macro_result = { #block };
        println!("Time: {:?}", __my_macro_start.elapsed());
        __my_macro_result
    }
}.into()
```

### Counter-Example 3: Type Inference Failure

```rust
// PROBLEM: Generated code relies on type inference
#[proc_macro_derive(DefaultBuilder)]
pub fn derive_default_builder(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = &input.ident;
    
    quote! {
        impl #name {
            pub fn builder() -> Self {
                Self::default()  // Requires Default trait
            }
        }
    }.into()
}

// User code - FAILS
#[derive(DefaultBuilder)]
struct Config {
    value: i32,
}
// Error: no method named `default` found for struct `Config`
```

**Issue**: Generated code assumes `Default` is implemented but doesn't add the bound.

**Solution**: Add proper trait bounds.

```rust
quote! {
    impl #name where #name: Default {
        pub fn builder() -> Self {
            Self::default()
        }
    }
}.into()
```

### Counter-Example 4: Wrong Token Spacing

```rust
// PROBLEM: Incorrect punctuation spacing
use proc_macro::{TokenStream, Punct, Spacing};
use quote::quote;

#[proc_macro]
pub fn make_range(input: TokenStream) -> TokenStream {
    let expr: syn::Expr = syn::parse(input).unwrap();
    
    // WRONG: Creates `0 .. 10` instead of `0..10`
    quote! {
        (0 .. #expr)  // Space after 0!
    }.into()
}

// Actually, quote! handles spacing correctly, but manual construction:
use proc_macro2::{Punct, Spacing};

fn wrong_spacing() -> TokenStream {
    let mut tokens = Vec::new();
    tokens.push(TokenTree::Literal(Literal::i32_unsuffixed(0)));
    
    // WRONG: Spacing::Alone creates space
    let dot1 = Punct::new('.', Spacing::Alone);
    let dot2 = Punct::new('.', Spacing::Alone);
    
    tokens.push(TokenTree::Punct(dot1));
    tokens.push(TokenTree::Punct(dot2));
    
    // Results in `0 . . 10` - syntax error!
    tokens.into_iter().collect()
}
```

**Issue**: Manual token construction requires proper spacing.

**Solution**: Use `quote!` or set spacing correctly.

```rust
let dot1 = Punct::new('.', Spacing::Joint);  // Glued to next token
let dot2 = Punct::new('.', Spacing::Joint);
```

### Counter-Example 5: Missing Span Information

```rust
// PROBLEM: Errors don't point to correct location
#[proc_macro_derive(Validate)]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    // Wrong: Using call_site for all errors
    if !has_required_attr(&input) {
        return syn::Error::new(
            Span::call_site(),  // Points to derive macro, not struct
            "Missing required attribute"
        ).to_compile_error().into();
    }
    
    quote! {}.into()
}

// User sees:
// error: Missing required attribute
//   --> src/main.rs:5:10
//    |
// 5  | #[derive(Validate)]
//    |          ^^^^^^^^
//    |
```

**Issue**: Error points to derive macro, not the actual problem location.

**Solution**: Use the input's span.

```rust
if !has_required_attr(&input) {
    return syn::Error::new(
        input.ident.span(),  // Points to struct name
        "Missing required attribute"
    ).to_compile_error().into();
}
```

### Counter-Example 6: Compile Error at Wrong Location

```rust
// PROBLEM: Generated code errors in wrong place
#[proc_macro]
pub fn bad_assert(input: TokenStream) -> TokenStream {
    let expr: syn::Expr = syn::parse(input).unwrap();
    
    quote! {
        if !(#expr) {
            panic!("Assertion failed");
        }
    }.into()
}

// User code:
bad_assert!(1 + 1 == 3);
// Error points inside the macro-generated if block, 
// not to the user's assertion
```

**Issue**: Panic location is inside generated code.

**Solution**: Use `panic!` with file!() and line!() or track spans.

```rust
quote! {
    {
        let __result = #expr;
        if !__result {
            panic!(
                "Assertion failed at {}:{}",
                file!(),
                line!()
            );
        }
    }
}.into()
```

### Counter-Example 7: Recursive Macro Expansion

```rust
// PROBLEM: Uncontrolled recursion
#[proc_macro]
pub fn recursive_macro(input: TokenStream) -> TokenStream {
    let depth: usize = input.to_string().parse().unwrap_or(0);
    
    if depth == 0 {
        quote! { 42 }.into()
    } else {
        // Calls itself with depth-1
        let inner = recursive_macro(
            (depth - 1).to_string().parse().unwrap()
        );
        
        quote! {
            { #inner }
        }.into()
    }
}

// This will fail at large depths due to:
// 1. TokenStream size limits
// 2. Compile time explosion
// 3. Stack overflow in macro expansion
```

**Issue**: Recursive macros can cause exponential code growth.

**Solution**: Limit recursion depth or use iterative approaches.

```rust
#[proc_macro]
pub fn limited_recursive(input: TokenStream) -> TokenStream {
    const MAX_DEPTH: usize = 10;
    
    let depth: usize = input.to_string().parse().unwrap_or(0);
    
    if depth > MAX_DEPTH {
        return syn::Error::new(
            Span::call_site(),
            format!("Recursion depth {} exceeds maximum {}", depth, MAX_DEPTH)
        ).to_compile_error().into();
    }
    
    // ... rest of implementation
}
```

### Counter-Example 8: Infinite Loop in Macro

```rust
// PROBLEM: Infinite loop during macro processing
use proc_macro::TokenStream;

#[proc_macro]
pub fn infinite_loop(input: TokenStream) -> TokenStream {
    loop {
        // Some condition that never becomes true
        if should_break(&input) {
            break;
        }
        
        // Process tokens...
        // But we forgot to update the state!
    }
    
    input
}
```

**Issue**: Macro never terminates.

**Solution**: Add iteration limits and progress checks.

```rust
#[proc_macro]
pub fn safe_loop(input: TokenStream) -> TokenStream {
    const MAX_ITERATIONS: usize = 1000;
    let mut iterations = 0;
    let mut current = input;
    
    loop {
        iterations += 1;
        
        if iterations > MAX_ITERATIONS {
            return syn::Error::new(
                Span::call_site(),
                "Macro expansion exceeded iteration limit"
            ).to_compile_error().into();
        }
        
        if should_break(&current) {
            break;
        }
        
        current = process_iteration(current);
    }
    
    current
}
```

### Counter-Example 9: TokenStream Ownership Issues

```rust
// PROBLEM: Consuming TokenStream multiple times
#[proc_macro]
pub fn double_use(input: TokenStream) -> TokenStream {
    // First use
    let parsed1: syn::Expr = syn::parse(input.clone())
        .expect("Failed to parse");
    
    // Second use - fails because input was consumed
    let parsed2: syn::Expr = syn::parse(input)  // ERROR!
        .expect("Failed to parse");
    
    quote! { (#parsed1, #parsed2) }.into()
}
```

**Issue**: `TokenStream` doesn't implement `Clone` in `proc_macro`.

**Solution**: Convert to `proc_macro2::TokenStream` which is cloneable.

```rust
use proc_macro2::TokenStream as TokenStream2;

#[proc_macro]
pub fn double_use_fixed(input: TokenStream) -> TokenStream {
    let input2: TokenStream2 = input.into();
    
    // Can clone now
    let parsed1: syn::Expr = syn::parse2(input2.clone())?;
    let parsed2: syn::Expr = syn::parse2(input2)?;
    
    quote! { (#parsed1, #parsed2) }.into()
}
```

### Counter-Example 10: Parse Failure Handling

```rust
// PROBLEM: Unhelpful error messages on parse failure
#[proc_macro]
pub fn bad_parse(input: TokenStream) -> TokenStream {
    // Unwrap gives generic error
    let expr: syn::Expr = syn::parse(input).unwrap();
    
    quote! { #expr }.into()
}

// User sees: "called `Result::unwrap()` on an `Err` value"
```

**Issue**: Unhelpful panic message.

**Solution**: Use proper error handling.

```rust
#[proc_macro]
pub fn good_parse(input: TokenStream) -> TokenStream {
    match syn::parse::<syn::Expr>(input) {
        Ok(expr) => quote! { #expr }.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

// Or with the ? operator:
#[proc_macro]
pub fn better_parse(input: TokenStream) -> TokenStream {
    let expr = syn::parse_macro_input!(input as syn::Expr);
    quote! { #expr }.into()
}
```

### Counter-Example 11: Attribute Order Dependency

```rust
// PROBLEM: Attribute order matters unexpectedly
#[proc_macro_attribute]
pub fn measure_time(args: TokenStream, input: TokenStream) -> TokenStream {
    let func: syn::ItemFn = syn::parse(input).unwrap();
    let body = &func.block;
    
    quote! {
        fn #func_name() {
            let start = std::time::Instant::now();
            let result = async { #body }.await;
            println!("Time: {:?}", start.elapsed());
            result
        }
    }.into()
}

// User must write:
#[measure_time]
#[tokio::main]
async fn main() { }

// Writing this fails:
#[tokio::main]
#[measure_time]
async fn main() { }  // ERROR: measure_time doesn't see async
```

**Issue**: Outer attributes may not see modifications by inner attributes.

**Solution**: Document attribute ordering requirements or use multiple passes.

### Counter-Example 12: Generics Handling Error

```rust
// PROBLEM: Incorrect generic handling
#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = &input.ident;
    let generics = &input.generics;
    
    // WRONG: Doesn't preserve generics properly
    quote! {
        impl Serialize for #name {  // Missing generics!
            fn serialize(&self) -> String {
                format!("{:?}", self)
            }
        }
    }.into()
}

// User code fails:
#[derive(Serialize)]
struct Container<T> {
    data: T,
}
// Error: wrong number of type arguments
```

**Issue**: Generics are not preserved in the generated impl block.

**Solution**: Use `split_for_impl`.

```rust
let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

quote! {
    impl #impl_generics Serialize for #name #ty_generics #where_clause {
        fn serialize(&self) -> String {
            format!("{:?}", self)
        }
    }
}.into()
```

### Counter-Example 13: Lifetime Elision Failure

```rust
// PROBLEM: Incorrect lifetime handling
#[proc_macro_derive(GetRef)]
pub fn derive_get_ref(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    if let syn::Data::Struct(s) = &input.data {
        if let syn::Fields::Named(fields) = &s.fields {
            let first_field = fields.named.first().unwrap();
            let field_name = &first_field.ident;
            let field_ty = &first_field.ty;
            let struct_name = &input.ident;
            
            // WRONG: Lifetime not declared
            quote! {
                impl #struct_name {
                    fn get_ref(&self) -> &#field_ty {  // Missing lifetime!
                        &self.#field_name
                    }
                }
            }.into()
        } else { quote!{}.into() }
    } else { quote!{}.into() }
}
```

**Issue**: Lifetime elision doesn't work in generated code the same way.

**Solution**: Explicitly declare lifetimes.

```rust
quote! {
    impl<'a> #struct_name {
        fn get_ref(&'a self) -> &'a #field_ty {
            &self.#field_name
        }
    }
}.into()
```

### Counter-Example 14: Where Clause Omission

```rust
// PROBLEM: Where clauses dropped
#[proc_macro_derive(Comparable)]
pub fn derive_comparable(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = &input.ident;
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    // WRONG: Using where_clause from generics without modification
    // but the generated code needs additional bounds
    
    quote! {
        impl #impl_generics PartialOrd for #name #ty_generics #where_clause {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                // Implementation assumes PartialOrd bounds on fields
                // but where_clause might not have them!
            }
        }
    }.into()
}
```

**Issue**: Generated impl requires bounds not present in original where clause.

**Solution**: Build proper where clause with required bounds.

```rust
use syn::parse_quote;

// Build modified where clause
let mut generics = input.generics.clone();
generics.make_where_clause().predicates.push(parse_quote! {
    Self: PartialOrd
});

let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

quote! {
    impl #impl_generics PartialOrd for #name #ty_generics #where_clause {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            // Now properly bounded
        }
    }
}.into()
```

### Counter-Example 15: Const Generic Issues

```rust
// PROBLEM: Const generics not handled
#[proc_macro_derive(PrintSize)]
pub fn derive_print_size(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = &input.ident;
    
    // WRONG: Doesn't account for const generics
    quote! {
        impl #name {
            fn print_size(&self) {
                println!("Size: {}", std::mem::size_of::<Self>());
            }
        }
    }.into()
}

// User code:
#[derive(PrintSize)]
struct Buffer<const N: usize> {
    data: [u8; N],
}
// ERROR: missing generics for struct `Buffer`
```

**Issue**: Const generics require the same handling as type generics.

**Solution**: Properly handle all generic parameters including const.

```rust
let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

quote! {
    impl #impl_generics #name #ty_generics #where_clause {
        fn print_size(&self) {
            println!("Size: {}", std::mem::size_of::<Self>());
        }
    }
}.into()
```

### Counter-Example 16: Attribute Parsing Error

```rust
// PROBLEM: Incorrect attribute parsing
#[proc_macro_derive(Config, attributes(config))]
pub fn derive_config(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    for attr in &input.attrs {
        // WRONG: This checks all attributes, not just config
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    // This might match non-config attributes!
                }
                _ => {}
            }
        }
    }
    
    quote! {}.into()
}
```

**Issue**: Parsing all attributes instead of filtering by path.

**Solution**: Filter by attribute path.

```rust
for attr in &input.attrs {
    if !attr.path.is_ident("config") {
        continue;  // Skip non-config attributes
    }
    
    // Now safe to parse config-specific attributes
    let meta = attr.parse_meta()?;
    // ...
}
```

### Counter-Example 17: Field Attribute Handling

```rust
// PROBLEM: Missing field attributes in derive
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    if let syn::Data::Struct(data) = &input.data {
        for field in data.fields.iter() {
            // WRONG: Doesn't check for #[builder(skip)]
            let name = &field.ident;
            let ty = &field.ty;
            
            // Generates builder method even for skipped fields
        }
    }
    
    quote! {}.into()
}
```

**Issue**: Field-level helper attributes are ignored.

**Solution**: Parse field attributes.

```rust
for field in data.fields.iter() {
    let mut skip = false;
    
    for attr in &field.attrs {
        if attr.path.is_ident("builder") {
            if let Ok(meta) = attr.parse_meta() {
                if let syn::Meta::List(list) = meta {
                    for nested in &list.nested {
                        if let syn::NestedMeta::Meta(syn::Meta::Path(path)) = nested {
                            if path.is_ident("skip") {
                                skip = true;
                            }
                        }
                    }
                }
            }
        }
    }
    
    if skip {
        continue;
    }
    
    // Generate builder method only for non-skipped fields
}
```

### Counter-Example 18: TokenStream Size Limits

```rust
// PROBLEM: Generating excessively large TokenStream
#[proc_macro]
pub fn generate_massive(input: TokenStream) -> TokenStream {
    let count: usize = input.to_string().parse().unwrap_or(1000);
    
    let mut items = Vec::new();
    
    // Generate thousands of functions
    for i in 0..count {
        let func_name = format_ident!("func_{}", i);
        items.push(quote! {
            fn #func_name() -> i32 { #i }
        });
    }
    
    // This can exceed compiler limits
    quote! { #(#items)* }.into()
}
```

**Issue**: Generated code size can exceed compiler or LLVM limits.

**Solution**: Limit generated code size and document limits.

```rust
const MAX_FUNCTIONS: usize = 100;

#[proc_macro]
pub fn generate_limited(input: TokenStream) -> TokenStream {
    let count: usize = input.to_string().parse().unwrap_or(10);
    
    if count > MAX_FUNCTIONS {
        return syn::Error::new(
            Span::call_site(),
            format!("Cannot generate more than {} functions", MAX_FUNCTIONS)
        ).to_compile_error().into();
    }
    
    // ... generate with limit
}
```

### Counter-Example 19: Visibility Handling

```rust
// PROBLEM: Ignoring visibility modifiers
#[proc_macro_derive(PublicAccessor)]
pub fn derive_public_accessor(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    
    if let syn::Data::Struct(s) = &input.data {
        if let syn::Fields::Named(fields) = &s.fields {
            let first = fields.named.first().unwrap();
            let name = &first.ident;
            let ty = &first.ty;
            let struct_name = &input.ident;
            
            // WRONG: Always generates public accessor
            quote! {
                impl #struct_name {
                    pub fn #name(&self) -> &#ty {
                        &self.#name
                    }
                }
            }.into()
        } else { quote!{}.into() }
    } else { quote!{}.into() }
}
```

**Issue**: Ignores the field's visibility, potentially exposing private fields.

**Solution**: Respect original visibility or add checks.

```rust
let vis = &first.vis;  // Get field visibility

quote! {
    impl #struct_name {
        #vis fn #name(&self) -> &#ty {
            &self.#name
        }
    }
}.into()
```

### Counter-Example 20: Path Resolution Issues

```rust
// PROBLEM: Assumes types are in scope
#[proc_macro_derive(Wrapper)]
pub fn derive_wrapper(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    let name = &input.ident;
    
    // WRONG: Assumes Vec is in scope
    quote! {
        struct #name {
            items: Vec<i32>,  // Might not be available!
        }
    }.into()
}

// User code:
mod inner {
    #[derive(Wrapper)]
    pub struct MyWrapper;  // ERROR: Vec not in scope
}
```

**Issue**: Generated code assumes certain types are imported.

**Solution**: Use fully qualified paths.

```rust
quote! {
    struct #name {
        items: ::std::vec::Vec<i32>,  // Fully qualified
    }
}.into()
```

## 8.4.5 Derive Macro Deep Dive

### 8.4.5.1 Anatomy of a Derive Macro

**Theorem DERIVE-COMPLETENESS**:
> A complete derive macro implementation must handle:
> 1. Structs (named, tuple, unit)
> 2. Enums (with variants and fields)
> 3. Unions
> 4. Generics (type, lifetime, const)
> 5. Where clauses
> 6. Helper attributes
> 7. Visibility modifiers

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, DeriveInput, Data, Fields, Generics, GenericParam};

#[proc_macro_derive(CustomDebug, attributes(debug))]
pub fn derive_custom_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let struct_name = &input.ident;
    let generics = &input.generics;
    
    // Handle different data types
    let implementation = match &input.data {
        Data::Struct(data) => {
            implement_struct(struct_name, &data.fields, generics)
        }
        Data::Enum(data) => {
            implement_enum(struct_name, &data.variants, generics)
        }
        Data::Union(_) => {
            return syn::Error::new(
                input.ident.span(),
                "CustomDebug does not support unions"
            ).to_compile_error().into();
        }
    };
    
    implementation
}
```

### 8.4.5.2 Helper Attributes Implementation

Helper attributes provide customization points for derive macros:

```rust
// Definition in macro
#[proc_macro_derive(MyTrait, attributes(my_trait))]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    // ...
}

// Usage in user code
#[derive(MyTrait)]
#[my_trait(skip_debug)]
#[my_trait(rename = "CustomName")]
struct MyStruct {
    #[my_trait(ignore)]
    internal_field: i32,
    
    #[my_trait(format = "{:?}")]
    display_field: String,
}
```

**Complete Helper Attribute Parser:**

```rust
use syn::{Attribute, Meta, NestedMeta, Lit, Expr};

#[derive(Debug, Default)]
struct FieldConfig {
    skip: bool,
    rename: Option<String>,
    format: Option<String>,
    default_value: Option<Expr>,
}

fn parse_field_attrs(attrs: &[Attribute]) -> Result<FieldConfig, syn::Error> {
    let mut config = FieldConfig::default();
    
    for attr in attrs {
        if !attr.path.is_ident("my_trait") {
            continue;
        }
        
        let meta = attr.parse_meta()?;
        
        match meta {
            Meta::List(list) => {
                for nested in list.nested {
                    match nested {
                        NestedMeta::Meta(Meta::Path(path)) => {
                            if path.is_ident("skip") {
                                config.skip = true;
                            }
                        }
                        NestedMeta::Meta(Meta::NameValue(nv)) => {
                            match nv.lit {
                                Lit::Str(s) if nv.path.is_ident("rename") => {
                                    config.rename = Some(s.value());
                                }
                                Lit::Str(s) if nv.path.is_ident("format") => {
                                    config.format = Some(s.value());
                                }
                                _ => {
                                    return Err(syn::Error::new(
                                        nv.span(),
                                        "Unexpected attribute value"
                                    ));
                                }
                            }
                        }
                        NestedMeta::Meta(Meta::List(list)) => {
                            if list.path.is_ident("default") {
                                // Parse default expression
                                for item in list.nested {
                                    if let NestedMeta::Lit(Lit::Str(s)) = item {
                                        config.default_value = Some(s.parse()?);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    
    Ok(config)
}
```

### 8.4.5.3 Complete Derive Implementation

Here's a complete, production-ready derive macro for a custom trait:

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{
    parse_macro_input, DeriveInput, Data, Fields, GenericParam, 
    Generics, Index, Ident, Type
};

#[proc_macro_derive(Reflect, attributes(reflect))]
pub fn derive_reflect(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let struct_name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    
    let implementation = match &input.data {
        Data::Struct(data) => {
            implement_reflect_struct(struct_name, &data.fields, &input.generics)
        }
        Data::Enum(data) => {
            implement_reflect_enum(struct_name, &data.variants, &input.generics)
        }
        Data::Union(_) => {
            return syn::Error::new(
                input.ident.span(),
                "Reflect does not support unions"
            ).to_compile_error().into();
        }
    };
    
    implementation
}

fn implement_reflect_struct(
    name: &Ident,
    fields: &Fields,
    generics: &Generics
) -> TokenStream {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    let field_info = match fields {
        Fields::Named(named) => {
            let infos = named.named.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let field_type = &f.ty;
                let field_name_str = field_name.to_string();
                
                quote! {
                    FieldInfo {
                        name: #field_name_str,
                        type_name: std::any::type_name::<#field_type>(),
                        getter: |obj: &dyn std::any::Any| {
                            obj.downcast_ref::<Self>()
                                .map(|s| &s.#field_name as &dyn std::any::Any)
                        },
                    }
                }
            });
            
            quote! {
                vec![#(#infos),*]
            }
        }
        Fields::Unnamed(unnamed) => {
            let infos = unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                let field_type = &f.ty;
                let index = Index::from(i);
                let field_name_str = format!("{}", i);
                
                quote! {
                    FieldInfo {
                        name: #field_name_str,
                        type_name: std::any::type_name::<#field_type>(),
                        getter: |obj: &dyn std::any::Any| {
                            obj.downcast_ref::<Self>()
                                .map(|s| &s.#index as &dyn std::any::Any)
                        },
                    }
                }
            });
            
            quote! {
                vec![#(#infos),*]
            }
        }
        Fields::Unit => {
            quote! { vec![] }
        }
    };
    
    let expanded = quote! {
        impl #impl_generics Reflect for #name #ty_generics #where_clause {
            fn type_name(&self) -> &'static str {
                std::any::type_name::<Self>()
            }
            
            fn fields(&self) -> Vec<FieldInfo> {
                use reflect::FieldInfo;
                #field_info
            }
        }
    };
    
    expanded.into()
}
```

## 8.4.6 Quote and Quasi-Quotation

The `quote!` macro provides quasi-quotation - a way to write code templates that mix literal code with interpolated values.

### 8.4.6.1 Basic Quoting

```rust
use quote::quote;
use proc_macro2::TokenStream;

fn generate_impl(name: &syn::Ident) -> TokenStream {
    quote! {
        impl #name {
            fn hello(&self) {
                println!("Hello from {}", stringify!(#name));
            }
        }
    }
}
```

### 8.4.6.2 Repetition

**Theorem QUOTE-REPETITION** (Repetition Consistency):
> Repetition patterns in `quote!` must use the same number of elements for all interpolated values within the repetition. Mismatched counts result in a compile-time error.

```rust
// Vector of fields
let field_names = vec!["x", "y", "z"];
let field_types = vec!["i32", "i32", "i32"];

let fields: Vec<_> = field_names.iter()
    .zip(&field_types)
    .map(|(name, ty)| {
        let name = format_ident!("{}", name);
        let ty: syn::Type = syn::parse_str(ty).unwrap();
        (name, ty)
    })
    .collect();

// Extract names and types separately for repetition
let names: Vec<_> = fields.iter().map(|(n, _)| n).collect();
let types: Vec<_> = fields.iter().map(|(_, t)| t).collect();

quote! {
    struct Point {
        #( #names: #types ),*  // Repeats for each field
    }
}
```

### 8.4.6.3 Advanced Quoting Patterns

```rust
use quote::{quote, format_ident};

// Conditional quoting
let debug_impl = if cfg!(feature = "debug") {
    quote! { 
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}", self.type_name())
            }
        }
    }
} else {
    quote! {}
};

// Nested quoting
let wrappers: Vec<_> = (0..3)
    .map(|i| {
        let wrapper_name = format_ident!("Wrapper{}", i);
        quote! {
            struct #wrapper_name<T>(T);
        }
    })
    .collect();

let expanded = quote! {
    #(#wrappers)*
};

// Quote with local variables
let local_var = 42;
quote! {
    const VALUE: i32 = #local_var;
};

// Quote blocks
let init_code = quote! {
    let mut x = 0;
    x += 1;
};

quote! {
    fn init() {
        #init_code
    }
};
```

### 8.4.6.4 The quote_spanned! Macro

```rust
use quote::quote_spanned;
use proc_macro2::Span;

// Generate code with specific span for better error messages
let field_span = field.ty.span();

quote_spanned! {field_span=>
    fn get_field(&self) -> #field_type {
        &self.#field_name
    }
}
```

## 8.4.7 Testing Proc Macros

**Theorem MACRO-TESTING** (Comprehensive Macro Testing):
> Proc macros require three levels of testing:
> 1. Unit tests for parsing logic
> 2. Integration tests for generated code correctness
> 3. Compile-fail tests for error message validation

### 8.4.7.1 Unit Testing with syn::parse2

```rust
// In your proc_macro crate's lib.rs or tests/
#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;
    use quote::quote;

    #[test]
    fn test_parse_struct() {
        let input: syn::DeriveInput = parse_quote! {
            struct Point {
                x: i32,
                y: i32,
            }
        };
        
        assert_eq!(input.ident.to_string(), "Point");
        
        if let syn::Data::Struct(data) = input.data {
            assert_eq!(data.fields.len(), 2);
        } else {
            panic!("Expected struct");
        }
    }

    #[test]
    fn test_generated_code() {
        let name = syn::Ident::new("MyStruct", proc_macro2::Span::call_site());
        let expanded = quote! {
            impl #name {
                fn new() -> Self {
                    Self {}
                }
            }
        };
        
        let code = expanded.to_string();
        assert!(code.contains("impl MyStruct"));
        assert!(code.contains("fn new"));
    }
}
```

### 8.4.7.2 Integration Testing

```rust
// tests/integration_test.rs
use my_proc_macro::Builder;

#[derive(Builder)]
struct User {
    name: String,
    age: u32,
}

#[test]
fn test_builder_pattern() {
    let user = User::builder()
        .name("Alice".to_string())
        .age(30)
        .build()
        .unwrap();
    
    assert_eq!(user.name, "Alice");
    assert_eq!(user.age, 30);
}

#[test]
fn test_builder_missing_field() {
    let result = User::builder()
        .name("Bob".to_string())
        .build();
    
    assert!(result.is_err());
}
```

### 8.4.7.3 trybuild for Compile-Fail Tests

`trybuild` is the standard tool for testing that code fails to compile with expected errors:

```toml
# Cargo.toml
[dev-dependencies]
trybuild = { version = "1.0", features = ["diff"] }
```

```rust
// tests/compile_test.rs
#[test]
fn test_compile_failures() {
    let t = trybuild::TestCases::new();
    
    // Tests that fail to compile
    t.compile_fail("tests/compile_fail/*.rs");
    
    // Tests that should compile successfully
    t.pass("tests/pass/*.rs");
}
```

```rust
// tests/compile_fail/missing_attribute.rs
use my_proc_macro::Builder;

#[derive(Builder)]
struct Config {
    value: i32,
}

fn main() {
    // ERROR: required field not set
    let config = Config::builder().build().unwrap();
}
```

```rust
// tests/compile_fail/missing_attribute.stderr
error[E0599]: no method named `value` found for struct `ConfigBuilder`
 --> tests/compile_fail/missing_attribute.rs:9:32
  |
9 |     let config = Config::builder().build().unwrap();
  |                                    ^^^^^ method not found in `ConfigBuilder`
```

### 8.4.7.4 Macrotest for Snapshot Testing

```toml
[dev-dependencies]
macrotest = "1.0"
```

```rust
// tests/macrotest.rs
#[test]
pub fn pass() {
    macrotest::expand("tests/expand/*.rs");
}
```

```rust
// tests/expand/basic.rs
use my_proc_macro::Builder;

#[derive(Builder)]
struct Point {
    x: i32,
    y: i32,
}
```

Generated snapshot:
```rust
// tests/expand/basic.expanded.rs
struct Point {
    x: i32,
    y: i32,
}

struct PointBuilder {
    x: Option<i32>,
    y: Option<i32>,
}

impl PointBuilder {
    fn new() -> Self {
        Self { x: None, y: None }
    }
    
    fn x(mut self, value: i32) -> Self {
        self.x = Some(value);
        self
    }
    
    fn y(mut self, value: i32) -> Self {
        self.y = Some(value);
        self
    }
    
    fn build(self) -> Result<Point, String> {
        Ok(Point {
            x: self.x.ok_or("x not set")?,
            y: self.y.ok_or("y not set")?,
        })
    }
}
```

## 8.4.8 Case Study: Complete Custom Derive

Let's build a complete, production-quality derive macro for a JSON serialization trait.

### 8.4.8.1 Project Structure

```
json-derive/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   ├── parse.rs      # Attribute parsing
│   ├── generate.rs   # Code generation
│   └── utils.rs      # Helper functions
└── tests/
    ├── integration.rs
    ├── compile_fail/
    └── expand/
```

### 8.4.8.2 Cargo.toml

```toml
[package]
name = "json-derive"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
proc-macro2 = "1.0"
quote = "1.0"
syn = { version = "2.0", features = ["full", "extra-traits"] }

[dev-dependencies]
trybuild = "1.0"
serde_json = "1.0"
```

### 8.4.8.3 Main Library

```rust
// src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

mod parse;
mod generate;
mod utils;

use parse::ContainerAttributes;
use generate::generate_to_json;

#[proc_macro_derive(ToJson, attributes(json))]
pub fn derive_to_json(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    
    // Parse container-level attributes
    let attrs = match ContainerAttributes::from_derive_input(&input) {
        Ok(attrs) => attrs,
        Err(e) => return e.to_compile_error().into(),
    };
    
    // Generate the implementation
    match generate_to_json(&input, &attrs) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
```

### 8.4.8.4 Attribute Parsing

```rust
// src/parse.rs
use syn::{Attribute, Meta, NestedMeta, Lit, DeriveInput, Data, Fields};
use quote::quote;

#[derive(Debug, Default)]
pub struct ContainerAttributes {
    pub rename_all: Option<String>,
    pub skip_serializing_none: bool,
}

#[derive(Debug, Default)]
pub struct FieldAttributes {
    pub skip: bool,
    pub rename: Option<String>,
    pub default: Option<syn::Expr>,
    pub skip_serializing_if: Option<String>,
}

impl ContainerAttributes {
    pub fn from_derive_input(input: &DeriveInput) -> syn::Result<Self> {
        let mut attrs = ContainerAttributes::default();
        
        for attr in &input.attrs {
            if !attr.path.is_ident("json") {
                continue;
            }
            
            let meta = attr.parse_meta()?;
            
            if let Meta::List(list) = meta {
                for nested in &list.nested {
                    if let NestedMeta::Meta(Meta::NameValue(nv)) = nested {
                        if nv.path.is_ident("rename_all") {
                            if let Lit::Str(s) = &nv.lit {
                                attrs.rename_all = Some(s.value());
                            }
                        }
                    } else if let NestedMeta::Meta(Meta::Path(path)) = nested {
                        if path.is_ident("skip_serializing_none") {
                            attrs.skip_serializing_none = true;
                        }
                    }
                }
            }
        }
        
        Ok(attrs)
    }
}

impl FieldAttributes {
    pub fn from_field(field: &syn::Field) -> syn::Result<Self> {
        let mut attrs = FieldAttributes::default();
        
        for attr in &field.attrs {
            if !attr.path.is_ident("json") {
                continue;
            }
            
            let meta = attr.parse_meta()?;
            
            if let Meta::List(list) = meta {
                for nested in &list.nested {
                    match nested {
                        NestedMeta::Meta(Meta::Path(path)) => {
                            if path.is_ident("skip") {
                                attrs.skip = true;
                            }
                        }
                        NestedMeta::Meta(Meta::NameValue(nv)) => {
                            if let Lit::Str(s) = &nv.lit {
                                if nv.path.is_ident("rename") {
                                    attrs.rename = Some(s.value());
                                } else if nv.path.is_ident("skip_serializing_if") {
                                    attrs.skip_serializing_if = Some(s.value());
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        
        Ok(attrs)
    }
}

pub fn get_field_name(
    field: &syn::Field,
    attrs: &FieldAttributes,
    container_attrs: &ContainerAttributes,
) -> String {
    // First check field-level rename
    if let Some(rename) = &attrs.rename {
        return rename.clone();
    }
    
    // Then check container-level rename_all
    let base_name = field.ident.as_ref().unwrap().to_string();
    
    if let Some(rule) = &container_attrs.rename_all {
        match rule.as_str() {
            "snake_case" => to_snake_case(&base_name),
            "camelCase" => to_camel_case(&base_name),
            "PascalCase" => to_pascal_case(&base_name),
            "SCREAMING_SNAKE_CASE" => to_screaming_snake_case(&base_name),
            _ => base_name,
        }
    } else {
        base_name
    }
}

fn to_snake_case(s: &str) -> String {
    // Implementation...
    s.to_lowercase()
}

fn to_camel_case(s: &str) -> String {
    // Implementation...
    s.clone()
}

fn to_pascal_case(s: &str) -> String {
    // Implementation...
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase(),
    }
}

fn to_screaming_snake_case(s: &str) -> String {
    s.to_uppercase()
}
```

### 8.4.8.5 Code Generation

```rust
// src/generate.rs
use quote::{quote, format_ident};
use syn::{DeriveInput, Data, Fields, Index};
use crate::parse::{ContainerAttributes, FieldAttributes, get_field_name};

pub fn generate_to_json(
    input: &DeriveInput,
    container_attrs: &ContainerAttributes,
) -> syn::Result<proc_macro2::TokenStream> {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    
    let body = match &input.data {
        Data::Struct(data) => {
            generate_struct_body(&data.fields, container_attrs)?
        }
        Data::Enum(data) => {
            generate_enum_body(&data.variants, container_attrs)?
        }
        Data::Union(_) => {
            return Err(syn::Error::new(
                input.ident.span(),
                "ToJson does not support unions"
            ));
        }
    };
    
    let expanded = quote! {
        impl #impl_generics ToJson for #name #ty_generics #where_clause {
            fn to_json(&self) -> String {
                #body
            }
        }
    };
    
    Ok(expanded)
}

fn generate_struct_body(
    fields: &Fields,
    container_attrs: &ContainerAttributes,
) -> syn::Result<proc_macro2::TokenStream> {
    match fields {
        Fields::Named(named) => {
            let field_entries = named.named.iter().filter_map(|f| {
                let attrs = match FieldAttributes::from_field(f) {
                    Ok(a) => a,
                    Err(e) => return Some(Err(e)),
                };
                
                if attrs.skip {
                    return None;
                }
                
                let field_name = f.ident.as_ref().unwrap();
                let json_name = get_field_name(f, &attrs, container_attrs);
                
                Some(Ok(quote! {
                    entries.push(format!(
                        "\"{}\": {}",
                        #json_name,
                        self.#field_name.to_json()
                    ));
                }))
            }).collect::<Result<Vec<_>, _>>()?;
            
            Ok(quote! {
                let mut entries = Vec::new();
                #(#field_entries)*
                format!("{{{{ }}}}"", entries.join(", "))
            })
        }
        Fields::Unnamed(unnamed) => {
            let field_entries = unnamed.unnamed.iter().enumerate().map(|(i, _)| {
                let index = Index::from(i);
                quote! {
                    self.#index.to_json()
                }
            });
            
            Ok(quote! {
                format!("[{}]", vec![#(#field_entries),*].join(", "))
            })
        }
        Fields::Unit => {
            Ok(quote! {
                "null".to_string()
            })
        }
    }
}

fn generate_enum_body(
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
    _container_attrs: &ContainerAttributes,
) -> syn::Result<proc_macro2::TokenStream> {
    let variant_arms = variants.iter().map(|v| {
        let variant_name = &v.ident;
        
        match &v.fields {
            Fields::Unit => {
                quote! {
                    Self::#variant_name => format!("\"{}\"", stringify!(#variant_name))
                }
            }
            Fields::Unnamed(unnamed) => {
                let field_names: Vec<_> = (0..unnamed.unnamed.len())
                    .map(|i| format_ident!("f{}", i))
                    .collect();
                
                let conversions = field_names.iter().map(|f| {
                    quote! { #f.to_json() }
                });
                
                quote! {
                    Self::#variant_name(#(#field_names),*) => {
                        format!("{{{{\"{}\": [{}]}}}}", 
                            stringify!(#variant_name),
                            vec![#(#conversions),*].join(", ")
                        )
                    }
                }
            }
            Fields::Named(named) => {
                let field_names: Vec<_> = named.named.iter()
                    .map(|f| f.ident.as_ref().unwrap())
                    .collect();
                
                let conversions = field_names.iter().map(|f| {
                    quote! {
                        format!("\"{}\": {}", stringify!(#f), #f.to_json())
                    }
                });
                
                quote! {
                    Self::#variant_name { #(#field_names),* } => {
                        format!("{{{{\"{}\": {{{{}}}}}}}}}"", 
                            stringify!(#variant_name),
                            vec![#(#conversions),*].join(", ")
                        )
                    }
                }
            }
        }
    });
    
    Ok(quote! {
        match self {
            #(#variant_arms),*
        }
    })
}
```

### 8.4.8.6 Integration Tests

```rust
// tests/integration.rs
use json_derive::ToJson;

#[derive(ToJson)]
#[json(rename_all = "camelCase")]
struct Person {
    first_name: String,
    last_name: String,
    #[json(skip)]
    internal_id: u64,
    age: u32,
}

#[derive(ToJson)]
enum Status {
    Active,
    Inactive,
    Pending(String),
}

#[derive(ToJson)]
struct Point(i32, i32);

#[derive(ToJson)]
struct Unit;

#[test]
fn test_struct_with_rename() {
    let person = Person {
        first_name: "Alice".to_string(),
        last_name: "Smith".to_string(),
        internal_id: 12345,
        age: 30,
    };
    
    let json = person.to_json();
    assert!(json.contains("\"firstName\": \"Alice\""));
    assert!(json.contains("\"lastName\": \"Smith\""));
    assert!(!json.contains("internal_id"));
}

#[test]
fn test_enum_variants() {
    let status = Status::Active;
    assert_eq!(status.to_json(), "\"Active\"");
    
    let pending = Status::Pending("review".to_string());
    assert!(pending.to_json().contains("\"Pending\""));
}

#[test]
fn test_tuple_struct() {
    let point = Point(10, 20);
    assert_eq!(point.to_json(), "[10, 20]");
}

#[test]
fn test_unit_struct() {
    let unit = Unit;
    assert_eq!(unit.to_json(), "null");
}
```

### 8.4.8.7 Compile-Fail Tests

```rust
// tests/compile_fail/union.rs
use json_derive::ToJson;

#[derive(ToJson)]
union Value {
    int: i32,
    float: f32,
}

fn main() {}
```

```
// tests/compile_fail/union.stderr
error: ToJson does not support unions
 --> tests/compile_fail/union.rs:4:7
  |
4 | union Value {
  |       ^^^^^
```

## 8.4.9 Best Practices and Guidelines

### 8.4.9.1 Performance Considerations

1. **Minimize TokenStream Cloning**: Clone `proc_macro2::TokenStream` instead of `proc_macro::TokenStream`
2. **Lazy Evaluation**: Only parse what you need
3. **Error Collection**: Collect multiple errors before returning

```rust
// Collect multiple errors
let mut errors = Vec::new();

for field in fields {
    if let Err(e) = validate_field(field) {
        errors.push(e);
    }
}

if !errors.is_empty() {
    // Combine errors
    let combined = errors.into_iter().fold(
        syn::Error::new(Span::call_site(), "Multiple errors"),
        |mut acc, e| { acc.combine(e); acc }
    );
    return combined.to_compile_error().into();
}
```

### 8.4.9.2 Error Handling

```rust
// Use syn::Result for error propagation
fn process_field(field: &syn::Field) -> syn::Result<TokenStream> {
    let attrs = FieldAttributes::from_field(field)?;
    
    if attrs.skip && attrs.rename.is_some() {
        return Err(syn::Error::new(
            field.span(),
            "Cannot use skip with rename"
        ));
    }
    
    // ...
}

// Use quote_spanned! for precise error locations
quote_spanned! {field.ty.span()=>
    fn get(&self) -> #field_type {
        &self.#field_name
    }
}
```

### 8.4.9.3 Documentation

Document your proc macros thoroughly:

```rust
/// Derive macro for the `Builder` trait.
///
/// # Example
///
/// ```
/// use my_crate::Builder;
///
/// #[derive(Builder)]
/// struct Person {
///     name: String,
///     age: u32,
/// }
///
/// let person = Person::builder()
///     .name("Alice".to_string())
///     .age(30)
///     .build()
///     .unwrap();
/// ```
///
/// # Attributes
///
/// - `#[builder(skip)]`: Skip this field in the builder
/// - `#[builder(default = "...")]`: Set a default value
/// - `#[builder(rename = "...")]`: Rename the builder method
#[proc_macro_derive(Builder, attributes(builder))]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // ...
}
```

## 8.4.10 Summary

**Theorem PROC-MACRO-COMPLETENESS**:
> A complete understanding of Rust procedural macros encompasses:
> 1. The three macro types and their appropriate use cases
> 2. TokenStream manipulation and the syn/quote ecosystem
> 3. Hygiene and span preservation
> 4. Common pitfalls and their solutions
> 5. Comprehensive testing strategies
> 6. Performance optimization techniques

Procedural macros are one of Rust's most powerful metaprogramming features. When used correctly, they can:
- Eliminate boilerplate code
- Enforce compile-time invariants
- Create domain-specific languages
- Extend the language with custom semantics

However, they also come with complexity:
- Steeper learning curve than declarative macros
- More code to write and maintain
- Potential for confusing error messages
- Longer compile times

**Guidelines for Proc Macro Usage:**

1. **Start Simple**: Use `macro_rules!` first, upgrade to proc macros only when necessary
2. **Use syn and quote**: Don't parse TokenStreams manually except for simple cases
3. **Preserve Spans**: Always use original token spans for error messages
4. **Test Thoroughly**: Use trybuild and macrotest for comprehensive testing
5. **Document Extensively**: Proc macros are part of your public API
6. **Handle Edge Cases**: Generics, lifetimes, and const generics require special attention

## Further Reading

- [The Rust Reference: Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
- [syn crate documentation](https://docs.rs/syn/)
- [quote crate documentation](https://docs.rs/quote/)
- [proc_macro2 crate documentation](https://docs.rs/proc-macro2/)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [Rust API Guidelines: Macros](https://rust-lang.github.io/api-guidelines/macros.html)
