# 生命周期系统思维导图

> **文档类型**: 🧠 思维导图 | 🗺️ 知识可视化  
> **创建日期**: 2025-10-19  
> **Rust 版本**: 1.90+

---

## 📋 思维导图概览

本思维导图以 **Rust 生命周期系统** 为中心，展开为9个主要分支，涵盖生命周期标注、推断、边界、HRTB等核心概念。

### 核心分支

1. **生命周期基础**: 概念、符号、作用域
2. **标注规则**: 函数、结构体、impl块
3. **省略规则**: 三大规则、自动推断
4. **生命周期边界**: 类型边界、生命周期关系
5. **HRTB**: 高阶生命周期边界
6. **NLL**: 非词法生命周期
7. **借用检查器**: 规则、错误、解决
8. **常见模式**: 自引用、多生命周期
9. **实战技巧**: 调试、优化、最佳实践

---

## 🗺️ 生命周期系统全景图

```mermaid
mindmap
  root((生命周期系统))
    基础概念
      定义
        引用有效性
        作用域
        编译时检查
      符号
        'a 'b 命名
        'static 静态
        '_ 省略/推断
      目的
        防止悬垂指针
        内存安全
        零运行时开销
    
    标注规则
      函数生命周期
        参数引用
          fn foo<'a>(x: &'a str)
        返回引用
          -> &'a str
        多个生命周期
          <'a 'b>
      结构体生命周期
        字段引用
          struct S<'a> { field: &'a T }
        生命周期要求
          结构体 <= 引用
      Impl块生命周期
        impl<'a> S<'a>
        方法生命周期
        关联函数
    
    省略规则
      规则1
        每个引用参数独立生命周期
        fn(x: &str y: &str)
        -> fn<'a 'b>(x: &'a str y: &'b str)
      规则2
        单输入赋给所有输出
        fn(x: &str) -> &str
        -> fn<'a>(x: &'a str) -> &'a str
      规则3
        &self 赋给输出
        fn method(&self) -> &str
        -> fn<'a>(&'a self) -> &'a str
    
    生命周期边界
      类型生命周期
        T: 'a
          T包含 'a引用
        T: 'static
          T无非静态引用
      生命周期关系
        'a: 'b
          'a至少和'b一样长
      组合边界
        T: 'a + Trait
        复合约束
    
    HRTB
      语法
        for<'a>
        对所有生命周期成立
      应用
        闭包特征
          Fn(&'a T)
        高阶函数
      示例
        where F: for<'a> Fn(&'a str) -> usize
    
    NLL
      Rust 2018
        非词法生命周期
        更精确分析
      优势
        减少借用冲突
        更灵活的代码
      示例
        let r = &s;
        println!("{}" r);
        let r2 = &mut s; // ✅
    
    借用检查器
      规则
        同时只能一个可变借用
        或多个不可变借用
        引用必须有效
      错误类型
        悬垂引用
        借用冲突
        生命周期不匹配
      解决策略
        限制作用域
        使用NLL
        重新设计
    
    常见模式
      多生命周期
        fn foo<'a 'b>
        独立生命周期
        关系约束
      自引用结构
        问题
          直接不可行
        解决
          Pin
          重新设计
      静态生命周期
        'static 数据
        全局变量
        字符串字面量
    
    实战技巧
      调试
        显式标注
        分解函数
        使用'static测试
      优化
        减少生命周期参数
        利用省略规则
        避免复杂嵌套
      最佳实践
        优先借用
        生命周期最短化
        避免自引用
```

---

## 核心概念速查

### 生命周期标注

```rust
// 函数生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 结构体生命周期
struct Context<'a> {
    text: &'a str,
}

impl<'a> Context<'a> {
    fn new(text: &'a str) -> Self {
        Context { text }
    }
}
```

### 省略规则

```rust
// 规则2应用
fn first_word(s: &str) -> &str {
    // 自动推断为 fn<'a>(s: &'a str) -> &'a str
    &s[..1]
}

// 规则3应用
impl<'a> Context<'a> {
    fn get_text(&self) -> &str {
        // 自动推断为 -> &'a str
        self.text
    }
}
```

### 生命周期边界

```rust
fn with_bounds<'a, T: 'a>(x: &'a T) -> &'a T
where
    T: std::fmt::Debug,
{
    println!("{:?}", x);
    x
}
```

### HRTB

```rust
fn apply<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> usize,
{
    println!("{}", f("hello"));
}

fn main() {
    apply(|s| s.len());
}
```

### NLL 示例

```rust
fn nll_example() {
    let mut s = String::from("hello");
    
    let r = &s;
    println!("{}", r); // r 最后使用
    
    let r2 = &mut s; // ✅ Rust 2018: 可以
    r2.push_str(" world");
}
```

---

## 学习路径

```mermaid
graph LR
    A[基础概念] --> B[标注规则]
    B --> C[省略规则]
    C --> D[生命周期边界]
    D --> E[NLL]
    E --> F[HRTB]
    F --> G[实战技巧]
    
    style A fill:#e1f5e1
    style G fill:#ffe1e1
```

---

## 🔗 相关文档

- [01_concept_ontology.md](01_concept_ontology.md) - 生命周期概念定义
- [12_lifetime_variance_matrix.md](12_lifetime_variance_matrix.md) - 生命周期型变对比
- [14_ownership_borrowing_matrix.md](14_ownership_borrowing_matrix.md) - 所有权借用
- [Rust Book - Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)

---

**文档状态**: ✅ 已完成  
**最后更新**: 2025-10-19  
**贡献者**: Rust Type System Knowledge Engineering Team

