# 🗺️ Rust 1.90 控制流与函数 - 综合思维导图

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **适用人群**: 初学者到高级开发者

---

## 📋 目录

- [🗺️ Rust 1.90 控制流与函数 - 综合思维导图](#️-rust-190-控制流与函数---综合思维导图)
  - [📋 目录](#-目录)
  - [🌳 整体架构](#-整体架构)
  - [🔀 控制流体系](#-控制流体系)
  - [📞 函数系统](#-函数系统)
  - [🎭 模式匹配](#-模式匹配)
  - [🔒 闭包系统](#-闭包系统)
  - [⚠️ 错误处理](#️-错误处理)
  - [📚 学习路径](#-学习路径)
    - [🌱 初学者路径 (1-2周)](#-初学者路径-1-2周)
    - [⚡ 进阶路径 (1-2周)](#-进阶路径-1-2周)
    - [🎓 专家路径 (2-3周)](#-专家路径-2-3周)
  - [🔍 问题诊断树](#-问题诊断树)
  - [⚖️ 技术选型决策树](#️-技术选型决策树)

---

## 🌳 整体架构

```text
                    Rust 控制流与函数
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
    控制流结构          函数体系           模式匹配
        │                  │                  │
    ┌───┴───┐         ┌────┴────┐       ┌────┴────┐
    │       │         │         │       │         │
   条件    循环      普通函数   闭包     基础      高级
    │       │         │         │       │         │
if/match while    fn定义   Fn/FnMut  let   守卫
let-else  for     泛型     FnOnce   match  解构
         loop    高阶函数  async闭包  if-let
                                    while-let
                  
          ┌──────────────────────────┐
          │      错误处理机制         │
          │                          │
          │  • Result<T, E>          │
          │  • Option<T>             │
          │  • ? 操作符               │
          │  • panic!/unwrap         │
          └──────────────────────────┘
```

---

## 🔀 控制流体系

```text
控制流结构
│
├─ 🎯 条件语句
│  ├─ if 表达式
│  │  ├─ 基本形式: if condition { ... }
│  │  ├─ if-else: if { ... } else { ... }
│  │  ├─ if-else if: if { } else if { } else { }
│  │  └─ if 表达式: let x = if condition { 1 } else { 2 };
│  │     • 所有分支必须返回相同类型
│  │     • 可以用作表达式
│  │
│  ├─ match 表达式
│  │  ├─ 穷尽性检查
│  │  ├─ 模式匹配
│  │  ├─ 守卫 (guard)
│  │  └─ 返回值
│  │     • 编译期保证覆盖所有情况
│  │     • 支持复杂模式
│  │
│  ├─ if let 表达式 (简化的match)
│  │  └─ if let Some(x) = option { ... }
│  │     • 只匹配一个模式
│  │     • 可选的else分支
│  │
│  └─ let else 语句 - Rust 1.65+
│     └─ let Some(x) = option else { return; };
│        • 模式匹配失败时的早期返回
│        • Rust 1.90: 改进的类型推导
│
├─ 🔄 循环语句
│  ├─ loop (无限循环)
│  │  ├─ loop { ... }
│  │  ├─ break: 跳出循环
│  │  ├─ continue: 继续下一次迭代
│  │  └─ break 返回值: loop { break value; }
│  │     • 可以返回值
│  │     • 循环标签: 'label: loop
│  │
│  ├─ while (条件循环)
│  │  ├─ while condition { ... }
│  │  └─ while let pattern = expr { ... }
│  │     • 模式匹配+循环
│  │     • 常用于迭代器
│  │
│  └─ for (迭代循环)
│     ├─ for item in iterator { ... }
│     ├─ for (i, item) in iter.enumerate() { ... }
│     └─ for i in 0..10 { ... }
│        • 最安全的循环方式
│        • 自动处理边界
│        • 使用迭代器协议
│
└─ ⚡ 控制流关键字
   ├─ break: 跳出循环
   │  └─ 可选标签: break 'label;
   │  └─ 可选返回值: break value;
   │
   ├─ continue: 跳过本次迭代
   │  └─ 可选标签: continue 'label;
   │
   └─ return: 函数返回
      └─ return value; 或隐式返回
```

---

## 📞 函数系统

```text
函数体系
│
├─ 📝 函数定义
│  ├─ 基本语法
│  │  └─ fn function_name(param: Type) -> ReturnType { ... }
│  │     • fn 关键字
│  │     • 参数类型必须标注
│  │     • 返回类型（可选）
│  │
│  ├─ 参数传递
│  │  ├─ 值传递: fn foo(x: i32)
│  │  ├─ 引用传递: fn foo(x: &i32)
│  │  ├─ 可变引用: fn foo(x: &mut i32)
│  │  └─ 所有权转移: fn foo(x: String)
│  │
│  ├─ 返回值
│  │  ├─ 显式返回: return value;
│  │  ├─ 隐式返回: 表达式（无分号）
│  │  └─ 单元类型: () 或不写
│  │
│  └─ 函数指针
│     └─ fn(i32) -> i32
│        • 可以存储和传递
│        • 实现了 Fn traits
│
├─ 🎯 泛型函数
│  ├─ 类型参数: fn foo<T>(x: T)
│  ├─ 约束: fn foo<T: Display>(x: T)
│  ├─ where子句: fn foo<T>(x: T) where T: Display
│  └─ 多个类型参数: fn foo<T, U>(x: T, y: U)
│
├─ 🔝 高阶函数
│  ├─ 接受函数作为参数
│  │  └─ fn apply<F>(f: F, x: i32) where F: Fn(i32) -> i32
│  │
│  ├─ 返回函数
│  │  ├─ fn returns_fn() -> fn(i32) -> i32
│  │  └─ fn returns_closure() -> impl Fn(i32) -> i32
│  │
│  └─ 函数组合
│     └─ fn compose<F, G>(f: F, g: G) -> impl Fn(i32) -> i32
│
├─ 🔁 递归函数
│  ├─ 直接递归
│  ├─ 尾递归优化
│  └─ 相互递归
│     • 注意栈溢出
│     • 考虑迭代替代
│
└─ ⚡ 方法
   ├─ 关联函数: impl Type { fn new() -> Self }
   ├─ 方法: impl Type { fn method(&self) }
   ├─ 可变方法: impl Type { fn method(&mut self) }
   └─ 消耗self: impl Type { fn method(self) }
```

---

## 🎭 模式匹配

```text
模式匹配系统
│
├─ 📌 基础模式
│  ├─ 字面量模式
│  │  └─ 1, "hello", true
│  │
│  ├─ 变量模式
│  │  └─ x, name, _
│  │
│  ├─ 通配符
│  │  ├─ _ (忽略值)
│  │  └─ .. (忽略剩余部分)
│  │
│  └─ 引用模式
│     ├─ &pattern
│     └─ &mut pattern
│
├─ 🎯 结构化模式
│  ├─ 元组模式
│  │  └─ (x, y, z)
│  │  └─ (first, .., last)
│  │
│  ├─ 结构体模式
│  │  ├─ Point { x, y }
│  │  ├─ Point { x: a, y: b }
│  │  └─ Point { x, .. }
│  │
│  ├─ 枚举模式
│  │  ├─ Some(x)
│  │  ├─ Ok(value)
│  │  └─ Message::Write(text)
│  │
│  └─ 数组/切片模式
│     ├─ [a, b, c]
│     └─ [first, rest @ ..]
│
├─ ⚡ 高级模式
│  ├─ 范围模式
│  │  ├─ 1..=5
│  │  └─ 'a'..='z'
│  │
│  ├─ 守卫 (Guard)
│  │  └─ Some(x) if x > 10
│  │     • 额外的条件判断
│  │     • 可以访问外部变量
│  │
│  ├─ @ 绑定
│  │  └─ x @ 1..=5
│  │     • 绑定值的同时匹配模式
│  │
│  └─ | 或模式
│     └─ 1 | 2 | 3
│        • 匹配多个模式
│
└─ 📍 使用场景
   ├─ match 表达式
   ├─ if let 表达式
   ├─ while let 循环
   ├─ for 循环
   ├─ let 语句
   └─ 函数参数
```

---

## 🔒 闭包系统

```text
闭包 (Closure)
│
├─ 📝 定义语法
│  ├─ 基本形式: |param| expr
│  ├─ 带类型标注: |param: Type| -> ReturnType { body }
│  ├─ 多个参数: |x, y| x + y
│  └─ 无参数: || println!("hello")
│     • 类型推导
│     • 捕获环境
│
├─ 🎯 捕获模式
│  ├─ 不可变借用
│  │  └─ let f = |x| x + y;
│  │     • 闭包实现 Fn trait
│  │     • 可以多次调用
│  │
│  ├─ 可变借用
│  │  └─ let mut f = |x| { list.push(x); };
│  │     • 闭包实现 FnMut trait
│  │     • 需要 mut 声明
│  │
│  └─ 所有权转移
│     └─ let f = move |x| vec.push(x);
│        • 闭包实现 FnOnce trait
│        • move 关键字
│        • 只能调用一次（如果消耗了捕获值）
│
├─ 🏷️ Trait 层次
│  └─ FnOnce (基础)
│     └─ FnMut (继承 FnOnce)
│        └─ Fn (继承 FnMut)
│           • Fn: 不可变借用环境
│           • FnMut: 可变借用环境
│           • FnOnce: 消耗环境
│
├─ ⚡ Rust 1.90 特性
│  ├─ async 闭包 - Rust 1.90+
│  │  └─ let f = async |x| { fetch(x).await };
│  │     • 异步闭包
│  │     • 返回 Future
│  │
│  └─ 改进的类型推导
│     • 更好的闭包类型推导
│     • 减少显式类型标注
│
└─ 📊 使用场景
   ├─ 迭代器方法
   │  ├─ map, filter, fold
   │  └─ for_each, any, all
   │
   ├─ 回调函数
   ├─ 延迟计算
   └─ 自定义控制流
```

---

## ⚠️ 错误处理

```text
错误处理机制
│
├─ 🎯 Result<T, E>
│  ├─ Ok(value): 成功
│  ├─ Err(error): 失败
│  │
│  ├─ 方法
│  │  ├─ unwrap(): 取值或panic
│  │  ├─ expect(msg): 带消息的unwrap
│  │  ├─ unwrap_or(default): 提供默认值
│  │  ├─ unwrap_or_else(f): 惰性默认值
│  │  ├─ map(f): 转换Ok值
│  │  ├─ map_err(f): 转换Err值
│  │  ├─ and_then(f): 链式Result
│  │  └─ or_else(f): 错误恢复
│  │
│  └─ ? 操作符
│     └─ let x = may_fail()?;
│        • 错误传播
│        • From trait 自动转换
│        • 提前返回
│
├─ 🎁 Option<T>
│  ├─ Some(value): 有值
│  ├─ None: 无值
│  │
│  └─ 方法
│     ├─ unwrap(): 取值或panic
│     ├─ expect(msg): 带消息
│     ├─ unwrap_or(default): 默认值
│     ├─ unwrap_or_else(f): 惰性默认
│     ├─ map(f): 转换值
│     ├─ and_then(f): 链式Option
│     ├─ or(other): 提供备选
│     ├─ or_else(f): 惰性备选
│     └─ filter(predicate): 过滤
│
├─ ⚡ ? 操作符
│  ├─ Result<T, E> → Result<U, E>
│  ├─ Option<T> → Option<U>
│  └─ 自动类型转换 (From trait)
│     • 简化错误传播
│     • 提前返回
│     • Rust 1.90: 更好的错误提示
│
├─ 💥 panic!
│  ├─ panic!(msg): 不可恢复错误
│  ├─ unwrap(): Result/Option panic
│  └─ expect(msg): 带消息的panic
│     • 用于不可恢复的错误
│     • 会展开栈
│
└─ 🔄 错误转换
   ├─ From trait
   │  └─ impl From<ErrorA> for ErrorB
   │
   ├─ thiserror crate
   │  └─ #[derive(Error)]
   │
   └─ anyhow crate
      └─ anyhow::Result<T>
         • 简化错误处理
         • 通用错误类型
```

---

## 📚 学习路径

### 🌱 初学者路径 (1-2周)

```text
Week 1: 基础控制流
│
├─ Day 1-2: 条件语句
│  ├─ if/else 基础
│  ├─ if 表达式
│  └─ 实践: 简单计算器
│
├─ Day 3-4: 循环
│  ├─ loop/while/for
│  ├─ break/continue
│  └─ 实践: 数字游戏
│
└─ Day 5-7: 模式匹配入门
   ├─ match 基础
   ├─ if let
   └─ 实践: 枚举处理

Week 2: 函数与错误处理
│
├─ Day 1-3: 函数基础
│  ├─ 函数定义
│  ├─ 参数和返回值
│  └─ 实践: 工具函数库
│
└─ Day 4-7: 错误处理
   ├─ Option/Result
   ├─ ? 操作符
   └─ 实践: 文件处理
```

### ⚡ 进阶路径 (1-2周)

```text
Week 1: 高级控制流
│
├─ 模式匹配高级
│  ├─ 守卫
│  ├─ @ 绑定
│  └─ 解构
│
├─ 闭包基础
│  ├─ Fn/FnMut/FnOnce
│  ├─ move 语义
│  └─ 实践: 迭代器方法
│
└─ 泛型函数
   ├─ 类型参数
   ├─ trait约束
   └─ 实践: 通用算法

Week 2: 高级特性
│
├─ 高阶函数
│  ├─ 函数作为参数
│  ├─ 返回闭包
│  └─ 实践: 函数组合
│
└─ 错误处理高级
   ├─ 自定义错误类型
   ├─ 错误转换
   └─ 实践: 错误传播链
```

### 🎓 专家路径 (2-3周)

```text
Week 1-2: 深度理论
│
├─ 控制流形式化
│  ├─ 控制流图
│  ├─ 数据流分析
│  └─ 死代码消除
│
├─ 闭包实现原理
│  ├─ 捕获列表
│  ├─ 内存布局
│  └─ 性能分析
│
└─ 模式匹配编译
   ├─ 决策树生成
   ├─ 穷尽性检查
   └─ 优化策略

Week 3: 实践项目
│
├─ DSL设计
├─ 控制流抽象
└─ 错误处理框架
```

---

## 🔍 问题诊断树

```text
遇到问题？
│
├─ 控制流错误
│  ├─ match不完整
│  │  ├─ 检查: 是否覆盖所有情况
│  │  └─ 解决: 添加通配符 _ 或具体模式
│  │
│  ├─ 类型不匹配
│  │  ├─ 检查: if/match所有分支类型
│  │  └─ 解决: 统一返回类型
│  │
│  └─ 循环标签
│     ├─ 检查: break/continue的目标
│     └─ 解决: 使用循环标签 'label
│
├─ 函数错误
│  ├─ 借用检查失败
│  │  ├─ 检查: 参数传递方式
│  │  └─ 解决: 选择&/&mut/所有权转移
│  │
│  ├─ 生命周期错误
│  │  ├─ 检查: 返回引用的生命周期
│  │  └─ 解决: 添加生命周期标注
│  │
│  └─ trait约束不满足
│     ├─ 检查: 类型是否实现了required trait
│     └─ 解决: 添加约束或实现trait
│
├─ 闭包错误
│  ├─ 捕获冲突
│  │  ├─ 检查: 可变/不可变借用冲突
│  │  └─ 解决: 调整闭包作用域或使用move
│  │
│  ├─ 生命周期过短
│  │  ├─ 检查: 捕获的引用是否有效
│  │  └─ 解决: 使用move获取所有权
│  │
│  └─ trait不匹配
│     ├─ 检查: 期望Fn但提供FnOnce
│     └─ 解决: 调整闭包实现
│
└─ 错误处理
   ├─ panic! vs Result
   │  ├─ 检查: 错误是否可恢复
   │  └─ 解决: 可恢复用Result，不可恢复用panic
   │
   ├─ ? 操作符类型不匹配
   │  ├─ 检查: 错误类型是否兼容
   │  └─ 解决: 实现From trait
   │
   └─ 错误丢失信息
      ├─ 检查: expect/unwrap是否合适
      └─ 解决: 使用? 或者自定义错误类型
```

---

## ⚖️ 技术选型决策树

```text
如何选择控制流？
│
├─ 条件判断
│  ├─ 简单二选一 → if/else
│  ├─ 多个分支 → match
│  ├─ 枚举匹配 → match
│  └─ 单一模式匹配 → if let
│
├─ 循环选择
│  ├─ 明确次数 → for (0..n)
│  ├─ 遍历集合 → for item in collection
│  ├─ 条件循环 → while
│  ├─ 模式匹配循环 → while let
│  └─ 无限循环 → loop
│
└─ 提前退出
   ├─ 循环中 → break
   ├─ 函数中 → return
   ├─ 错误传播 → ?
   └─ 模式不匹配 → let else

函数参数如何传递？
│
├─ 小类型(Copy) → 值传递 (i32, bool)
├─ 只读访问 → 不可变引用 (&T)
├─ 需要修改 → 可变引用 (&mut T)
├─ 转移所有权 → 值传递 (String, Vec)
└─ 性能关键 → 考虑零拷贝

闭包还是函数？
│
├─ 需要捕获环境 → 闭包
├─ 不需要捕获 → fn 函数指针
├─ 类型参数化 → impl Fn(...)
└─ 性能关键 → 考虑内联

错误处理策略？
│
├─ 可恢复错误 → Result<T, E>
├─ 无值情况 → Option<T>
├─ 不可恢复 → panic!
├─ 简化传播 → ? 操作符
└─ 通用错误 → Box<dyn Error>
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

---

🗺️ **掌握控制流与函数，编写清晰的 Rust 代码！** 🚀✨
