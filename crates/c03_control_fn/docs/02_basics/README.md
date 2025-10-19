# 02. 基础知识 (Basics)

本部分涵盖 Rust 控制流与函数的基础知识，适合初学者和需要巩固基础的开发者。通过丰富的代码示例和清晰的讲解，帮助你快速掌握 Rust 控制流的核心用法。

## 📚 文档列表

### 核心文档 (6份)

| 编号 | 文档 | 难度 | 时间 | 核心主题 |
|------|------|------|------|---------|
| 01 | [控制流基础概念](./01_control_flow_fundamentals.md) | ⭐⭐ | 1-2h | 全面入门，涵盖所有基本概念 |
| 02 | [条件表达式](./02_conditional_expressions.md) | ⭐⭐ | 1.5h | if、if let、match 详解 |
| 03 | [循环结构](./03_iterative_constructs.md) | ⭐⭐ | 1.5h | loop、while、for 详解 |
| 04 | [函数与闭包](./04_functions_and_closures.md) | ⭐⭐⭐ | 2h | 函数、闭包、Fn trait |
| 05 | [错误处理控制流](./05_error_handling_as_control_flow.md) | ⭐⭐⭐ | 1.5h | Option、Result、? 运算符 |
| 06 | [Rust 1.90 特性总览](./06_control_flow_overview_1_90.md) | ⭐⭐ | 1h | 最新语法快速参考 |

---

## 📖 文档详情

### 1. [控制流基础概念](./01_control_flow_fundamentals.md)

**推荐作为第一份文档阅读**:

**核心内容**：

- 条件控制流：if 和 match 表达式
- 循环控制流：loop、while、for
- 模式匹配基础
- 函数与闭包入门
- 错误处理入门
- 异步控制流概览

**适合读者**：

- Rust 初学者
- 需要全面了解控制流的开发者
- 从其他语言转到 Rust 的开发者

**学习收获**：

- 建立 Rust 控制流的整体框架
- 理解表达式优先的设计理念
- 掌握基本的模式匹配语法
- 了解 Rust 独特的错误处理方式

**建议**：

- 第一次阅读可以快速浏览
- 结合后续专题文档深入学习
- 编写代码验证每个概念

---

### 2. [条件表达式](./02_conditional_expressions.md)

**if、if let、match 专题**:

**核心内容**：

- if 表达式的形式化定义
- if let 的语法糖本质
- match 表达式的穷尽性检查
- 守卫条件的使用
- 条件表达式中的所有权规则

**适合读者**：

- 掌握基本语法的初学者
- 需要理解模式匹配的开发者
- 想优化条件分支代码的开发者

**学习收获**：

- 理解表达式返回值的类型约束
- 掌握 match 的强大模式匹配能力
- 避免穷尽性检查错误
- 理解分支中的借用冲突

**实践技能**：

```rust
// 使用 match 而非多重 if
match value {
    0 => "zero",
    1..=9 => "small",
    10..=99 => "medium",
    _ => "large",
}

// if let 简化简单匹配
if let Some(value) = optional {
    println!("Got: {}", value);
}
```

---

### 3. [循环结构](./03_iterative_constructs.md)

**loop、while、for 专题**:

**核心内容**：

- loop 的无限循环和 break 返回值
- while 和 while let 的条件循环
- for 循环和迭代器
- 循环标签和嵌套控制
- 循环中的所有权规则

**适合读者**：

- 需要掌握循环语法的初学者
- 想高效使用迭代器的开发者
- 关注性能优化的开发者

**学习收获**：

- 理解三种循环的适用场景
- 掌握迭代器的三种所有权模式
- 使用循环标签控制嵌套循环
- 避免循环中的常见陷阱

**实践技能**：

```rust
// loop 返回值
let result = loop {
    counter += 1;
    if counter == 10 {
        break counter * 2;
    }
};

// 迭代器三种模式
for item in collection.into_iter() { } // 消耗所有权
for item in collection.iter() { }      // 不可变借用
for item in collection.iter_mut() { }  // 可变借用
```

---

### 4. [函数与闭包](./04_functions_and_closures.md)

**函数、闭包、Fn trait 专题**:

**核心内容**：

- 函数的控制流转移
- 函数参数的所有权传递
- 发散函数和 never 类型
- 闭包的环境捕获机制
- Fn、FnMut、FnOnce trait
- 高阶函数和闭包组合

**适合读者**：

- 掌握基本语法的开发者
- 需要深入理解闭包的学习者
- 想编写函数式代码的开发者

**学习收获**：

- 理解函数调用的控制权转移
- 掌握闭包的三种捕获模式
- 理解 Fn trait 的类型层级
- 能够编写和使用高阶函数

**实践技能**：

```rust
// 闭包三种捕获
let by_ref = |x| println!("{}", x);      // Fn
let mut by_mut_ref = |x| { data += x; }; // FnMut  
let by_move = move |x| drop(data);       // FnOnce

// 高阶函数
fn apply<F>(f: F, x: i32) -> i32 
where F: Fn(i32) -> i32 
{
    f(x)
}
```

---

### 5. [错误处理控制流](./05_error_handling_as_control_flow.md)

**Option、Result、? 运算符专题**:

**核心内容**：

- Option 和 Result 的控制流分裂
- ? 运算符的提前返回机制
- 错误传播的控制流
- 组合子方法链式处理
- panic 的控制流影响
- let-else 模式

**适合读者**：

- 需要掌握错误处理的初学者
- 想优化错误处理代码的开发者
- 关注代码健壮性的开发者

**学习收获**：

- 理解 Rust 的显式错误处理哲学
- 掌握 ? 运算符的使用场景
- 使用组合子优雅处理错误
- 理解 panic 的适用场景

**实践技能**：

```rust
// ? 运算符链式调用
fn process() -> Result<i32, Error> {
    let data = read_file()?;
    let parsed = parse_data(data)?;
    Ok(transform(parsed)?)
}

// 组合子链式处理
value
    .ok_or("missing value")?
    .parse::<i32>()
    .map_err(|_| "parse error")?
```

---

### 6. [Rust 1.90 特性总览](./06_control_flow_overview_1_90.md)

**快速参考文档**:

**核心内容**：

- if / if let / if let 链
- let-else 提前返回
- 循环标签和跳转
- break 返回值
- 发散类型 !
- 最新稳定特性

**适合读者**：

- 想快速查阅语法的开发者
- 关注新特性的学习者
- 需要参考文档的所有人

**使用方式**：

- 作为快速参考手册
- 了解版本新增特性
- 对照实际代码使用

---

## 🎯 学习路径

### 推荐学习顺序

#### 完全初学者

```text
第1步: 控制流基础概念 (01) - 建立整体框架
  ↓
第2步: 条件表达式 (02) - 掌握 if 和 match
  ↓
第3步: 循环结构 (03) - 掌握循环语法
  ↓
第4步: 错误处理控制流 (05) - 掌握错误处理
  ↓
第5步: 函数与闭包 (04) - 深入函数和闭包
```

#### 有其他语言经验

```text
第1步: 快速浏览 控制流基础概念 (01)
  ↓
第2步: 重点学习 条件表达式 (02) - Rust 特色
  ↓
第3步: 重点学习 错误处理控制流 (05) - 与异常不同
  ↓
第4步: 深入学习 函数与闭包 (04) - 闭包捕获
  ↓
第5步: 参考 Rust 1.90 特性总览 (06)
```

#### 复习巩固

```text
使用 Rust 1.90 特性总览 (06) 作为索引
  ↓
根据需要查阅对应的专题文档
  ↓
完成文档中的练习题
```

### 按主题学习

**关注模式匹配**：

- [控制流基础概念 § 模式匹配](./01_control_flow_fundamentals.md#模式匹配)
- [条件表达式 (完整)](./02_conditional_expressions.md)
- [循环结构 § while let](./03_iterative_constructs.md#322-while-let-循环)

**关注错误处理**：

- [控制流基础概念 § 错误处理](./01_control_flow_fundamentals.md#错误处理控制流)
- [错误处理控制流 (完整)](./05_error_handling_as_control_flow.md)

**关注函数式编程**：

- [函数与闭包 § 闭包](./04_functions_and_closures.md#42-闭包-closures)
- [循环结构 § for 与迭代器](./03_iterative_constructs.md#33-迭代循环-for)

**关注性能**：

- [循环结构 § 迭代器性能](./03_iterative_constructs.md#性能考量)
- [函数与闭包 § 内联优化](./04_functions_and_closures.md)

---

## 💡 学习建议

### 1. 动手实践为主

**理论学习比例**：30%  
**代码实践比例**：70%

```bash
# 创建练习项目
cargo new control_flow_practice
cd control_flow_practice

# 每学习一个概念，立即编写代码验证
# 观察编译器错误，理解背后的原理
```

### 2. 利用编译器学习

Rust 编译器是最好的老师：

```rust
// 故意写错，看编译器如何提示
let x = if true { 1 } else { "two" };
// error: `if` and `else` have incompatible types
```

**学习策略**：

- 尝试编写"边界情况"的代码
- 仔细阅读编译器错误信息
- 理解错误背后的类型规则

### 3. 循序渐进

**第一遍学习**：

- 快速浏览，建立整体认知
- 运行所有代码示例
- 不纠结于细节

**第二遍学习**：

- 深入理解每个概念
- 完成练习题
- 总结知识点

**第三遍学习**：

- 在实际项目中应用
- 总结最佳实践
- 教授他人

### 4. 对比其他语言

如果你熟悉其他语言：

| 其他语言 | Rust 对应 | 主要区别 |
|---------|----------|---------|
| C/C++ switch | match | 必须穷尽，可解构 |
| Python for | for | 基于迭代器，明确所有权 |
| JavaScript try-catch | Result + ? | 显式，编译时检查 |
| Java lambda | 闭包 | 显式捕获模式 |

### 5. 结合官方资源

**推荐阅读顺序**：

1. 本模块基础文档（先学习）
2. The Rust Book 对应章节（巩固）
3. Rust by Example（更多示例）
4. 本模块高级文档（深入）

---

## 🎓 检查点

完成基础部分学习后，你应该能够：

### 基础能力

- [ ] 编写包含 if、match、loop 的代码
- [ ] 使用 for 循环遍历集合
- [ ] 编写简单的闭包
- [ ] 使用 ? 运算符处理错误
- [ ] 理解编译器的类型错误信息

### 中级能力

- [ ] 选择合适的循环结构
- [ ] 使用 match 进行复杂模式匹配
- [ ] 理解闭包的捕获模式
- [ ] 链式组合错误处理
- [ ] 使用迭代器方法

### 进阶能力

- [ ] 编写高阶函数
- [ ] 理解控制流中的所有权转移
- [ ] 使用类型系统保证安全性
- [ ] 优化循环性能
- [ ] 设计优雅的错误处理

---

## 📝 练习建议

### 基础练习

1. **FizzBuzz**

   ```rust
   // 使用 match 实现 FizzBuzz
   fn fizzbuzz(n: i32) -> String {
       match (n % 3, n % 5) {
           (0, 0) => "FizzBuzz".to_string(),
           (0, _) => "Fizz".to_string(),
           (_, 0) => "Buzz".to_string(),
           _ => n.to_string(),
       }
   }
   ```

2. **计算器**
   - 使用 match 实现简单计算器
   - 使用 Result 处理除零错误

3. **查找最大值**
   - 使用 for 循环
   - 使用迭代器方法
   - 对比两种方式

### 进阶练习

1. **自定义迭代器**
   - 实现 Iterator trait
   - 使用闭包作为过滤器

2. **错误处理链**
   - 实现多步骤处理函数
   - 使用 ? 运算符传播错误
   - 使用 map_err 转换错误类型

3. **闭包组合器**
   - 实现 and_then、or_else
   - 组合多个闭包

---

## 🔗 相关章节

### 向前关联

- **前置学习**：[理论基础](../01_theory/README.md)
- **相关模块**：Rust Book Chapter 3-6

### 向后关联

- **深入学习**：[高级主题](../03_advanced/README.md)
- **实践应用**：[工程实践](../04_practice/README.md)
- **新特性**：[Rust 1.89/1.90](../05_rust_features/README.md)

### 横向关联

- **所有权系统**：c01_ownership_borrow_scope
- **类型系统**：c02_type_system
- **异步编程**：c06_async

---

## 💬 常见问题

Q1：是否需要按顺序阅读所有文档？

A：**建议但不强制**：

**推荐顺序**：

- 初学者：按 01 → 02 → 03 → 05 → 04 顺序
- 有经验者：可以根据需要选读

**灵活调整**：

- 遇到困难可以跳过，之后回来
- 可以根据实际项目需要优先学习某些主题

</details>

Q2：基础部分学习需要多长时间？

A：**因人而异**：

**完全初学者**：1-2周

- 每天学习 1-2 小时
- 包括阅读和实践

**有编程经验**：3-5天

- 重点理解 Rust 特色
- 快速上手基本语法

**经验丰富者**：1-2天

- 快速浏览文档
- 对照实际代码理解

</details>

Q3：练习题在哪里？

A：**多种来源**：

1. **文档内练习**：每份文档末尾都有
2. **Rust by Example**：<https://doc.rust-lang.org/rust-by-example/>
3. **Exercism**：<https://exercism.org/tracks/rust>
4. **Rustlings**：<https://github.com/rust-lang/rustlings>

**建议**：

- 先完成文档内练习
- 再做 Rustlings 强化训练

</details>

Q4：如何判断已经掌握基础知识？

A：**自我评估标准**：

**能够独立完成**：

- [ ] 实现一个命令行程序（带错误处理）
- [ ] 使用迭代器处理集合
- [ ] 编写使用闭包的函数
- [ ] 理解编译器错误并修复

**理解核心概念**：

- [ ] 表达式 vs 语句
- [ ] 穷尽性检查
- [ ] 所有权在控制流中的转移
- [ ] 错误传播机制

</details>

---

**导航**：

- [返回主文档](../README.md)
- [查看完整索引](../DOCUMENTATION_INDEX.md)
- 上一部分：[理论基础](../01_theory/README.md)
- 下一部分：[高级主题](../03_advanced/README.md)

---

*最后更新：2025年1月*  
*文档版本：v1.0*  
*Rust 版本：1.90+*
