# 编译器内部机制示例

> 这些示例配合 [Rust编译器内部机制完整指南](../../RUST_COMPILER_INTERNALS_GUIDE_2025.md) 使用

## 📋 示例列表

### 01. 查看MIR (`01_view_mir.rs`)

**目标**：学习如何查看和理解MIR（中级中间表示）

```bash
# 查看MIR
rustc +nightly -Z unpretty=mir examples/compiler_internals/01_view_mir.rs

# 保存到文件
rustc +nightly -Z unpretty=mir examples/compiler_internals/01_view_mir.rs > mir_output.txt

# 查看特定优化pass后的MIR
rustc +nightly -Z dump-mir=all examples/compiler_internals/01_view_mir.rs
```

**包含的场景**：

- ✅ 简单函数
- ✅ 控制流（if/else）
- ✅ 循环（while）
- ✅ 模式匹配（match）
- ✅ 所有权转移
- ✅ 借用
- ✅ 闭包
- ✅ 泛型
- ✅ Option/Result处理

### 02. 优化示例 (`02_optimization_examples.rs`)

**目标**：对比不同优化级别的效果

```bash
# 无优化（O0）
rustc --emit=llvm-ir -C opt-level=0 examples/compiler_internals/02_optimization_examples.rs -o unopt.ll

# 最大优化（O3）
rustc --emit=llvm-ir -C opt-level=3 examples/compiler_internals/02_optimization_examples.rs -o opt.ll

# 对比差异
diff -u unopt.ll opt.ll

# 查看汇编
rustc --emit=asm -C opt-level=3 examples/compiler_internals/02_optimization_examples.rs -o opt.s
```

**观察的优化**：

- ✅ 常量传播
- ✅ 死代码消除
- ✅ 函数内联
- ✅ 循环展开
- ✅ 向量化
- ✅ 分支预测
- ✅ 尾调用优化
- ✅ 零成本抽象
- ✅ 边界检查消除

### 03. 借用检查器分析 (`03_borrow_checker_analysis.rs`)

**目标**：理解借用检查器如何分析代码

```bash
# 编译（会显示借用检查）
cargo build --example 03_borrow_checker_analysis

# 查看借用检查的MIR
rustc +nightly -Z unpretty=mir examples/compiler_internals/03_borrow_checker_analysis.rs
```

**演示的概念**：

- ✅ NLL（非词法生命周期）
- ✅ 两阶段借用
- ✅ 借用分裂
- ✅ 生命周期省略
- ✅ 复杂借用场景
- ✅ Drop检查
- ✅ 结构体字段借用
- ✅ 闭包捕获分析

## 🔧 实践练习

### 练习 1：MIR分析

1. 选择`01_view_mir.rs`中的一个函数
2. 查看其MIR表示
3. 识别以下元素：
   - Basic blocks（基本块）
   - Statements（语句）
   - Terminators（终止符）
   - Local variables（局部变量）

### 练习 2：优化对比

1. 编译`02_optimization_examples.rs`为LLVM IR（O0和O3）
2. 选择一个函数，对比优化前后的IR
3. 识别应用了哪些优化

### 练习 3：借用检查理解

1. 修改`03_borrow_checker_analysis.rs`中的代码
2. 故意创建借用冲突
3. 理解编译器的错误消息

## 📊 性能分析工具

### cargo-asm

查看函数的汇编输出：

```bash
# 安装
cargo install cargo-asm

# 使用
cargo asm your_crate::function_name --rust
```

### cargo-show-mir

查看函数的MIR：

```bash
# 安装
cargo install cargo-show-mir

# 使用
cargo show-mir --fn function_name
```

### cargo-expand

查看宏展开：

```bash
# 安装
cargo install cargo-expand

# 使用
cargo expand
```

## 📚 扩展阅读

- [Rust编译器开发指南](https://rustc-dev-guide.rust-lang.org/)
- [MIR文档](https://rust-lang.github.io/rustc-guide/mir/index.html)
- [LLVM语言参考](https://llvm.org/docs/LangRef.html)
- [主指南](../../RUST_COMPILER_INTERNALS_GUIDE_2025.md)

## 💡 技巧

1. **使用nightly版本**：许多内部查看功能需要nightly

   ```bash
   rustup install nightly
   rustup default nightly
   ```

2. **保存输出**：将MIR/LLVM IR保存到文件便于分析

   ```bash
   rustc -Z unpretty=mir main.rs > output.txt
   ```

3. **使用图形化工具**：生成CFG图

   ```bash
   rustc +nightly -Z dump-mir-graphviz main.rs
   # 生成.dot文件，使用graphviz查看
   ```

4. **增量编译**：查看依赖图

   ```bash
   RUSTC_LOG=rustc_incremental cargo build
   ```

---

**创建日期**: 2025-10-20  
**维护者**: Rust Learning Community

🔬 **探索编译器的内部世界！** ✨
