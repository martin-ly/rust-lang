pub mod items;
pub mod expressions;
pub mod statements;
pub mod control_struct;
pub mod pattern_matching;
pub mod closure;
pub mod error_handling;

/*
在 Rust 中，控制流的核心概念之间的组合关系和形式可以通过范畴论的视角来理解。
以下是对这些概念之间关系的具体解释：
1. **项（Item）与表达式（Expression）**：
   - **组合关系**：
     - 项是程序的基本构建块，而表达式是这些项的具体实现。
     - 每个项可以包含多个表达式，表达式在项的上下文中执行。
2. **表达式（Expression）与语句（Statement）**：
   - **组合关系**：
     - 表达式可以作为语句的一部分，语句通常由一个或多个表达式组成。
     - 语句执行操作但不返回值，而表达式则计算并返回值。
3. **控制结构（Control Structure）与表达式（Expression）**：
   - **组合关系**：
     - 控制结构通过条件和循环来控制表达式的执行流。
     - 控制结构本身可以是表达式（如 `if` 表达式），并根据条件返回不同的值。
4. **模式匹配（Pattern Matching）与控制结构（Control Structure）**：
   - **组合关系**：
     - 模式匹配是一种特殊的控制结构，它允许根据数据的形状和内容进行分支。
     - 它可以看作是对控制流的扩展，提供更强大的条件判断能力。
5. **闭包（Closure）与表达式（Expression）**：
   - **组合关系**：
     - 闭包可以作为表达式使用，并且可以在控制结构中传递和执行。
     - 闭包允许将逻辑封装在一个可重用的单元中。
6. **错误处理（Error Handling）与控制结构（Control Structure）**：
   - **组合关系**：
     - Rust 的错误处理机制（如 `Result` 和 `Option`）与控制结构结合使用，
     以便在出现错误时控制程序的执行流。
通过这些组合关系和形式，我们可以看到 Rust 中的控制流是如何通过不同的核心概念
相互作用和协作的。
这种结构化的方式使得 Rust 的控制流既灵活又强大，能够有效地处理各种编程场景。
*/