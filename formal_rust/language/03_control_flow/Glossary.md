# C03: 术语表 (Glossary)

- **控制流 (Control Flow)**
  - 定义：程序指令执行的顺序和规则。在 Rust 中，它与类型和所有权系统深度集成，以保证安全。

- **表达式 (Expression)**
  - 定义：能计算并返回一个值的代码片段。Rust 的大部分控制结构（如 `if`, `match`）都是表达式。

- **语句 (Statement)**
  - 定义：执行一个动作但不返回值的指令。在 Rust 中，以分号结尾的表达式会变成语句。

- **穷尽性 (Exhaustiveness)**
  - 定义：`match` 表达式的模式必须覆盖所有可能输入的值。这是由编译器静态强制执行的规则，用于防止未处理的逻辑路径。

- **`?` 运算符 (Question Mark Operator)**
  - 定义：用于错误传播的语法糖。当应用于 `Result` 或 `Option` 时，如果值为 `Err` 或 `None`，它会立即从当前函数返回；否则，它会解包出 `Ok` 或 `Some` 中的值。

- **发散函数 (Diverging Function)**
  - 定义：一个永不返回到其调用点的函数。其返回类型是 `!` (never type)。例如 `panic!` 或无限循环。

- **闭包 (Closure)**
  - 定义：可以捕获其周围环境（变量）的匿名函数。

- **`Fn` Traits (`Fn`/`FnMut`/`FnOnce`)**
  - 定义：由编译器自动为闭包实现的 trait，用于表示闭包如何捕获其环境。
    - `Fn`: 不可变借用。
    - `FnMut`: 可变借用。
    - `FnOnce`: 获取所有权。

- **高阶函数 (Higher-Order Function)**
  - 定义：接受一个或多个函数（如闭包）作为参数，或返回一个函数的函数。

- **`Future` Trait**
  - 定义：代表一个异步计算的 trait，其结果可能在未来某个时间点才可用。`async fn` 返回一个实现了 `Future` 的类型。

- **状态机 (State Machine)**
  - 定义：一种计算模型，可以处于有限个状态中的一个。在 Rust 异步编程中，编译器将 `async fn` 转换为一个状态机。

- **类型状态模式 (Type State Pattern)**
  - 定义：一种利用类型系统在编译时强制执行状态转换逻辑的设计模式。对象的状态被编码为类型参数，使得非法状态转换成为编译时错误。

---

## 批判性分析

- 术语表有助于统一控制流相关概念，提升文档一致性和可读性，但部分术语解释需结合实际案例和工程语境。
- 与主流技术文档相比，Rust 控制流术语表的系统性和权威性较强，但多语言对照和跨领域术语补充仍有提升空间。
- 在知识传播和工程协作中，术语表的持续更新和标准化管理仍需加强。

## 典型案例

- 收录控制流核心术语及标准定义，提升文档一致性。
- 针对易混淆术语，结合实际案例进行对比说明。
- 结合社区和行业标准，持续完善术语表内容。

## 批判性分析（未来展望）

- Rust 控制流术语表未来可在自动化生成、标准化和智能检索等方面持续优化。
- 随着术语体系扩展，术语表应更关注跨平台、异步和分布式场景下的术语演化与管理。
- 社区和生态对术语表标准化、自动化工具和智能检索系统的支持仍有较大提升空间。

## 典型案例（未来展望）

- 开发自动化术语表生成与智能检索平台，提升开发者学习与协作效率。
- 在分布式系统中，结合术语表与任务调度、容错机制实现高可用知识支持。
- 推动术语表相关的跨平台标准和社区协作，促进 Rust 控制流术语体系的持续完善。
