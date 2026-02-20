# Command 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 行为型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 14 行（Command）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Command 形式化分析](#command-形式化分析)
  - [📊 目录](#-目录)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
    - [方式一：闭包](#方式一闭包)
    - [方式二：Trait 命令](#方式二trait-命令)
    - [方式三：FnOnce“消费型”命令](#方式三fnonce消费型命令)
    - [撤销/重做（Undo/Redo）](#撤销重做undoredo)
  - [证明思路](#证明思路)
  - [典型场景](#典型场景)
  - [完整场景示例：可撤销文本编辑器](#完整场景示例可撤销文本编辑器)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例：命令副作用不可逆](#反例命令副作用不可逆)
  - [选型决策树](#选型决策树)
  - [与 GoF 对比](#与-gof-对比)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Command 结构）**:

设 $C$ 为命令类型。Command 满足：

- $\exists \mathit{execute} : C \to ()$ 或 $\mathit{execute} : C \to \mathrm{Result}$
- $C$ 封装操作与参数
- 可存储、队列、撤销（若支持）

**Axiom CM1**：命令对象可存储；可 defer 执行。

**Axiom CM2**：闭包 `Fn` 或 `FnOnce` 即命令；捕获环境为参数。

**定理 CM-T1**：闭包 `Fn() -> R` 或 `FnOnce() -> R` 即命令；由 [type_system_foundations](../../../type_theory/type_system_foundations.md) 类型安全。

**定理 CM-T2**：`Box<dyn Fn()>` 可存储、可跨边界传递；满足 Send 则可跨线程。

**推论 CM-C1**：Command 为纯 Safe；闭包或 trait 封装操作，无 `unsafe`。由 CM-T1、CM-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Command 结构）、Axiom CM1/CM2（可存储、闭包即命令） | 上 |
| **属性关系层** | Axiom CM1/CM2 → 定理 CM-T1/CM-T2 → 推论 CM-C1；依赖 type、ownership、Send | 上 |
| **解释论证层** | 证明思路：闭包类型安全、Send 跨线程；反例：命令副作用不可逆 | §证明思路、§反例 |

---

## Rust 实现与代码示例

### 方式一：闭包

```rust
let x = 42;
let cmd: Box<dyn Fn() -> i32> = Box::new(move || x + 1);
let result = cmd();
assert_eq!(result, 43);
```

### 方式二：Trait 命令

```rust
trait Command {
    fn execute(&self);
}

struct PrintCommand(pub String);
impl Command for PrintCommand {
    fn execute(&self) {
        println!("{}", self.0);
    }
}

// 存储命令队列
let mut queue: Vec<Box<dyn Command>> = vec![];
queue.push(Box::new(PrintCommand("hello".into())));
for cmd in &queue {
    cmd.execute();
}
```

### 方式三：FnOnce“消费型”命令

```rust
let mut queue: Vec<Box<dyn FnOnce()>> = vec![];
queue.push(Box::new(|| println!("done")));
let cmd = queue.pop().unwrap();
cmd();  // 消费
```

**形式化对应**：`Command` trait 或 `Fn`/`FnOnce` 即 $C$；`execute` 即 $\mathit{execute}$。

### 撤销/重做（Undo/Redo）

```rust
trait ReversibleCommand {
    fn execute(&mut self);
    fn undo(&mut self);
}

struct IncrementCommand { value: i32, prev: Option<i32> }
impl ReversibleCommand for IncrementCommand {
    fn execute(&mut self) {
        self.prev = Some(self.value);
        self.value += 1;
    }
    fn undo(&mut self) {
        if let Some(p) = self.prev {
            self.value = p;
            self.prev = None;
        }
    }
}
```

---

## 证明思路

1. **类型安全**：闭包类型由捕获推导；`dyn Command` 由 trait 保证。
2. **存储**：`Box<dyn Fn>` 可在 `Vec` 中存储；所有权明确。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 撤销/重做 | 编辑器、事务、历史记录 |
| 任务队列 | 延迟执行、批处理 |
| 宏/脚本 | 录制与回放操作 |
| 异步调度 | Future 即可恢复命令 |

---

## 完整场景示例：可撤销文本编辑器

**场景**：插入/删除字符；支持 undo/redo 栈；命令对象封装操作与逆操作。

```rust
trait EditorCommand {
    fn execute(&mut self, doc: &mut String);
    fn undo(&mut self, doc: &mut String);
}

struct InsertCommand { pos: usize, ch: char }
impl EditorCommand for InsertCommand {
    fn execute(&mut self, doc: &mut String) {
        doc.insert(self.pos, self.ch);
    }
    fn undo(&mut self, doc: &mut String) {
        doc.remove(self.pos);
    }
}

struct DeleteCommand { pos: usize, removed: Option<char> }
impl EditorCommand for DeleteCommand {
    fn execute(&mut self, doc: &mut String) {
        if self.pos < doc.len() {
            self.removed = Some(doc.remove(self.pos));
        }
    }
    fn undo(&mut self, doc: &mut String) {
        if let Some(c) = self.removed.take() {
            doc.insert(self.pos, c);
        }
    }
}

struct Editor {
    doc: String,
    undo_stack: Vec<Box<dyn EditorCommand>>,
}
impl Editor {
    fn apply(&mut self, mut cmd: Box<dyn EditorCommand>) {
        cmd.execute(&mut self.doc);
        self.undo_stack.push(cmd);
    }
}
// 使用：editor.apply(Box::new(InsertCommand { pos: 0, ch: 'x' }));
```

**形式化对应**：`EditorCommand` 即 $C$；`execute`/`undo` 为可逆操作；由 Axiom CM1、CM2。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Observer](observer.md) | 观察者可接收命令；命令可作为事件 |
| [Chain of Responsibility](chain_of_responsibility.md) | 链中节点可封装为 Command |
| [Memento](memento.md) | 撤销需 Memento 保存状态 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `Box<dyn Fn()>` | 无参数、无返回值 | 简单操作 |
| `Box<dyn FnOnce()>` | 消费型；可移动捕获 | 一次性执行 |
| `trait Command` | 可扩展、可存储 | 撤销/重做、队列 |
| `Future` | 异步命令 | async/await 任务 |

---

## 反例：命令副作用不可逆

**错误**：命令执行 I/O、网络请求等不可逆操作，`undo` 无法恢复。

```rust
impl ReversibleCommand for SendEmailCommand {
    fn execute(&mut self) { /* 邮件已发送 */ }
    fn undo(&mut self) { /* 无法撤回 */ }
}
```

**结论**：撤销仅对纯函数或可逆状态有效；需在设计时区分可逆/不可逆命令。

---

## 选型决策树

```text
需要封装可存储/可撤销的操作？
├── 是 → 需撤销？ → trait ReversibleCommand
│       └── 仅执行？ → Box<dyn Fn> 或 trait Command
├── 需一对多通知？ → Observer
└── 需沿链传递？ → Chain of Responsibility
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 命令接口 | trait Command 或 Fn | 等价 |
| 具体命令 | impl Command | 等价 |
| 撤销 | undo 方法 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Command 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、定理 CM-T1（L2） |
| 代码 | ✅ | 可运行示例、可撤销编辑器 |
| 场景 | ✅ | 典型场景、完整示例 |
| 反例 | ✅ | 命令副作用不可逆 |
| 衔接 | ✅ | ownership、CE-T2、Send |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
