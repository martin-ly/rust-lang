# Rust 所有权系统 - 快速参考卡片

> 一页纸速查，核心概念快速回顾

---

## 🎯 所有权三原则

```rust
1. 唯一性     // 每个值有且仅有一个所有者
2. 作用域绑定 // 所有者离开作用域时释放值
3. 可转移性   // 所有权可以转移 (Move)
```

---

## 🔄 借用规则

```rust
// 不可变借用: 多个 &T 同时存在
let r1 = &data;
let r2 = &data;  // OK

// 可变借用: 仅一个 &mut T
let r = &mut data;  // OK
// let r2 = &mut data;  // 错误!
// let r3 = &data;      // 错误!

// XOR 规则: 不能同时存在可变和不可变借用
```

---

## ⏱️ 生命周期规则

```rust
// 编译器自动推断 (省略规则)
fn first(x: &str) -> &str { &x[0..1] }

// 显式注解 (多输入)
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 'static: 整个程序生命周期
let s: &'static str = "编译期字符串";
```

---

## 🧠 智能指针速查

| 指针 | 用途 | Send | Sync |
|:-----|:-----|:----:|:----:|
| `Box<T>` | 堆分配 | T: Send | T: Sync |
| `Rc<T>` | 共享所有权(单线程) | ❌ | ❌ |
| `Arc<T>` | 共享所有权(多线程) | ✅ | ✅ |
| `RefCell<T>` | 内部可变性(单线程) | ❌ | ❌ |
| `Mutex<T>` | 内部可变性(多线程) | ✅ | ✅ |

---

## 🎨 常见模式

### RAII 模式

```rust
pub struct LockGuard<'a> {
    lock: &'a Lock,
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        self.lock.release();
    }
}
```

### 类型状态模式

```rust
pub struct Ready;
pub struct Running;

impl Connection<Ready> {
    pub fn start(self) -> Connection<Running>;
}
```

### 内部可变性

```rust
use std::cell::RefCell;
let data = RefCell::new(5);
*data.borrow_mut() += 1;
```

---

## ⚡ 并发 Send/Sync

```rust
// Send: 可跨线程转移所有权
// Sync: 可跨线程共享引用 (&T: Send)

// 自动实现规则:
impl Send for T where T: Send { }
impl Sync for T where &T: Send { }

// 常见类型:
// i32: Send + Sync
// Rc<T>: !Send, !Sync
// Arc<T>: Send + Sync (if T: Send + Sync)
// RefCell<T>: Send (if T: Send), !Sync
// Mutex<T>: Send + Sync (if T: Send)
```

---

## 🔧 错误快速修复

| 错误 | 修复方法 |
|:-----|:---------|
| E0382 (use of moved) | `.clone()` 或改用 `&T` |
| E0499 (multi mut) | 使用作用域或 `RefCell` |
| E0502 (mut + immut) | 顺序化借用 |
| E0597 (lifetime) | 延长作用域或 `Rc/Arc` |

---

## 📊 验证工具

| 工具 | 用途 | 命令 |
|:-----|:-----|:-----|
| Miri | UB 检测 | `cargo miri run` |
| Kani | 模型检测 | `cargo kani` |
| Clippy | Lint | `cargo clippy` |

---

## 📚 快速导航

```text
📖 理论
├── UNIFIED_THEORETICAL_FRAMEWORK.md  // 统一框架
├── THEOREM_DEPENDENCY_GRAPH.md       // 定理依赖
└── coq-formalization/                // Coq证明

💻 实践
├── INTERACTIVE_LEARNING_GUIDE.md     // 交互学习
├── exercises/                        // 练习题
└── case-studies/                     // 案例分析

❓ 参考
├── COMPREHENSIVE_FAQ.md              // FAQ
├── ERROR_DIAGNOSTICS_GUIDE.md        // 错误诊断
└── QUICK_REFERENCE_CARD.md           // 本卡片
```

---

## 🎓 学习路径

```text
初学者: 概念卡片 → 交互指南 → 基础练习
进阶:   详细概念 → 设计模式 → 案例研究
专家:   理论框架 → Coq证明 → 研究前沿
```

---

## 🔗 关键链接

- [完整认证](FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md)
- [知识梳理](COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md)
- [案例索引](case-studies/COMPLETE_DOMAIN_COVERAGE_INDEX.md)

---

*打印此页，随时查阅* 🖨️

---

## 🆕 Rust 1.94 所有权系统更新

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| rray_windows | 安全的切片访问 | ✅ 编译期检查 |
| ControlFlow | 控制流语义 | ✅ 类型安全 |
| LazyCell/LazyLock | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- rray_windows 的边界安全证明
- ControlFlow 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
