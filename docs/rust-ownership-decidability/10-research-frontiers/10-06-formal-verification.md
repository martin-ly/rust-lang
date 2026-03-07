# 形式化验证前沿

> **难度**: 🔴 高级
> **主题**: 定理证明、模型检测、Rust 验证工具链

---

## 当前研究热点

### 1. RustBelt 项目

RustBelt 是首个完整的 Rust 形式化安全证明。

```
核心成果:
- 在 Iris (分离逻辑框架) 中形式化 Rust 核心
- 证明标准库原语的安全性
- 处理 unsafe 代码的模块化验证
```

### 2. Aeneas 项目

将 Rust 翻译到纯函数式语言进行验证。

```rust
// Rust 代码
type List = Option<Box<Node>>;

// 翻译为 (类似):
// type List = ListCons u32 List | ListNil
// 然后使用 Lean/Coq 证明
```

### 3. Kani / CBMC

模型检测 Rust 代码的状态空间。

```bash
# 验证所有可能输入
cargo kani --function my_function
```

---

## 开放问题

1. **Unsafe 代码验证**: 如何模块化验证 unsafe 块?
2. **异步/并发**: 形式化验证 async/await 的正确性
3. **性能模型**: 形式化推理与运行时性能的关系
4. **类型系统扩展**: GAT、泛型关联类型的元理论

---

## 相关工具

| 工具 | 方法 | 状态 |
|-----|------|------|
| Creusot | 前置/后置条件 | 活跃开发 |
| Kani | 模型检测 | 生产可用 |
| Aeneas | 程序翻译 | 研究阶段 |
| RustBelt | 分离逻辑 | 研究完成 |

---

*文档版本: 1.0.0*
