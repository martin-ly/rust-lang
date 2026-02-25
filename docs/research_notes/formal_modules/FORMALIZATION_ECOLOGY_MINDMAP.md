# Rust形式化生态思维导图

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 思维导图

---

## 生态系统层次

```text
                        Rust形式化验证生态
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
       【验证工具】          【证明助手】          【形式化语义】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
  Miri          Kani    Coq          Isabelle  RustBelt    RustBelt
    │               │    │               │    │               │
 未定义行为检测   模型检查  交互式证明     自动证明  Stacked Borrows
```

---

## 验证工具详解

```
工具分类
│
├── 动态分析
│   ├── Miri (解释器)
│   ├── AddressSanitizer
│   └── ThreadSanitizer
│
├── 静态分析
│   ├── Clippy (lints)
│   ├── Prusti (规范验证)
│   └── Creusot (Why3集成)
│
└── 模型检查
    ├── Kani (CBMC)
    └── Shuttle (并发测试)
```

| 工具 | 方法 | 用途 |
| :--- | :--- | :--- |
| Miri | 解释执行 | 检测UB |
| Kani | 模型检查 | 验证属性 |
| Prusti | 契约验证 | 规范检查 |

---

## 证明助手集成

```
证明助手
│
├── Coq
│   ├── Coq-of-Rust (翻译)
│   ├── RustBelt (所有权)
│   └── 人工证明
│
├── Isabelle/HOL
│   ├── Rust verification
│   └── 自动推理
│
└── F*
    └── hacspec (规范)
```

---

## 形式化语义

```
语义模型
│
├── 操作语义
│   ├── 小步语义
│   └── 大步语义
│
├── 逻辑关系
│   ├── Iris (高阶分离逻辑)
│   └── Lifetime逻辑
│
└── 类型系统
    ├── 子类型关系
    └── 变型规则
```

---

## 研究项目

```
活跃研究
│
├── RustBelt (MPI-SWS)
│   └── 所有权形式化
│
├── Rust Verification Tools
│   └── Prusti + Aeneas
│
├── Ferrocene
│   └── 工业级验证
│
└── Rust Formal Methods WG
    └── 官方工作组
```

---

## 应用路径

```
使用场景选择
│
├── 学习研究
│   └── Miri + Coq骨架
│
├── 生产验证
│   └── Kani + Prusti
│
└── 高可信系统
    └── 完整形式化证明
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 思维导图 12/15
