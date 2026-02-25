# 泛型与Trait概念思维导图

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 思维导图

---

## 概念层次结构

```text
                            泛型与Trait系统
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
         【泛型】            【Trait】           【关联类型】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
  结构体泛型     函数泛型  接口定义       实现    Item          Output
    │               │      │               │      │               │
 <T>             <T, U>   trait          impl    类型别名       返回值类型
```

---

## Trait类型详解

```text
Trait分类
│
├── 标记Trait (Marker Traits)
│   ├── Sized
│   ├── Copy
│   ├── Send
│   └── Sync
│
├── 操作Trait
│   ├── Drop
│   ├── Deref/DerefMut
│   └── AsRef/AsMut
│
├── 比较Trait
│   ├── PartialEq/Eq
│   ├── PartialOrd/Ord
│   └── Hash
│
└── 转换Trait
    ├── From/Into
    ├── TryFrom/TryInto
    └── Borrow/BorrowMut
```

---

## 泛型约束

```text
约束形式
│
├── 简单约束
│   └── T: Trait
│
├── 多重约束
│   └── T: TraitA + TraitB
│
├── 关联类型约束
│   └── T: Iterator<Item = u32>
│
└── 生命周期约束
    └── T: 'static
```

| 约束 | 含义 | 示例 |
| :--- | :--- | :--- |
| `T: Clone` | 可克隆 | `vec.clone()` |
| `T: Default` | 有默认值 | `T::default()` |
| `T: Debug` | 可打印调试 | `println!("{:?}", t)` |

---

## Trait对象

```text
Trait对象
├── 动态分发
│   └── dyn Trait
├── 胖指针
│   ├── 数据指针
│   └── vtable指针
└── 对象安全
    ├── 方法返回Self
    └── 泛型方法
```

---

## 高级特性

```text
高级泛型特性
│
├── 默认泛型参数
│   └── <T = String>
│
├── const泛型
│   └── [T; N]
│
├── HRTB
│   └── for<'a> Trait<'a>
│
└── 关联常量
    └── trait { const N: usize; }
```

---

## 与其他概念的关系

```text
泛型系统
├── 所有权 → T的lifetime约束
├── 类型系统 → 参数多态
├── 生命周期 → 'a泛型参数
└── 编译器 → 单态化
```

---

## 学习路径

1. **L1**: 基础泛型与trait
2. **L2**: 关联类型与约束
3. **L3**: HRTB与高级模式

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 思维导图 11/15
