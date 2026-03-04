# 形式化模型总览

> **导航中心**: Rust所有权系统的形式化理论模型

本目录包含Rust所有权和借用系统的严格形式化模型，建立在现代程序语言理论的基础之上。

---

## 目录结构

```
02-formal-models/
├── README.md                    # 本文件: 总览和导航
├── 02-01-rustbelt.md           # RustBelt: Rust的形式化基础
├── 02-02-ownership-types.md    # 所有权类型系统 (线性/仿射类型)
├── 02-03-borrow-semantics.md   # 借用语义的形式化
├── 02-04-lifetime-logic.md     # 生命周期逻辑 (区域代数)
└── 02-05-move-analysis.md      # 移动语义分析
```

---

## 理论框架概览

### 形式化层次

```text
┌─────────────────────────────────────────────────────────────────────┐
│                     形式化理论层次结构                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Level 4: 应用层                                                     │
│  ├── Rust标准库验证 (Vec, HashMap, Rc, Arc)                         │
│  └── 并发原语验证 (Mutex, RwLock, Channel)                          │
│                              │                                      │
│  Level 3: 类型系统层                                                │
│  ├── 所有权类型 (线性/仿射)                                         │
│  ├── 借用类型 (&T, &mut T)                                          │
│  └── 生命周期参数化                                                 │
│                              │                                      │
│  Level 2: 逻辑层                                                    │
│  ├── 分离逻辑 (Separation Logic)                                    │
│  ├── 生命周期逻辑 (Lifetime Logic)                                  │
│  └── Iris 高阶框架                                                  │
│                              │                                      │
│  Level 1: 操作语义层                                                │
│  ├── λRust 核心语言                                                 │
│  ├── 小步操作语义                                                   │
│  └── 内存模型                                                       │
│                              │                                      │
│  Level 0: 元理论层                                                  │
│  ├── 数学基础 (集合论, 范畴论)                                      │
│  ├── 可判定性理论                                                   │
│  └── 复杂性分析                                                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 各文件核心内容

### 02-01-rustbelt.md: RustBelt基础

**核心贡献**: Ralf Jung et al. (POPL 2018)

- **λRust**: Rust核心语言的形式化
- **Iris分离逻辑**: 高阶并发推理框架
- **类型语义**: 所有权谓词的数学定义
- **验证方法**: 机器检查的安全性证明

**关键数学对象**:

```
[[τ]].own : ThreadId → list Val → iProp
```

---

### 02-02-ownership-types.md: 所有权类型系统

**理论基础**: 线性类型、仿射类型

**核心概念**:

| 类型系统 | 弱化规则 | 收缩规则 | 对应Rust |
|---------|---------|---------|---------|
| 线性逻辑 | ✗ | ✗ | Copy类型 |
| 仿射逻辑 | ✓ | ✗ | 所有权类型 |
| 经典逻辑 | ✓ | ✓ | (不适用) |

**形式化规则**:

```
Γ ⊢ e : τ    Γ, x:τ ⊢ e' : τ'        (Move)
────────────────────────────────────────
Γ ⊢ let x = e in e' : τ'

Γ ⊢ e : !τ    Γ, x:τ, x:τ ⊢ e' : τ'  (Copy)
────────────────────────────────────────
Γ ⊢ let x = e in e' : τ'
```

---

### 02-03-borrow-semantics.md: 借用语义

**核心规则**: 别名 XOR 变异 (Aliasing XOR Mutation)

**形式化语义**:

```
共享借用:  [&τ].share(t, [ℓ]) ≡ ∀t'. &^α(∃v. ℓ ↦ v * [[τ]].share(t', v))
可变借用:  [&mut τ].own(t, [ℓ]) ≡ &^α(∃v. ℓ ↦ v * ▷[[τ]].own(t, v))
```

**借用关系代数**:

```
Borrow(ℓ, kind, region) where kind ∈ {Shared, Mut}

冲突检测:
loan(ℓ, Mut, r) ∧ loan(ℓ', _, r') ⊢ conflict
  if paths_conflict(ℓ, ℓ') ∧ regions_overlap(r, r')
```

---

### 02-04-lifetime-logic.md: 生命周期逻辑

**理论基础**: 区域代数 (Region Algebra)、Tofte-Talpin

**核心形式化**:

```
区域包含:     α ⊆ β  (生命周期α包含于β)
区域连接:     α ⊔ β  (区域的最小上界)
区域交汇:     α ⊓ β  (区域的最大下界)

生命周期上下文:
[[L]] ≡ ★_{α∈L} ([α]₁ * ([α]₁ ⇒ ◇[↑α]))
```

**约束求解**:

```
生命周期约束:   'a: 'b  ↔  region(a) ⊇ region(b)

子类型关系:     &'^a T <: &'^b T  if 'a: 'b
```

---

### 02-05-move-analysis.md: 移动语义分析

**核心分析**: 资源转移、Drop检查、所有权跟踪

**移动语义形式化**:

```
移动操作:    move(x) : τ → τ

资源状态:
  Owned(ℓ)      - 拥有位置ℓ的资源
  Borrowed(ℓ)   - 借用了位置ℓ
  Moved(ℓ)      - 资源已被移动
  Uninitialized - 未初始化状态
```

**Drop检查**:

```
Drop标志分析:
  Init(ℓ)  - 位置ℓ已初始化
  Drop(ℓ)  - 位置ℓ需要drop

移动后状态转换:
  Init(ℓ) --move--> Moved(ℓ) --drop--> ⊥
```

---

## 理论间的关联

### 概念映射图

```text
                    ┌─────────────────┐
                    │   Rust 概念      │
                    └────────┬────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│   线性逻辑     │   │  分离逻辑      │   │   区域类型     │
│  (Linear)     │   │  (Separation) │   │   (Regions)   │
└───────┬───────┘   └───────┬───────┘   └───────┬───────┘
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│   ⊗, ⊸, !     │   │   *, ↦, ▷     │   │    ⊆, ⊔, ⊓   │
│   张量积      │   │  分离合取      │   │   区域操作     │
│   线性蕴含    │   │  points-to    │   │               │
└───────────────┘   └───────────────┘   └───────────────┘
        │                    │                    │
        └────────────────────┼────────────────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   统一形式化     │
                    │  RustBelt/Iris  │
                    └─────────────────┘
```

---

## 形式化方法概览

### 1. 操作语义 (Operational Semantics)

```
小步语义:  (e, h) ↦ (e', h')

表达式求值与堆更新的关系
```

### 2. 逻辑关系 (Logical Relations)

```
类型安全性:  Γ ⊢ e : τ  ⟹  e 表现良好

上下文等价:  Γ ⊢ e₁ ≈ e₂ : τ
```

### 3. 分离逻辑 (Separation Logic)

```
Hoare三元组:  {P} e {v. Q(v)}

P, Q 是断言，* 是分离合取
```

---

## 数学符号参考

### 逻辑符号

| 符号 | 名称 | 含义 |
|-----|------|------|
| ⊢ | 推导 | 在上下文中可推导 |
| ≡ | 定义相等 | 按定义相等 |
| ⇒ | 蕴含 | 逻辑蕴含 |
| ∀ | 全称量词 | 对于所有 |
| ∃ | 存在量词 | 存在 |
| * | 分离合取 | 资源分离 |
| -∘ | 分离蕴含 | Magic wand |

### 模态符号

| 符号 | 名称 | 含义 |
|-----|------|------|
| □ | 持久性 | 无限复制 |
| ▷ | 下一步 | 延迟到下一步 |
| ◇ | 更新 | 原子更新 |
| ! | Of course | 指数模态 |
| ? | Why not | 指数模态 |

### 类型符号

| 符号 | 名称 | 含义 |
|-----|------|------|
| ⊗ | 张量积 | 线性积 |
| ⊸ | 线性蕴含 | 线性函数 |
| & | With | 加法合取 |
| ⊕ | Plus | 加法析取 |
| ⊤ | Top | 最大类型 |
| 0 | Zero | 空类型 |

---

## 可判定性总结

| 检查项目 | 复杂度 | 算法 |
|---------|-------|------|
| 类型推断 | PTIME | Hindley-Milner扩展 |
| 借用检查 | PTIME | NLL算法 |
| 生命周期检查 | PTIME | 约束求解 |
| 泛型约束求解 | 图灵完备 | 可能不终止 |
| Drop检查 | PTIME | 数据流分析 |

---

## 延伸阅读路径

### 基础路径

```
00-foundations/00-01-linear-logic.md
        ↓
00-foundations/00-02-affine-types.md
        ↓
01-core-concepts/01-01-ownership-rules.md
        ↓
02-formal-models/02-02-ownership-types.md
```

### 高级路径

```
02-formal-models/02-01-rustbelt.md
        ↓
02-formal-models/02-03-borrow-semantics.md
        ↓
02-formal-models/02-04-lifetime-logic.md
        ↓
03-verification-tools/03-01-verification-overview.md
```

---

## 参考文献

1. **RustBelt**: Jung, R., et al. (2018). *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL.
2. **Oxide**: Weiss, A., Patterson, D., & Ahmed, A. (2020). *Oxide: The Essence of Rust*. arXiv:1903.00982.
3. **Iris**: Jung, R., et al. (2018). *Iris from the Ground Up*. Journal of Functional Programming.
4. **线性逻辑**: Girard, J.-Y. (1987). *Linear Logic*. Theoretical Computer Science.
5. **仿射逻辑**: Kopylov, A.P. (2001). *Decidability of Linear Affine Logic*. Information and Computation.
6. **区域类型**: Tofte, M., & Talpin, J.-P. (1997). *Region-Based Memory Management*. Information and Computation.

---

## 贡献指南

向本目录添加新内容时，请确保：

1. **数学严谨性**: 包含明确的定义和定理
2. **形式化规则**: 使用标准推导规则格式
3. **Rust对应**: 解释与Rust概念的对应关系
4. **代码示例**: 提供可编译的Rust示例
5. **理论意义**: 讨论理论贡献和实际影响
