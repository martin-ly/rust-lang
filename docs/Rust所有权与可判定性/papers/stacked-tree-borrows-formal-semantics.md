# Stacked Borrows 与 Tree Borrows 完整形式语义

> 本文档提供Stacked Borrows和Tree Borrows的完整形式化操作语义
> 基于 Jung et al. (2021) Stacked Borrows 和 Ralf Jung 的 Tree Borrows

---

## 目录

- [Stacked Borrows 与 Tree Borrows 完整形式语义](#stacked-borrows-与-tree-borrows-完整形式语义)
  - [目录](#目录)
  - [1. Stacked Borrows 形式语义](#1-stacked-borrows-形式语义)
    - [1.1 配置定义](#11-配置定义)
    - [1.2 标签（Tag）定义](#12-标签tag定义)
    - [1.3 栈操作](#13-栈操作)
    - [1.4 操作语义规则](#14-操作语义规则)
      - [规则 1：创建唯一引用（retag Unique）](#规则-1创建唯一引用retag-unique)
      - [规则 2：创建共享只读引用（retag SharedReadOnly）](#规则-2创建共享只读引用retag-sharedreadonly)
      - [规则 3：创建两阶段借用（retag TwoPhase）](#规则-3创建两阶段借用retag-twophase)
      - [规则 4：使用引用（use tag）- 读操作](#规则-4使用引用use-tag--读操作)
      - [规则 5：使用引用（use tag）- 写操作](#规则-5使用引用use-tag--写操作)
      - [规则 6：弹出不兼容标签](#规则-6弹出不兼容标签)
    - [1.5 无效转换（Undefined Behavior）](#15-无效转换undefined-behavior)
  - [2. Tree Borrows 形式语义](#2-tree-borrows-形式语义)
    - [2.1 配置定义](#21-配置定义)
    - [2.2 权限树结构](#22-权限树结构)
    - [2.3 权限状态](#23-权限状态)
    - [2.4 状态转换规则](#24-状态转换规则)
      - [规则 1：Active → Frozen（创建子节点）](#规则-1active--frozen创建子节点)
      - [规则 2：Frozen → Disabled（父节点写入）](#规则-2frozen--disabled父节点写入)
      - [规则 3：Active 保持（无冲突访问）](#规则-3active-保持无冲突访问)
    - [2.5 访问检查规则](#25-访问检查规则)
    - [2.6 与Stacked Borrows的关键区别](#26-与stacked-borrows的关键区别)
  - [3. 别名模型与编译器优化](#3-别名模型与编译器优化)
    - [3.1 LLVM noalias 属性](#31-llvm-noalias-属性)
    - [3.2 优化示例](#32-优化示例)
  - [4. Miri中的实现](#4-miri中的实现)
    - [4.1 运行标志](#41-运行标志)
    - [4.2 常见UB模式检测](#42-常见ub模式检测)
  - [5. 形式化属性证明](#5-形式化属性证明)
    - [5.1 Stacked Borrows安全性](#51-stacked-borrows安全性)
    - [5.2 Tree Borrows正确性](#52-tree-borrows正确性)
  - [参考文献](#参考文献)

## 1. Stacked Borrows 形式语义

### 1.1 配置定义

**配置**：$C = \langle M, S, T \rangle$

- $M: \text{Loc} \to \text{Val}$：内存映射
- $S: \text{Loc} \to \text{Stack}\langle\text{Tag}\rangle$：每个位置的标签栈
- $T \subseteq \text{Tag}$：已使用的标签集合（用于生成新标签）

### 1.2 标签（Tag）定义

$$
\text{Tag} ::= \text{Untagged} \mid \text{Tagged}(n) \mid \text{Reserved}(n) \mid \text{SharedReadOnly}
$$

其中 $n \in \mathbb{N}$ 是标签标识符。

**标签语义**：

| 标签 | 含义 | 权限 |
|------|------|------|
| `Untagged` | 原始指针，无别名信息 | 无限制 |
| `Tagged(n)` | 唯一引用标签 | 独占读写 |
| `Reserved(n)` | 潜在唯一引用（两阶段借用）| 读取，可升级为独占 |
| `SharedReadOnly` | 共享只读引用 | 只读 |

### 1.3 栈操作

**栈操作定义**：

```text
push(S, tag):    将tag压入栈顶
pop(S):          弹出栈顶
pop_until(S, tag): 弹出直到tag在栈顶
remove(S, tag):  从栈中移除指定tag
top(S):          返回栈顶tag
```

### 1.4 操作语义规则

#### 规则 1：创建唯一引用（retag Unique）

$$
\frac{\ell \in \text{dom}(M) \quad n = \text{fresh}(T)}{\langle M, S, T \rangle \xrightarrow{\text{retag}(\ell, \text{Unique})} \langle M, S[\ell \mapsto \text{push}(S(\ell), \text{Tagged}(n))], T \cup \{n\} \rangle} \quad \text{[SB-RETAG-UNIQUE]}
$$

**条件**：新标签不能已在 $T$ 中。

#### 规则 2：创建共享只读引用（retag SharedReadOnly）

$$
\frac{\ell \in \text{dom}(M)}{\langle M, S, T \rangle \xrightarrow{\text{retag}(\ell, \text{SR})} \langle M, S[\ell \mapsto \text{push}(S(\ell), \text{SharedReadOnly})], T \rangle} \quad \text{[SB-RETAG-SRO]}
$$

#### 规则 3：创建两阶段借用（retag TwoPhase）

$$
\frac{\ell \in \text{dom}(M) \quad n = \text{fresh}(T)}{\langle M, S, T \rangle \xrightarrow{\text{retag}(\ell, \text{TwoPhase})} \langle M, S[\ell \mapsto \text{push}(S(\ell), \text{Reserved}(n))], T \cup \{n\} \rangle} \quad \text{[SB-RETAG-2PHASE]}
$$

#### 规则 4：使用引用（use tag）- 读操作

$$
\frac{\text{compatible\_read}(\text{top}(S(\ell)), \text{tag})}{\langle M, S, T \rangle \xrightarrow{\text{read}(\ell, \text{tag})} \langle M, S, T \rangle} \quad \text{[SB-USE-READ]}
$$

**兼容性检查**：

$$
\text{compatible\_read}(t_{\text{top}}, t_{\text{access}}) \triangleq
\begin{cases}
\text{true} & \text{if } t_{\text{access}} = \text{SharedReadOnly} \\
t_{\text{top}} = t_{\text{access}} & \text{if } t_{\text{access}} = \text{Tagged}(n) \\
t_{\text{top}} = t_{\text{access}} & \text{if } t_{\text{access}} = \text{Reserved}(n) \\
\text{true} & \text{if } t_{\text{access}} = \text{Untagged}
\end{cases}
$$

#### 规则 5：使用引用（use tag）- 写操作

对于 `Tagged(n)` 标签的写操作：

$$
\frac{\text{top}(S(\ell)) = \text{Tagged}(n)}{\langle M, S, T \rangle \xrightarrow{\text{write}(\ell, \text{Tagged}(n))} \langle M[\ell \mapsto v], S, T \rangle} \quad \text{[SB-USE-WRITE-UNIQUE]}
$$

对于 `Reserved(n)` 升级为 `Tagged(n)`：

$$
\frac{\text{top}(S(\ell)) = \text{Reserved}(n)}{\langle M, S, T \rangle \xrightarrow{\text{write}(\ell, \text{Reserved}(n))} \langle M[\ell \mapsto v], S[\ell \mapsto \text{replace}(S(\ell), \text{Reserved}(n), \text{Tagged}(n))], T \rangle} \quad \text{[SB-USE-WRITE-RESERVED]}
$$

#### 规则 6：弹出不兼容标签

当访问标签与栈顶不兼容时，弹出直到兼容或报错：

$$
\frac{\neg\text{compatible}(\text{top}(S(\ell)), \text{tag}) \quad S' = \text{pop\_until\_compatible}(S(\ell), \text{tag})}{\langle M, S, T \rangle \xrightarrow{\text{access}(\ell, \text{tag})} \langle M, S[\ell \mapsto S'], T \rangle} \quad \text{[SB-POP-INCOMPATIBLE]}
$$

### 1.5 无效转换（Undefined Behavior）

以下情况触发UB：

1. **使用已弹出的标签**：
   $$\text{tag} \notin S(\ell) \land \text{tag} \neq \text{Untagged}$$

2. **通过 SharedReadOnly 写入**：
   $$\text{write}(\ell, \text{SharedReadOnly})$$

3. **未授权写入**：
   $$\text{write}(\ell, \text{tag}) \land \text{tag} \notin \{\text{Tagged}(n), \text{Reserved}(n)\}$$

---

## 2. Tree Borrows 形式语义

### 2.1 配置定义

**配置**：$C = \langle M, T, P \rangle$

- $M: \text{Loc} \to \text{Val}$：内存映射
- $T$：权限树（Permission Tree）
- $P: \text{Tag} \to \text{Permission}$：标签到权限状态的映射

### 2.2 权限树结构

权限树是引用派生关系的树形表示：

```text
Tree Node ::=
  | Root(ℓ)                    // 内存位置根节点
  | Node(tag, parent, children) // 引用标签节点

tag ::= Unique(n) | Shared(n) | Reserved(n)
```

**派生关系**：

- `Root` 是树的根
- 从 `&x` 创建 `&y`：新节点作为子节点添加
- 树反映了引用的"派生历史"

### 2.3 权限状态

每个标签有权限状态：

$$
\text{Permission} ::= \text{Active} \mid \text{Frozen} \mid \text{Disabled} \mid \text{Undefined}
$$

**状态语义**：

| 状态 | 读权限 | 写权限 | 说明 |
|------|--------|--------|------|
| `Active` | ✓ | ✓ | 唯一引用，完全权限 |
| `Frozen` | ✓ | ✗ | 共享引用或父节点有子节点 |
| `Disabled` | ✗ | ✗ | 已被禁用（父节点可变借用）|
| `Undefined` | ✗ | ✗ | 从未定义或已过期 |

### 2.4 状态转换规则

**转换图**：

```text
                    创建子Active
    ┌─────────────────────────────────┐
    │                                 ▼
Active ────────► Frozen              Active(子)
    │    创建子节点    │                  │
    │                  │ 父节点写入       │ 子节点结束
    │                  ▼                  │
    │              Disabled ◄─────────────┘
    │   父节点写入      ▲
    └───────────────────┘
```

#### 规则 1：Active → Frozen（创建子节点）

$$
\frac{P(\text{parent}) = \text{Active} \quad \text{create\_child}(\text{parent}, \text{child})}{P' = P[\text{parent} \mapsto \text{Frozen}, \text{child} \mapsto \text{Active}]} \quad \text{[TB-SPAWN-CHILD]}
$$

#### 规则 2：Frozen → Disabled（父节点写入）

$$
\frac{P(\text{parent}) = \text{Frozen} \quad \text{write\_via}(\text{ancestor})}{P' = P[\text{parent} \mapsto \text{Disabled}]} \quad \text{[TB-PARENT-WRITE]}
$$

#### 规则 3：Active 保持（无冲突访问）

$$
\frac{P(\text{tag}) = \text{Active} \quad \neg\text{conflicting\_access}(\text{tag}, \text{access})}{P' = P} \quad \text{[TB-ACTIVE-KEEP]}
$$

### 2.5 访问检查规则

**读取检查**：

$$
\text{can\_read}(\text{tag}) \triangleq P(\text{tag}) \in \{\text{Active}, \text{Frozen}\}
$$

**写入检查**：

$$
\text{can\_write}(\text{tag}) \triangleq P(\text{tag}) = \text{Active}
$$

**冲突处理**：

对于通过 `tag_a` 的访问，所有相关标签 `tag_x`：

1. 若 `tag_a` 是 `tag_x` 的祖先且写入：禁用 `tag_x`
2. 若 `tag_x` 是 `tag_a` 的祖先且 `tag_x` 是 Frozen：报错（父节点不应被写入）

### 2.6 与Stacked Borrows的关键区别

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| 结构 | 栈（线性） | 树（层次） |
| 子借用处理 | 重新借用（reborrow） | 派生（spawn） |
| 父节点失效 | 弹出（pop） | 冻结（freeze） |
| 优化友好性 | 中等 | 更高 |
| 复杂模式支持 | 有限 | 更强 |

---

## 3. 别名模型与编译器优化

### 3.1 LLVM noalias 属性

**生成规则**：

```
对于 &mut T（Tagged(n)）:
  生成 noalias 属性
  假设：该指针是唯一访问路径

对于 &T（SharedReadOnly 或 Frozen）:
  不生成 noalias
  允许其他只读别名
```

### 3.2 优化示例

**CSE（公共子表达式消除）**：

```rust
// 源代码
let x = *ptr;
let y = *ptr;  // 可以消除第二次读取？
```

在 Stacked Borrows 下：

- 若 `ptr` 是 `Unique`：两次读取间无写入，可消除
- 若 `ptr` 是 `SharedReadOnly`：两次读取间无写入，可消除

**循环不变量外提**：

```rust
// 源代码
for i in 0..n {
    let x = *ptr;  // 可以外提？
}
```

条件：

- `ptr` 在循环内不被写入
- 基于借用状态判断

---

## 4. Miri中的实现

### 4.1 运行标志

```bash
# Stacked Borrows（默认）
cargo +nightly miri test

# Tree Borrows
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test

# 宽松模式
MIRIFLAGS="-Zmiri-permissive-provenance" cargo +nightly miri test
```

### 4.2 常见UB模式检测

**Stacked Borrows检测**：

```rust
// UB: 通过父引用访问已被弹出的子借用
let mut x = 5;
let r1 = &mut x as *mut i32;
let r2 = &mut x as *mut i32;  // 重新借用，r1被弹出
unsafe { *r1 = 10; }  // UB! r1已无效
```

**Tree Borrows允许**：

```rust
// Tree Borrows允许：父节点冻结而非失效
let mut x = 5;
let r1 = &mut x as *mut i32;
let r2 = &mut x as *mut i32;  // r1被冻结
unsafe { *r1 = 10; }  // Tree Borrows: 从Frozen→Disabled，允许
```

---

## 5. 形式化属性证明

### 5.1 Stacked Borrows安全性

**定理（Stacked Borrows无数据竞争）**：

对于任意配置 $C = \langle M, S, T \rangle$，若执行步骤 $C \to C'$ 不触发UB，则：

$$
\neg\exists \ell. \text{concurrent\_write\_access}(\ell)
$$

**证明概要**：

1. 唯一写权限：`Tagged(n)` 是栈中唯一允许写入的标签
2. 写前检查：写入前必须检查栈顶是 `Tagged(n)`
3. 无并发：单线程模型，借用过期才释放

### 5.2 Tree Borrows正确性

**定理（Tree Borrows权限单调性）**：

对于任意标签 $\text{tag}$，其权限状态随时间单调递减：

$$
\text{Active} \succeq \text{Frozen} \succeq \text{Disabled} \succeq \text{Undefined}
$$

**证明**：检查所有转换规则，权限只向更低状态转换。

---

## 参考文献

1. Jung, R., et al. (2021). Stacked Borrows: An Aliasing Model for Rust. POPL.
2. Jung, R. (2023). Tree Borrows. <https://www.ralfj.de/blog/2023/06/02/tree-borrows.html>
3. LLVM Project. (2024). noalias and alias.scope Metadata. LLVM Documentation.
4. Rust Project. (2024). Miri - Undefined Behavior Detection. <https://github.com/rust-lang/miri>

---

*本文档为《Rust所有权与可判定性》项目的学术对齐补充材料*
