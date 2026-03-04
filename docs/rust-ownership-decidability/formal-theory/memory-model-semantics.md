# Rust 内存模型语义形式化理论

## 目录

- [Rust 内存模型语义形式化理论](#rust-内存模型语义形式化理论)
  - [目录](#目录)
  - [引言](#引言)
    - [形式化目标](#形式化目标)
    - [核心概念](#核心概念)
  - [内存模型基础](#内存模型基础)
    - [2.1 内存抽象](#21-内存抽象)
      - [2.1.1 内存状态定义](#211-内存状态定义)
      - [2.1.2 内存操作](#212-内存操作)
    - [2.2 有效性条件](#22-有效性条件)
      - [2.2.1 有效值定义](#221-有效值定义)
      - [2.2.2 类型有效性](#222-类型有效性)
    - [2.3 所有权状态机](#23-所有权状态机)
  - [栈语义](#栈语义)
    - [3.1 栈帧结构](#31-栈帧结构)
      - [3.1.1 栈帧定义](#311-栈帧定义)
      - [3.1.2 栈操作语义](#312-栈操作语义)
    - [3.2 局部变量生命周期](#32-局部变量生命周期)
      - [3.2.1 生命周期规则](#321-生命周期规则)
      - [3.2.2 生命周期结束处理](#322-生命周期结束处理)
    - [3.3 栈展开 (Unwinding)](#33-栈展开-unwinding)
      - [3.3.1 panic 语义](#331-panic-语义)
      - [3.3.2 析构顺序](#332-析构顺序)
  - [堆语义](#堆语义)
    - [4.1 堆分配](#41-堆分配)
      - [4.1.1 分配语义](#411-分配语义)
      - [4.1.2 Box 语义](#412-box-语义)
    - [4.2 所有权转移](#42-所有权转移)
      - [4.2.1 移动语义形式化](#421-移动语义形式化)
      - [4.2.2 复制语义形式化](#422-复制语义形式化)
    - [4.3 Rc 和 Arc 语义](#43-rc-和-arc-语义)
      - [4.3.1 引用计数形式化](#431-引用计数形式化)
  - [内存布局与对齐](#内存布局与对齐)
    - [5.1 类型布局计算](#51-类型布局计算)
      - [5.1.1 基本类型布局](#511-基本类型布局)
      - [5.1.2 结构体布局](#512-结构体布局)
      - [5.1.3 枚举布局](#513-枚举布局)
    - [5.2 对齐约束](#52-对齐约束)
      - [5.2.1 对齐要求](#521-对齐要求)
      - [5.2.2 未对齐访问](#522-未对齐访问)
    - [5.3 零大小类型 (ZST)](#53-零大小类型-zst)
      - [5.3.1 ZST 定义](#531-zst-定义)
      - [5.3.2 ZST 语义](#532-zst-语义)
  - [借用与别名模型](#借用与别名模型)
    - [6.1 借用规则](#61-借用规则)
      - [6.1.1 基本借用规则（Rust 保证）](#611-基本借用规则rust-保证)
      - [6.1.2 形式化借用状态](#612-形式化借用状态)
    - [6.2 Stacked Borrows 模型](#62-stacked-borrows-模型)
      - [6.2.1 栈结构](#621-栈结构)
      - [6.2.2 借用操作语义](#622-借用操作语义)
      - [6.2.3 使用检查](#623-使用检查)
    - [6.3 Tree Borrows 模型](#63-tree-borrows-模型)
      - [6.3.1 树结构](#631-树结构)
      - [6.3.2 重新借用](#632-重新借用)
      - [6.3.3 访问验证](#633-访问验证)
    - [6.4 内部可变性](#64-内部可变性)
      - [6.4.1 Cell 语义](#641-cell-语义)
      - [6.4.2 RefCell 语义](#642-refcell-语义)
  - [形式化语义](#形式化语义)
    - [7.1 小步操作语义](#71-小步操作语义)
      - [7.1.1 配置定义](#711-配置定义)
      - [7.1.2 求值规则](#712-求值规则)
    - [7.2 内存安全定理](#72-内存安全定理)
      - [7.2.1 类型安全保证](#721-类型安全保证)
      - [7.2.2 进展性与保持性](#722-进展性与保持性)
  - [证明概要](#证明概要)
    - [8.1 所有权正确性证明](#81-所有权正确性证明)
    - [8.2 借用安全性证明](#82-借用安全性证明)
    - [8.3 无数据竞争证明](#83-无数据竞争证明)
    - [8.4 内存泄漏安全](#84-内存泄漏安全)
  - [参考文献](#参考文献)
    - [Rust 内存模型](#rust-内存模型)
    - [内存安全形式化](#内存安全形式化)
    - [别名分析](#别名分析)
    - [类型系统与内存](#类型系统与内存)
    - [并发与同步](#并发与同步)
  - [附录 A：内存布局示例](#附录-a内存布局示例)
    - [A.1 结构体布局](#a1-结构体布局)
    - [A.2 枚举布局](#a2-枚举布局)
  - [附录 B：借用检查示例](#附录-b借用检查示例)
    - [B.1 基本借用检查](#b1-基本借用检查)

---

## 引言

Rust 的内存模型是其内存安全保证的核心基础。
不同于传统系统语言（如 C/C++），Rust 在编译期通过所有权系统强制执行严格的内存访问规则，从而避免了空指针解引用、双重释放、数据竞争等内存错误。

### 形式化目标

本文档旨在形式化 Rust 内存模型的以下方面：

- **栈语义**：函数调用栈、局部变量生命周期
- **堆语义**：动态分配、所有权转移
- **内存布局**：对齐、填充、类型布局计算
- **别名模型**：Stacked Borrows / Tree Borrows
- **有效性不变式**：哪些内存访问是合法的

### 核心概念

```
内存安全三要素：
1. 所有权 (Ownership)：每个值有唯一的所有者
2. 借用 (Borrowing)：临时访问权限授予
3. 生命周期 (Lifetimes)：引用有效性的编译期跟踪
```

---

## 内存模型基础

### 2.1 内存抽象

#### 2.1.1 内存状态定义

```
Memory ::= Location → Value ∪ {⊥, uninit}

Location ::= StackFrame × Offset    (栈位置)
          | HeapAddress              (堆地址)
          | StaticAddress            (静态/全局地址)

Value ::= Primitive(n)              (基本值)
       | Pointer(Location)          (裸指针)
       | Reference(Location, Perm)  (引用)

Perm ::= Own                        (所有权)
      | Shared(ℓ)                   (共享借用)
      | MutBorrow(ℓ)                (可变借用)
      | Raw                         (原始指针权限)
```

#### 2.1.2 内存操作

```
read : Memory × Location → Value ∪ {error}
write : Memory × Location × Value → Memory ∪ {error}
allocate : Memory × Size × Align → (Memory, Location)
deallocate : Memory × Location → Memory ∪ {error}
```

### 2.2 有效性条件

#### 2.2.1 有效值定义

一个值在内存位置 `loc` 处是**有效的**，当且仅当：

```
valid(Memory, loc, τ) :=
  1. loc 已分配
  2. loc 已初始化（非 uninit）
  3. loc 满足类型 τ 的对齐要求
  4. 类型 τ 的所有不变式成立
```

#### 2.2.2 类型有效性

```
valid_val(v, Int) := v ∈ ℤ
valid_val(v, Bool) := v ∈ {true, false}
valid_val(v, &ℓ τ) :=
    v = Reference(loc, perm) ∧
    valid(Memory, loc, τ) ∧
    lifetime(loc) ⊇ ℓ
valid_val(v, Box<τ>) :=
    v = Pointer(loc) ∧
    valid(Memory, loc, τ) ∧
    Memory(loc).owner = current_thread
```

### 2.3 所有权状态机

```
                    move
    Owned ───────────────────────────→ Moved
       │                                  │
       │ borrow_mut                       │
       ↓                                  │
   MutBorrowed ←──── return ─────────────┘
       │
       │ borrow_shared
       ↓
   SharedBorrowed
       ↑
       │
   (多个共享借用可共存)
```

---

## 栈语义

### 3.1 栈帧结构

#### 3.1.1 栈帧定义

```
StackFrame ::= {
    function: FunctionName,
    locals: LocalId → (Type, Value, State),
    return_addr: Address,
    parent: Option<StackFrameId>
}

State ::= Uninitialized | Initialized | Moved | Borrowed(Permission)
```

#### 3.1.2 栈操作语义

**函数调用 (Call)**：

```
enter_stack(F, args):
    1. 创建新栈帧 S
    2. 分配参数空间: params(F) → args
    3. 设置返回地址
    4. 压入调用栈
```

**函数返回 (Return)**：

```
exit_stack(S, ret_val):
    1. 验证所有借用已归还
    2. 执行析构函数 (drop)
    3. 释放栈帧资源
    4. 返回 ret_val 给调用者
```

### 3.2 局部变量生命周期

#### 3.2.1 生命周期规则

```
Γ ⊢ let x: τ = e:
    1. 为 x 分配栈空间 sizeof(τ)
    2. 计算 e 得值 v
    3. 写入 x ← v
    4. x 的生命周期开始于声明点
    5. x 的生命周期结束于作用域末尾
```

#### 3.2.2 生命周期结束处理

```
end_of_scope(x):
    if State(x) = Initialized then
        if needs_drop(τ) then
            call_drop(x)
        deallocate(x)
    else if State(x) = Borrowed then
        error: 未归还的借用
```

### 3.3 栈展开 (Unwinding)

#### 3.3.1 panic 语义

```
panic!(msg):
    1. 标记 panic 状态
    2. 从当前栈帧开始向上遍历
    3. 对每个栈帧执行 landing pad:
       a. 执行析构函数
       b. 释放资源
    4. 到达 catch_unwind 或程序终止
```

#### 3.3.2 析构顺序

```
逆序析构规则 (LIFO)：
    let a = ...;
    let b = ...;
    let c = ...;
    // 作用域结束时的析构顺序: c → b → a
```

---

## 堆语义

### 4.1 堆分配

#### 4.1.1 分配语义

```
allocate_heap(τ):
    Precondition:
        - 存在足够的堆内存
    Action:
        1. loc = malloc(sizeof(τ), alignof(τ))
        2. Memory(loc) = uninit
    Postcondition:
        - Memory'(loc) = uninit
        - owns(loc, current_thread)
    Returns: Pointer(loc)
```

#### 4.1.2 Box<T> 语义

```
Box::new(e):
    1. p = allocate_heap(τ)
    2. v = eval(e)
    3. *p = v
    4. return Box(p)  // 拥有唯一所有权

Box 解引用 (*b):
    1. assert(owns(b.ptr))
    2. return Memory(b.ptr)

Drop(Box):
    1. if owns(ptr) then
           drop_in_place(ptr)
           deallocate_heap(ptr)
```

### 4.2 所有权转移

#### 4.2.1 移动语义形式化

```
move(src) → dst:
    Precondition:
        - State(src) ∈ {Initialized, Owned}
    Action:
        1. v = Memory(src)
        2. State(src) := Moved
        3. State(dst) := Initialized
        4. Memory(dst) := v
        5. transfer_ownership(src, dst)
    Postcondition:
        - State(src) = Moved
        - State(dst) = Initialized
        - owns(dst, current_thread)
```

#### 4.2.2 复制语义形式化

```
copy(src) → dst:
    Precondition:
        - Copy trait: τ implements Copy
        - State(src) = Initialized
    Action:
        1. v = bitwise_copy(Memory(src))
        2. State(dst) := Initialized
        3. Memory(dst) := v
    Postcondition:
        - State(src) = Initialized  (不变)
        - State(dst) = Initialized
```

### 4.3 Rc 和 Arc 语义

#### 4.3.1 引用计数形式化

```
Rc<T> ::= (ptr: *mut RcBox<T>)

RcBox<T> ::= {
    strong_count: usize,
    weak_count: usize,
    value: T
}
```

**Rc::new**：

```
Rc::new(v):
    1. box = allocate_heap(RcBox<T>)
    2. box.strong_count = 1
    3. box.weak_count = 0
    4. box.value = v
    5. return Rc(box)
```

**Clone (Rc)**：

```
clone(rc):
    1. (*rc.ptr).strong_count += 1
    2. return Rc(rc.ptr)
```

**Drop (Rc)**：

```
drop(rc):
    1. (*rc.ptr).strong_count -= 1
    2. if (*rc.ptr).strong_count == 0 then
           drop_in_place(&mut (*rc.ptr).value)
           if (*rc.ptr).weak_count == 0 then
               deallocate_heap(rc.ptr)
```

---

## 内存布局与对齐

### 5.1 类型布局计算

#### 5.1.1 基本类型布局

```
layout(Int8)   = { size: 1, align: 1 }
layout(Int16)  = { size: 2, align: 2 }
layout(Int32)  = { size: 4, align: 4 }
layout(Int64)  = { size: 8, align: 8 }
layout(Int128) = { size: 16, align: 16 }
layout(Bool)   = { size: 1, align: 1 }
layout(Char)   = { size: 4, align: 4 }
```

#### 5.1.2 结构体布局

```
layout(struct { f₁: τ₁, ..., fₙ: τₙ }) =
    let l₁ = layout(τ₁)
    ...
    let lₙ = layout(τₙ)
    let align = max(l₁.align, ..., lₙ.align)
    let size = compute_struct_size([(τ₁,l₁), ..., (τₙ,lₙ)], align)
    return { size, align }

compute_struct_size(fields, align):
    offset = 0
    for (τ, l) in fields:
        offset = align_to(offset, l.align)  // 添加填充
        record_offset(τ, offset)
        offset += l.size
    offset = align_to(offset, align)  // 尾部对齐
    return offset
```

#### 5.1.3 枚举布局

```
layout(enum { V₁(τ₁), ..., Vₙ(τₙ) }) =
    let discriminant_size = min_bytes_to_represent(n)
    let discriminant_align = 1 (通常)
    let max_variant_size = max(size(τ₁), ..., size(τₙ))
    let max_variant_align = max(align(τ₁), ..., align(τₙ))
    let align = max(discriminant_align, max_variant_align)
    let size = discriminant_size + padding + max_variant_size
    size = align_to(size, align)
    return { size, align, discriminant_size }
```

### 5.2 对齐约束

#### 5.2.1 对齐要求

```
align_to(addr, align) = ((addr + align - 1) / align) * align

检查: addr % align == 0
```

#### 5.2.2 未对齐访问

```
read_unaligned<T>(ptr):
    - 允许读取未对齐数据
    - 可能性能较差
    - 仍要求 ptr 有效且可访问
```

### 5.3 零大小类型 (ZST)

#### 5.3.1 ZST 定义

```
is_zst(τ) := layout(τ).size == 0

ZST 示例：
- () - 单元类型
- PhantomData<T> - 幻影数据
- [T; 0] - 空数组
- 空结构体 struct Foo;
```

#### 5.3.2 ZST 语义

```
layout(ZST) = { size: 0, align: 1 }

ZST 特性：
1. 所有 ZST 值在运行时等价
2. ZST 引用可以悬挂（dangling）
3. ZST 不占用内存，但仍需正确对齐
4. ZST 数组 stride = max(1, alignof(T))
```

---

## 借用与别名模型

### 6.1 借用规则

#### 6.1.1 基本借用规则（Rust 保证）

```
借用规则 (Borrow Checker):
1. 在任意时刻，只能有：
   a) 一个可变引用 &mut T，或
   b) 任意数量的不可变引用 &T
2. 引用必须总是有效的（指向有效的内存）
3. 可变引用具有唯一性保证
```

#### 6.1.2 形式化借用状态

```
BorrowState ::=
    | Inactive              (未激活)
    | Shared { count: ℕ }   (共享借用，计数)
    | Mutable               (可变借用)
    | Disabled              (被禁用，来自父借用)

Permissions ::= Location → BorrowState
```

### 6.2 Stacked Borrows 模型

#### 6.2.1 栈结构

```
BorrowStack ::= List<BorrowItem>

BorrowItem ::=
    | Unique(tag)          (唯一借用，带标签)
    | SharedReadOnly       (共享只读)
    | SharedReadWrite(tag) (共享读写，用于内部可变性)
    | Untagged             (无标签，不安全代码)

tag ::= ℕ  (唯一标识符)
```

#### 6.2.2 借用操作语义

**创建共享借用**：

```
&x @ tag:
    1. 找到包含 x 的内存位置的 BorrowStack
    2. 弹出所有 Disabled 项目
    3. 如果栈顶是 Unique(_):
           将栈顶标记为 Disabled
       如果栈顶是 SharedReadOnly:
           保持不变
       如果栈顶是 SharedReadWrite(_):
           保持不变
    4. 压入 SharedReadOnly
    5. 返回带 tag 的引用
```

**创建可变借用**：

```
&mut x @ tag:
    1. 找到包含 x 的内存位置的 BorrowStack
    2. 弹出所有不在栈底的 SharedReadOnly
    3. 验证当前有 Unique 权限
    4. 将所有上层 Unique 标记为 Disabled
    5. 压入 Unique(tag)
    6. 返回带 tag 的引用
```

#### 6.2.3 使用检查

```
use(ptr, access_kind):
    1. 找到 ptr 对应的 BorrowStack
    2. 从栈顶向下查找 ptr.tag
    3. 如果未找到或已 Disabled:
           error: 非法内存访问
    4. 验证访问权限:
           - 读操作: SharedReadOnly, SharedReadWrite, Unique 都允许
           - 写操作: 只允许 Unique 和 SharedReadWrite
```

### 6.3 Tree Borrows 模型

#### 6.3.1 树结构

Tree Borrows 是 Stacked Borrows 的改进，使用树结构处理重新借用：

```
BorrowTree ::= Node<BorrowItem, List<BorrowTree>>

每个节点记录：
- 权限类型
- 父节点引用
- 子节点列表
- 活跃状态
```

#### 6.3.2 重新借用

```
reborrow(parent, new_tag, permission):
    1. 在 BorrowTree 中找到 parent 对应的节点
    2. 创建新节点 new_tag，作为 parent 的子节点
    3. 新节点继承适当的权限
    4. 根据父子关系更新权限传播
```

#### 6.3.3 访问验证

```
validate_access(tree, tag, access):
    1. 找到 tag 对应的节点
    2. 检查节点是否活跃
    3. 验证访问权限不违反父节点约束
    4. 对于写操作，可能需要冻结兄弟节点
```

### 6.4 内部可变性

#### 6.4.1 Cell<T> 语义

```
Cell<T> ::= { value: UnsafeCell<T> }

Cell::new(v):
    return Cell { value: UnsafeCell::new(v) }

Cell::get(&self):
    1. // 注意：Cell<T> 要求 T: Copy
    2. unsafe { *self.value.get() }

Cell::set(&self, v):
    1. unsafe { *self.value.get() = v }
    // 即使在共享引用上也可调用！
```

#### 6.4.2 RefCell<T> 语义

```
RefCell<T> ::= {
    value: UnsafeCell<T>,
    state: Cell<BorrowState>
}

RefCell::borrow(&self):
    match self.state.get():
        Inactive | Shared(n) => {
            self.state.set(Shared(n+1));
            Ref { cell: self }
        }
        Mutable => panic!("already borrowed mutably")

RefCell::borrow_mut(&self):
    match self.state.get():
        Inactive => {
            self.state.set(Mutable);
            RefMut { cell: self }
        }
        _ => panic!("already borrowed")
```

---

## 形式化语义

### 7.1 小步操作语义

#### 7.1.1 配置定义

```
Configuration ::= (Expression, Stack, Heap, Permissions)

Stack ::= List<StackFrame>
Heap ::= Address → Object
Permissions ::= Location → BorrowStack
```

#### 7.1.2 求值规则

**变量查找**：

```
〈x, σ, h, π〉→ 〈v, σ, h, π〉
其中 v = lookup(σ, x)
```

**赋值**：

```
〈x = e, σ, h, π〉→ 〈x = e', σ', h', π'〉
    if 〈e, σ, h, π〉→ 〈e', σ', h', π'〉

〈x = v, σ, h, π〉→ 〈(), σ[x↦v], h, π〉
    if valid_write(π, x)
```

**函数调用**：

```
〈f(e₁, ..., eₙ), σ, h, π〉→
〈e_body[params↦values], σ', h, π'〉
其中：
    - (e₁, ..., eₙ) 已求值为 (v₁, ..., vₙ)
    - σ' = push_frame(f, [v₁, ..., vₙ], σ)
```

### 7.2 内存安全定理

#### 7.2.1 类型安全保证

**定理 7.1 (内存安全)**：
如果程序 p 通过 Rust 借用检查，则在执行过程中：

1. 不会发生空指针解引用
2. 不会发生使用-after-free
3. 不会发生数据竞争
4. 不会发生缓冲区溢出

*证明概要*：

- 借用检查器确保所有引用在生命周期内有效
- 所有权系统确保内存正确释放
- 类型系统区分线程安全类型

#### 7.2.2 进展性与保持性

**引理 7.2 (进展性)**：
良类型的程序不会 stuck，除非：

- 到达正常终止
- 显式调用 panic!()
- 外部 I/O 阻塞

**引理 7.3 (保持性)**：
执行步骤保持类型正确性：
如果 Γ ⊢ e : τ 且 〈e, σ, h, π〉→ 〈e', σ', h', π'〉，
则 Γ' ⊢ e' : τ 且不变式在 σ', h', π' 下成立。

---

## 证明概要

### 8.1 所有权正确性证明

**定理 8.1 (所有权唯一性)**：
在任意程序点，每个堆分配单元最多有一个所有者。

*证明*：

1. 分配时创建唯一所有权（Box::new）
2. 移动转移所有权，原位置标记为 Moved
3. 借用不转移所有权
4. 通过类型系统强制检查

### 8.2 借用安全性证明

**定理 8.2 (借用隔离)**：
可变借用和任何其他借用不能共存。

*证明*：

1. 借用检查器在编译期验证
2. 别名模型（Stacked/Tree Borrows）在运行时验证
3. 两者都保证互斥性质

### 8.3 无数据竞争证明

**定理 8.3 (无数据竞争)**：
Safe Rust 代码不会出现数据竞争。

*证明*：

1. Sync trait 标记线程安全共享类型
2. Send trait 标记线程安全转移类型
3. 类型系统确保跨线程访问遵循借用规则
4. 内部可变性需要 Sync 实现

### 8.4 内存泄漏安全

**注意**：Rust 不保证无内存泄漏，但保证：

**定理 8.4 (确定性析构)**：
值在作用域结束时确定性析构（除非被泄漏）。

*证明*：

1. 编译器在作用域结束处插入 drop 调用
2. 所有权转移时更新责任
3. Rc/Arc 在引用计数为零时析构

---

## 参考文献

### Rust 内存模型

1. **Jung, R., et al.** (2019). Stacked Borrows: An aliasing model for Rust. *POPL '20*.
   - Rust 别名模型的开创性工作

2. **Jung, R., et al.** (2021). Tree Borrows: An aliasing model for Rust. *Draft*.
   - Stacked Borrows 的改进模型

3. **Jung, R.** (2020). Understanding and evolving the Rust programming language. *PhD Thesis*.
   - Rust 形式化语义的全面论述

4. **Weiss, A., et al.** (2021). Ownership in Rust 101. *Tutorial*.
   - 所有权系统入门

### 内存安全形式化

1. **RustBelt Team.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.
   - Rust 内存安全的机器化证明

2. **Tarditi, D.** (2016). The semantics of Rust. *Microsoft Research*.
   - Rust 语义研究

3. **Patrignani, M., & Clarke, D.** (2015). Interruptible interfaces. *CSF '15*.
   - 内存安全接口的形式化

### 别名分析

1. **Horn, D. V., & Might, M.** (2010). Abstracting abstract machines. *ICFP '10*.
   - 抽象机形式化方法

2. **Calcagno, C., et al.** (2011). Compositional shape analysis. *POPL '11*.
   - 基于分离逻辑的形状分析

3. **Reynolds, J. C.** (2002). Separation logic: A logic for shared mutable data structures. *LICS '02*.
    - 分离逻辑基础

### 类型系统与内存

1. **Pierce, B. C.** (2002). *Types and Programming Languages*. MIT Press.
    - 类型理论标准教材

2. **Grossman, D., et al.** (2002). Region-based memory management in Cyclone. *PLDI '02*.
    - 区域内存管理

3. **Fluet, M., et al.** (2006). Linear regions are all you need. *ESOP '06*.
    - 线性类型与区域

### 并发与同步

1. **Vafeiadis, V.** (2010). RGSep action inference. *VMCAI '10*.
    - 并发程序验证

2. **Turon, A., et al.** (2013). Calculating correct concurrent memory models. *PLDI '13*.
    - 并发内存模型计算

---

## 附录 A：内存布局示例

### A.1 结构体布局

```rust
struct Example {
    a: u8,      // 1 byte
    b: u32,     // 4 bytes
    c: u16,     // 2 bytes
}
```

布局计算：

```
字段 a: offset 0, size 1
填充: 3 bytes (对齐到 b 的 4 字节边界)
字段 b: offset 4, size 4
字段 c: offset 8, size 2
尾部填充: 2 bytes (对齐到 4 字节)
─────────────────────────────
总大小: 12 bytes
对齐: 4 bytes
```

### A.2 枚举布局

```rust
enum Message {
    Quit,                           // 0 字段
    Move { x: i32, y: i32 },        // 2 字段
    Write(String),                  // 1 字段
    ChangeColor(i32, i32, i32),     // 3 字段
}
```

布局：

```
discriminant: 1 byte (4 个变体)
padding: 7 bytes (64 位对齐)
union of variants:
    - Quit: 0 bytes
    - Move: 8 bytes (2 × i32)
    - Write: 24 bytes (String)
    - ChangeColor: 12 bytes (3 × i32)
总大小: 1 + 7 + 24 = 32 bytes
```

---

## 附录 B：借用检查示例

### B.1 基本借用检查

```rust
let mut x = 5;
let y = &mut x;    // 可变借用开始
*y = 10;           // 通过借用修改
let z = &x;        // ERROR: 不能同时有可变和不可变借用
println!("{}", y); // 可变借用最后使用
```

形式化分析：

```
L0: x: Own(i32)
L1: y: MutBorrow(L0) from x
L2: *y = 10       [valid: y active]
L3: z: SharedBorrow(L0)  [invalid: MutBorrow active]
```

---

*文档版本：1.0.0*
*最后更新：2026年3月*
*作者：Rust 形式化理论研究组*
