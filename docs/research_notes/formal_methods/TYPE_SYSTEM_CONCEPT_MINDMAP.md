# 类型系统概念族谱

> **创建日期**: 2026-02-24
> **更新状态**: 完善 (Phase 1 Week 5)
> **任务ID**: P1-W5-T2

---

## 类型系统概念全景

```text
                        类型系统概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【基础类型】            【复合类型】            【抽象类型】
        │                      │                      │
    ├─标量类型            ├─struct              ├─泛型
    │  ├─整数              │  ├─命名字段         │  ├─类型参数
    │  │  ├─i8/i16        │  ├─元组结构体         │  ├─约束
    │  │  ├─i32/i64       │  └─单元结构体         │  └─边界
    │  │  ├─i128          │                      │
    │  │  └─isize        ├─enum                 ├─Trait
    │  ├─无符号整数        │  ├─变体              │  ├─接口定义
    │  │  ├─u8/u16        │  ├─携带数据          │  ├─实现
    │  │  ├─u32/u64       │  └─判别式            │  └─对象安全
    │  │  └─usize        │                      │
    │  ├─浮点            ├─tuple                ├─impl Trait
    │  │  ├─f32          │  ├─固定长度          │  └─匿名实现
    │  │  └─f64          │  └─异构类型           │
    │  ├─布尔            │                      └─dyn Trait
    │  │  └─bool         ├─array                 └─动态分发
    │  ├─字符             │  ├─固定长度
    │  │  └─char         │  └─同构类型
    │  └─单元类型         │
           └─()          └─slice
                           └─动态长度
```

---

## 一、基础类型详解

### 1.1 标量类型

```text
标量类型
├── 整数
│   ├── 有符号
│   │   ├── i8  (-128 to 127)
│   │   ├── i16 (-32768 to 32767)
│   │   ├── i32 (-2147483648 to 2147483647) [默认]
│   │   ├── i64 (-9223372036854775808 to 9223372036854775807)
│   │   ├── i128
│   │   └── isize (指针大小)
│   │
│   └── 无符号
│       ├── u8  (0 to 255)
│       ├── u16 (0 to 65535)
│       ├── u32 (0 to 4294967295)
│       ├── u64 (0 to 18446744073709551615)
│       ├── u128
│       └── usize (指针大小)
│
├── 浮点
│   ├── f32 (IEEE-754单精度)
│   └── f64 (IEEE-754双精度) [默认]
│
├── 布尔
│   └── bool (true/false)
│
├── 字符
│   └── char (Unicode标量值, 4字节)
│
└── 单元类型
    └── () (类似void, 但占用0字节)
```

### 1.2 字面量表示

| 类型 | 字面量示例 |
| :--- | :--- |
| 十进制 | `98_222` |
| 十六进制 | `0xff` |
| 八进制 | `0o77` |
| 二进制 | `0b1111_0000` |
| 字节 | `b'A'` |
| 浮点 | `2.0`, `3.14e-2` |
| 字符 | `'a'`, `'\n'`, `'\u{2764}'` |

---

## 二、复合类型详解

### 2.1 struct

```text
struct
├── 命名字段结构体
│   └── struct Point { x: f64, y: f64 }
│
├── 元组结构体
│   └── struct Point(f64, f64)
│
└── 单元结构体
    └── struct AlwaysEqual; (无字段)
```

### 2.2 enum

```text
enum
├── 简单枚举
│   └── enum Color { Red, Green, Blue }
│
├── 携带数据
│   └── enum Message {
│           Quit,
│           Move { x: i32, y: i32 },
│           Write(String),
│           ChangeColor(i32, i32, i32),
│       }
│
└── 带判别值
    └── enum HttpStatus {
            OK = 200,
            NotFound = 404,
        }
```

### 2.3 集合类型

```text
集合类型
├── array: 固定长度，栈分配
│   └── let a: [i32; 5] = [1, 2, 3, 4, 5];
│
├── slice: 动态长度，引用视图
│   └── let s: &[i32] = &a[1..3];
│
└── tuple: 固定长度，异构
    └── let t: (i32, f64, &str) = (500, 6.4, "hi");
```

---

## 三、抽象类型详解

### 3.1 泛型

```text
泛型
├── 类型参数
│   └── struct Point<T> { x: T, y: T }
│
├── 多个参数
│   └── struct Point<T, U> { x: T, y: U }
│
├── 约束
│   └── fn largest<T: PartialOrd>(list: &[T]) -> T
│
└── 边界
    └── T: Display + Clone, U: Clone + Debug
```

### 3.2 Trait

```text
Trait
├── 接口定义
│   └── trait Summary {
│           fn summarize(&self) -> String;
│       }
│
├── 默认实现
│   └── trait Summary {
│           fn summarize(&self) -> String {
│               String::from("(Read more...)")
│           }
│       }
│
├── 实现
│   └── impl Summary for NewsArticle { ... }
│
├── Trait bound
│   └── pub fn notify<T: Summary>(item: &T)
│
├── 关联类型
│   └── trait Iterator { type Item; ... }
│
└── 对象安全
    └── trait ObjectSafe {
            fn method(&self);  // 对象安全
            // fn generic<T>(&self);  // 不对象安全
        }
```

### 3.3 impl Trait vs dyn Trait

```text
impl Trait vs dyn Trait
├── impl Trait (静态分发)
│   ├── 编译时确定具体类型
│   ├── 单态化生成代码
│   ├── 零运行时开销
│   └── 返回类型可用
│
└── dyn Trait (动态分发)
    ├── 运行时确定具体类型
    ├── 虚表查找
    ├── 运行时开销
    └── 必须用Box封装返回
```

---

## 四、型变(Variance)

```text
型变
├── 协变 (+)
│   ├── T <: U → C<T> <: C<U>
│   └── 示例: Box<T>, Vec<T>, Option<T>, &T
│
├── 逆变 (-)
│   ├── T <: U → C<U> <: C<T>
│   └── 示例: fn(T) (参数位置)
│
└── 不变 (=)
    ├── T = U → C<T> = C<U>
    └── 示例: &mut T, Cell<T>, RefCell<T>
```

**型变表**:

| 类型构造器 | 对T的型变 |
| :--- | :---: |
| `Box<T>` | + |
| `Vec<T>` | + |
| `Option<T>` | + |
| `&T` | + |
| `&mut T` | = |
| `fn(T) -> U` | - (T), + (U) |
| `Cell<T>` | = |
| `RefCell<T>` | = |

---

## 五、类型安全

### 5.1 类型安全保证

```text
类型安全
├── 进展性 (Progress)
│   └── 良类型表达式可以继续求值或已是值
│
├── 保持性 (Preservation)
│   └── 求值保持类型
│
└── 结果
    └── 良类型程序不会stuck（遇到类型错误）
```

### 5.2 类型推导

```text
类型推导
├── 显式标注
│   └── let x: i32 = 5;
│
├── 隐式推导
│   └── let x = 5;  // 推导为i32
│
└── 泛型推导
    └── let v = Vec::new();  // 根据使用推导
```

---

## 六、特殊类型

### 6.1  never类型 (!)

```text
never类型 (!)
├── 永不返回的函数
│   └── fn panic() -> ! { ... }
│
├── 可协变为任意类型
│   └── let x: i32 = panic();
│
└── 用于
    ├── panic!()
    ├── exit()
    └── 无限循环
```

### 6.2 PhantomData

```text
PhantomData<T>
├── 零大小类型
├── 告诉编译器"使用"了T
├── 影响生命周期推导
└── 示例:
    struct Slice<'a, T: 'a> {
        ptr: *const T,
        _marker: PhantomData<&'a T>,
    }
```

### 6.3 Sized与?Sized

```text
Sized trait
├── Sized (默认)
│   └── 编译时已知大小
│       ├── i32, f64, String
│       └── Vec<T>, Box<T>
│
└── ?Sized (动态大小类型DST)
    └── 编译时大小未知
        ├── str
        ├── [T]
        └── dyn Trait
```

---

## 七、类型关系

```text
类型关系
├── 子类型 (<:)
│   ├── 'static <: 'a
│   ├── 协变类型的子类型关系
│   └── 特征对象子类型
│
├── 相等 (=)
│   └── 类型完全相同
│
└── 强制转换 (as)
    ├── 数值类型转换
    └── 指针类型转换
```

---

## 八、与其他概念族的关系

```text
类型系统概念族
        │
        ├──→ 所有权概念族
        │       └── 类型系统基于所有权
        │
        ├──→ 生命周期概念族
        │       └── 类型包含生命周期信息
        │
        ├──→ 并发概念族
        │       └── Send/Sync是类型约束
        │
        └──→ 证明技术概念族
                └── 类型即证明，程序即证明项
```

---

## 九、学习路径

```text
学习类型系统
        │
        ├──→ 基础
        │       ├── 标量类型
        │       ├── 复合类型
        │       └── 泛型入门
        │
        ├──→ 进阶
        │       ├── Trait系统
        │       ├── 型变规则
        │       └── 生命周期
        │
        └──→ 专家
                ├── 类型推导算法
                ├── 类型安全证明
                └── 高级类型特性(GAT等)
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 类型系统概念族谱
