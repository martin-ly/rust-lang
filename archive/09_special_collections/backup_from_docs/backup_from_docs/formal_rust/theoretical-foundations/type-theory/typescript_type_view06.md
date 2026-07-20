# TypeScript深度分析

## 目录

- [1. 变量、类型、控制流与语义](#1-变量类型控制流与语义)
  - [1.1 变量](#11-变量)
  - [1.2 类型系统](#12-类型系统)
  - [1.3 控制流语法](#13-控制流语法)
  - [1.4 语义与作用域](#14-语义与作用域)
  - [1.5 形式化证明概念](#15-形式化证明概念)
- [2. 控制流、数据流与执行流形式化分析](#2-控制流数据流与执行流形式化分析)
  - [2.1 控制流分析](#21-控制流分析)
  - [2.2 数据流分析](#22-数据流分析)
  - [2.3 执行流分析](#23-执行流分析)
  - [2.4 语义与形式化验证](#24-语义与形式化验证)

## 1. 变量、类型、控制流与语义

### 1.1 变量

#### 1.1.1 变量声明方式

TypeScript提供三种变量声明方式，每种具有不同的作用域规则：

```typescript
// var: 函数作用域，存在变量提升
function varExample() {
  if (true) {
    var x = 10;
  }
  console.log(x); // 输出10，函数作用域可访问
}

// let: 块级作用域，存在暂时性死区(TDZ)
function letExample() {
  // console.log(y); // 错误：TDZ
  if (true) {
    let y = 20;
  }
  // console.log(y); // 错误：块级作用域外无法访问
}

// const: 块级作用域，借用不可变
const z = 30;
// z = 40; // 错误：不能重新赋值
const obj = { value: 1 };
obj.value = 2; // 可以：内部属性可变
```

#### 1.1.2 变量作用域形式化

作用域可以形式化定义为变量绑定与可见性的环境函数：

```math
Scope := { 
  bindings: Map<Identifier, Value>,
  parent: Option<Scope>
}

resolve(scope, id) := 
  if id ∈ scope.bindings then scope.bindings[id]
  else if scope.parent ≠ null then resolve(scope.parent, id)
  else undefined
```

静态作用域（词法作用域）是在代码编写时决定的，而非运行时：

```typescript
let x = 10;

function outer() {
  let y = 20;
  function inner() {
    let z = 30;
    console.log(x, y, z); // 可访问所有变量
  }
  inner();
}
```

### 1.2 类型系统

#### 1.2.1 静态类型特质

TypeScript使用静态类型系统，在编译时进行类型检查：

```typescript
// 类型注解
let name: string = "张三";
let age: number = 30;
let isActive: boolean = true;

// 类型推断
let inferred = "自动推断为string类型";
```

#### 1.2.2 基础与复合类型

```typescript
// 基础类型
let str: string = "hello";
let num: number = 42;
let bool: boolean = true;
let n: null = null;
let u: undefined = undefined;
let sym: symbol = Symbol("id");
let big: bigint = 100n;

// 数组与元组
let arr: number[] = [1, 2, 3];
let tuple: [string, number] = ["id", 100];

// 对象类型
interface Person {
  name: string;
  age: number;
  sayHello(): void;
}

// 函数类型
type MathFunc = (x: number, y: number) => number;
```

#### 1.2.3 高级类型特质

```typescript
// 联合类型
type StringOrNumber = string | number;

// 交叉类型
type Employee = Person & { employeeId: number };

// 泛型
function identity<T>(arg: T): T {
  return arg;
}

// 条件类型
type NonNullable<T> = T extends null | undefined ? never : T;

// 映射类型
type Readonly<T> = { readonly [P in keyof T]: T[P] };

// 字面量类型
type Direction = "north" | "east" | "south" | "west";
```

#### 1.2.4 类型系统形式化

类型系统可以形式化为类型判断规则：

```math
// 类型判断形式：Γ ⊢ e: T （在上下文Γ中，表达式e具有类型T）

// 变量规则
x: T ∈ Γ
---------
Γ ⊢ x: T

// 函数应用规则
Γ ⊢ f: (T1 → T2)    Γ ⊢ e: T1
-----------------------------
        Γ ⊢ f(e): T2
```

### 1.3 控制流语法

#### 1.3.1 条件语句

```typescript
// if-else语句
function checkValue(x: number): string {
  if (x > 0) {
    return "正数";
  } else if (x < 0) {
    return "负数";
  } else {
    return "零";
  }
}

// switch语句
type Status = "pending" | "success" | "error";

function handleStatus(status: Status): void {
  switch (status) {
    case "pending":
      console.log("处理中...");
      break;
    case "success":
      console.log("处理成功");
      break;
    case "error":
      console.log("处理失败");
      break;
  }
}
```

#### 1.3.2 循环语句

```typescript
// for循环
function sumArray(arr: number[]): number {
  let sum = 0;
  for (let i = 0; i < arr.length; i++) {
    sum += arr[i];
  }
  return sum;
}

// while循环
function countdown(n: number): void {
  while (n > 0) {
    console.log(n);
    n--;
  }
}

// for-of循环（迭代可迭代对象）
function processItems<T>(items: T[]): void {
  for (const item of items) {
    // 处理每个item
  }
}
```

### 1.4 语义与作用域

#### 1.4.1 类型擦除

TypeScript使用类型擦除机制，编译后的JavaScript不包含类型信息：

```typescript
// TypeScript代码
function greet(name: string): string {
  return `Hello, ${name}`;
}

// 编译后的JavaScript
function greet(name) {
  return `Hello, ${name}`;
}
```

#### 1.4.2 静态与动态作用域

TypeScript采用静态作用域（又称词法作用域）：

```typescript
let x = 10;

function foo() {
  console.log(x); // 借用外层作用域的x
}

function bar() {
  let x = 20;
  foo(); // 调用foo，输出10而非20
}

// 对比：如果是动态作用域，foo()将输出20
```

### 1.5 形式化证明概念

#### 1.5.1 类型安全性

类型安全性可以形式化表述为：

1. **进展性（Progress）**：任何类型良好的表达式要么是一个值，要么可以按照评估规则再进一步求值。
2. **类型保持（Preservation）**：如果一个类型良好的表达式求值为另一个表达式，那么结果表达式也是类型良好的。

```typescript
// 类型良好的表达式示例
let x: number = 1 + 2; // 静态检查通过，求值结果仍是number类型

// 类型错误示例（静态检查阶段报错）
// let y: string = 1 + 2; // 错误：不能将number类型赋值给string类型
```

#### 1.5.2 不变量与断言

程序验证中的不变量和断言：

```typescript
function binarySearch<T>(arr: T[], target: T): number {
  let left = 0;
  let right = arr.length - 1;
  
  // 循环不变量：如果target在数组中，则位于arr[left..right]区间
  while (left <= right) {
    const mid = Math.floor((left + right) / 2);
    if (arr[mid] === target) return mid;
    if (arr[mid] < target) left = mid + 1;
    else right = mid - 1;
  }
  
  return -1; // 未找到
}
```

## 2. 控制流、数据流与执行流形式化分析

### 2.1 控制流分析

#### 2.1.1 控制流图

控制流图(CFG)是一种图形化表示程序执行路径的方式：

```math
CFG := (V, E)
V := {基本块} // 顺序执行无分支的指令序列
E := {(v₁, v₂, c)} // 从v₁到v₂的边，可能带条件c
```

```typescript
// 示例函数及其控制流图表示（概念性）
function absolute(x: number): number {
  // 基本块1: 入口
  if (x >= 0) { 
    // 基本块2: x >= 0
    return x;
  } else {
    // 基本块3: x < 0
    return -x;
  }
  // 基本块4: 出口（不可达）
}

// CFG: 
// B1 --[x>=0]--> B2 --> B4
// B1 --[x<0]---> B3 --> B4
```

#### 2.1.2 类型守卫与控制流分析

TypeScript利用控制流分析实现类型守卫，缩小变量类型范围：

```typescript
function process(value: string | number) {
  // value类型：string | number
  
  if (typeof value === "string") {
    // 此分支中，value类型被缩小为string
    console.log(value.toUpperCase());
  } else {
    // 此分支中，value类型被缩小为number
    console.log(value.toFixed(2));
  }
  
  // value类型恢复为string | number
}
```

#### 2.1.3 可达性分析

控制流分析能够检测不可达代码：

```typescript
function unreachableExample(condition: boolean): number {
  if (condition) {
    return 1;
  } else {
    return 2;
  }
  
  // 编译器警告：不可达代码
  console.log("This is unreachable");
  return 3;
}
```

### 2.2 数据流分析

#### 2.2.1 定义-使用链

数据流分析追踪变量的定义和使用：

```typescript
function example(): void {
  let x = 5;       // x的定义
  let y;           // y的定义（未初始化）
  
  console.log(x);  // x的使用
  
  y = x + 1;       // y的定义，x的使用
  
  return;          // y未使用
}
```

形式化表示：

```math
定义(Def) := {(变量, 赋值点)}
使用(Use) := {(变量, 使用点)}
DefUseChain := {(def, use) | def ∈ Def, use ∈ Use, 且use使用def定义的值}
```

#### 2.2.2 类型推断系统

TypeScript的类型推断是数据流分析的应用：

```typescript
// 基于初始化值推断类型
let message = "TypeScript"; // 推断为string
let value = 42;             // 推断为number

// 基于使用方式推断类型
function processArray<T>(arr: T[]): T {
  return arr[0]; // 返回类型被推断为T
}

// 上下文类型推断
const numbers = [1, 2, 3]; // 推断为number[]
```

### 2.3 执行流分析

#### 2.3.1 同步执行模型

同步代码执行按顺序进行：

```typescript
function sequential(): number {
  const a = 1;       // 第1步
  const b = a + 1;   // 第2步
  const c = b * 2;   // 第3步
  return c;          // 第4步
}
```

#### 2.3.2 异步执行模型

异步执行使用Promise、async/await：

```typescript
// Promise链
function fetchAndProcess(url: string): Promise<string> {
  return fetch(url)                // 异步操作1
    .then(response => response.text()) // 异步操作2
    .then(text => processText(text))   // 异步操作3
    .catch(error => handleError(error)); // 错误处理
}

// async/await
async function fetchData(url: string): Promise<string> {
  try {
    const response = await fetch(url);        // 暂停执行直到Promise完成
    const text = await response.text();       // 暂停执行直到Promise完成
    return processText(text);                 // 返回Promise<string>
  } catch (error) {
    return handleError(error);
  }
}
```

异步执行流形式化表示：

```math
AsyncExecution := {
  task: Task,
  state: "pending" | "fulfilled" | "rejected",
  result: Option<Value>,
  error: Option<Error>,
  continuations: List<(Value) -> AsyncExecution>
}
```

### 2.4 语义与形式化验证

#### 2.4.1 操作语义

操作语义形式化描述程序执行步骤：

```math
// 小步操作语义示例（表达式求值）
⟨1 + 2, σ⟩ → ⟨3, σ⟩
⟨x, σ⟩ → ⟨σ(x), σ⟩  // 假设σ是状态，σ(x)表示x在状态σ中的值
```

#### 2.4.2 类型系统验证

TypeScript的类型系统是一种轻量级形式化验证：

```typescript
// 类型约束作为规范
function divide(a: number, b: number): number {
  // 类型系统可以验证a和b是number，但不验证b≠0
  return a / b;
}

// 更严格的类型
function safeDivide(a: number, b: NonZeroNumber): number {
  return a / b;
}
type NonZeroNumber = number & { __nonZero: never };
const asNonZero = (n: number): NonZeroNumber => {
  if (n === 0) throw new Error("除数不能为零");
  return n as NonZeroNumber;
};
```

## 思维导图

```text
TypeScript深度分析
├── 变量与类型系统
│   ├── 变量声明与作用域
│   │   ├── var（函数作用域，变量提升）
│   │   ├── let（块级作用域，TDZ）
│   │   ├── const（块级作用域，借用不可变）
│   │   └── 静态作用域（词法作用域）规则
│   ├── 基础类型系统
│   │   ├── 静态类型检查
│   │   ├── 基础类型（string, number, boolean, null, undefined等）
│   │   ├── 复合类型（数组, 对象, 函数, 元组等）
│   │   └── 特殊类型（any, unknown, never, void）
│   ├── 高级类型特质
│   │   ├── 联合类型（|）
│   │   ├── 交叉类型（&）
│   │   ├── 泛型（<T>）
│   │   ├── 条件类型（T extends U ? X : Y）
│   │   ├── 映射类型（{ [K in keyof T]: ... }）
│   │   └── 字面量类型（"value", 42, true）
│   └── 类型系统形式化
│       ├── 类型判断（Γ ⊢ e: T）
│       ├── 子类型关系（S <: T）
│       ├── 类型安全性（Progress & Preservation）
│       └── 类型擦除机制
├── 控制流与语法语义
│   ├── 条件语句
│   │   ├── if-else
│   │   ├── switch
│   │   ├── 三元运算符
│   │   └── 控制流类型分析
│   ├── 循环语句
│   │   ├── for
│   │   ├── while/do-while
│   │   ├── for...of/for...in
│   │   └── 迭代器模式
│   ├── 控制流结构
│   │   ├── 顺序执行
│   │   ├── 分支选择
│   │   ├── 循环结构
│   │   └── 异常处理（try/catch/finally）
│   └── 语义规则
│       ├── 静态语义（类型检查）
│       ├── 动态语义（运行时行为）
│       ├── 类型擦除的影响
│       └── 可靠性保证与限制
├── 控制流分析
│   ├── 控制流图（CFG）
│   │   ├── 基本块与边
│   │   ├── 入口与出口
│   │   └── 分支与合并点
│   ├── 类型守卫与流敏感类型
│   │   ├── typeof守卫
│   │   ├── instanceof守卫
│   │   ├── 属性检查守卫
│   │   └── 用户定义类型谓词
│   ├── 穷尽性检查
│   │   ├── switch分支完备性
│   │   ├── 联合类型处理完备性
│   │   └── never类型在穷尽检查中的应用
│   └── 可达性分析
│       ├── 不可达代码检测
│       ├── 控制流死区
│       └── 条件真值分析
├── 数据流分析
│   ├── 定义-使用链
│   │   ├── 变量定义点
│   │   ├── 变量使用点
│   │   └── 数据依赖图
│   ├── 类型推断系统
│   │   ├── 上下文类型推断
│   │   ├── 返回类型推断
│   │   ├── 泛型类型推断
│   │   └── 最佳通用类型算法
│   ├── 空值处理
│   │   ├── 严格空检查
│   │   ├── 可选链（?.）
│   │   └── 空值合并（??）
│   └── 别名分析
│       ├── 借用跟踪
│       ├── 副作用检测
│       └── 不可变性支持
└── 执行流与形式化验证
    ├── 执行流分析
    │   ├── 同步执行模型
    │   ├── 异步执行模型
    │   │   ├── Promise链
    │   │   ├── async/await
    │   │   └── 事件循环与任务队列
    │   ├── 调用图分析
    │   │   ├── 函数调用关系
    │   │   ├── 回调函数追踪
    │   │   └── 闭包数据流
    │   └── 异常流分析
    │       ├── 异常传播路径
    │       ├── 异常处理完整性
    │       └── 资源管理安全性
    └── 形式化语义与验证
        ├── 操作语义
        │   ├── 小步语义（单步执行规则）
        │   ├── 大步语义（整体执行结果）
        │   └── 状态转换系统
        ├── 类型系统验证
        │   ├── 类型规则形式化
        │   ├── 类型检查算法
        │   ├── 类型安全证明
        │   └── 验证限制（unsoundness）
        ├── 程序验证技术
        │   ├── 断言与前/后置条件
        │   ├── 循环不变量
        │   ├── 契约式编程
        │   └── 类型驱动设计
        └── 形式化工具支持
            ├── TypeScript编译器
            ├── ESLint静态分析
            ├── 类型约束优化
            └── 验证范围扩展方法
```
