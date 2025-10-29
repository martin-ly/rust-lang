# TypeScript深度分析

## 目录

- [TypeScript深度分析](#typescript深度分析)
  - [目录](#目录)
  - [1. 变量、类型、控制与语义](#1-变量类型控制与语义)
    - [1.1 变量](#11-变量)
      - [变量声明](#变量声明)
      - [作用域](#作用域)
    - [1.2 类型系统](#12-类型系统)
      - [基本类型](#基本类型)
      - [类型操作](#类型操作)
    - [1.3 控制流语法](#13-控制流语法)
      - [条件语句](#条件语句)
      - [循环语句](#循环语句)
      - [跳转语句和异常处理](#跳转语句和异常处理)
    - [1.4 语义与作用域](#14-语义与作用域)
      - [表达式求值](#表达式求值)
      - [语义](#语义)
    - [1.5 形式化证明](#15-形式化证明)
      - [形式化语法](#形式化语法)
      - [形式化类型系统](#形式化类型系统)
  - [2. 控制流、数据流与执行流](#2-控制流数据流与执行流)
    - [2.1 控制流分析](#21-控制流分析)
      - [控制流图(CFG)](#控制流图cfg)
      - [类型守卫与流敏感分析](#类型守卫与流敏感分析)
    - [2.2 数据流分析](#22-数据流分析)
      - [到达定义与活跃变量](#到达定义与活跃变量)
      - [TypeScript中的应用](#typescript中的应用)
    - [2.3 执行流分析](#23-执行流分析)
      - [同步执行与调用栈](#同步执行与调用栈)
      - [异步执行与事件循环](#异步执行与事件循环)
    - [2.4 形式化语义与验证](#24-形式化语义与验证)
      - [操作语义](#操作语义)
      - [指称语义](#指称语义)
      - [公理语义](#公理语义)
      - [TypeScript类型系统作为轻量级形式化方法](#typescript类型系统作为轻量级形式化方法)
  - [3. TypeScript转换JavaScript](#3-typescript转换javascript)
    - [3.1 转换机制](#31-转换机制)
    - [3.2 类型擦除](#32-类型擦除)
    - [3.3 双射性问题](#33-双射性问题)
  - [4. 思维导图](#4-思维导图)

## 1. 变量、类型、控制与语义

### 1.1 变量

#### 变量声明

TypeScript提供三种变量声明方式，具有不同的作用域规则：

```typescript
// let: 块级作用域
let count: number = 5;
count = 10; // 可以重新赋值

// const: 块级作用域，引用不可变
const message: string = "Hello";
// message = "World"; // 错误：常量不能重新赋值

// var: 函数作用域，有变量提升（不推荐）
var age: number = 30;
```

#### 作用域

变量的可访问性由其作用域决定：

- **静态作用域**（词法作用域）：TypeScript采用静态作用域，变量的作用域在代码编写时确定
- **块级作用域**：`let`和`const`引入的作用域，限定在`{}`内
- **函数作用域**：`var`声明的变量在整个函数内有效
- **全局作用域**：在所有函数和代码块之外声明的变量

形式化表示：

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

### 1.2 类型系统

#### 基本类型

- **原始类型**：`number`, `string`, `boolean`, `null`, `undefined`, `symbol`, `bigint`
- **对象类型**：对象字面量、数组、元组、函数类型、类实例等
- **特殊类型**：`any`（禁用类型检查）, `unknown`（类型安全的`any`）, `void`（无返回值）, `never`（永不返回）

```typescript
// 基本类型示例
let name: string = "张三";
let age: number = 30;
let isActive: boolean = true;
let id: null = null;
let job: undefined = undefined;
let uniqueSymbol: symbol = Symbol("唯一");
let largeNumber: bigint = 100n;

// 对象类型示例
let person: { name: string; age: number } = { name: "李四", age: 25 };
let scores: number[] = [90, 85, 92];
let role: [string, number] = ["管理员", 1]; // 元组
```

#### 类型操作

- **类型注解**：显式指定类型
- **类型推断**：编译器自动推断类型
- **联合类型**：`|`表示可能的多种类型
- **交叉类型**：`&`表示合并多种类型的成员
- **泛型**：`<T>`参数化类型
- **条件类型**：`T extends U ? X : Y`根据类型关系选择类型
- **映射类型**：基于现有类型创建新类型
- **结构化类型**：基于结构而非名称的类型兼容性

```typescript
// 联合类型
type ID = string | number;

// 交叉类型
type Employee = Person & { employeeId: string };

// 泛型
function identity<T>(arg: T): T {
    return arg;
}

// 条件类型
type NonNullable<T> = T extends null | undefined ? never : T;

// 映射类型
type Readonly<T> = { readonly [P in keyof T]: T[P] };
```

### 1.3 控制流语法

#### 条件语句

```typescript
// if-else
if (condition) {
    // 代码块
} else if (anotherCondition) {
    // 代码块
} else {
    // 代码块
}

// switch
switch (expression) {
    case value1:
        // 代码块
        break;
    case value2:
        // 代码块
        break;
    default:
        // 代码块
}

// 三元运算符
const result = condition ? valueIfTrue : valueIfFalse;
```

#### 循环语句

```typescript
// for循环
for (let i = 0; i < 5; i++) {
    console.log(i);
}

// for...of (遍历可迭代对象)
for (const item of items) {
    console.log(item);
}

// for...in (遍历对象属性)
for (const key in obj) {
    if (Object.prototype.hasOwnProperty.call(obj, key)) {
        console.log(`${key}: ${obj[key as keyof typeof obj]}`);
    }
}

// while循环
while (condition) {
    // 代码块
}

// do-while循环
do {
    // 代码块
} while (condition);
```

#### 跳转语句和异常处理

```typescript
// break和continue
while (true) {
    if (condition1) break;
    if (condition2) continue;
}

// return
function calculate(): number {
    return result;
}

// throw
throw new Error("发生错误");

// try-catch-finally
try {
    // 可能抛出异常的代码
} catch (error) {
    // 处理异常
} finally {
    // 始终执行的代码
}
```

### 1.4 语义与作用域

#### 表达式求值

表达式求值遵循运算符优先级、结合性和短路规则：

```typescript
let x = 5 + 3 * 2; // x等于11（乘法优先）
let y = (5 + 3) * 2; // y等于16（括号优先）

// 短路求值
let isValid = true;
let result = isValid && getValue(); // 如果isValid为false，getValue()不会被调用
```

#### 语义

- **静态语义**：编译时可确定的规则，主要是类型检查
- **动态语义**：运行时的行为
- **类型擦除**：TypeScript的类型注解在编译后被移除，不影响运行时行为

### 1.5 形式化证明

#### 形式化语法

使用上下文无关文法(CFG)描述TypeScript语法：

```math
Program → Statement*
Statement → VariableDeclaration | FunctionDeclaration | ...
VariableDeclaration → ("let" | "const" | "var") Identifier TypeAnnotation? Initializer?
TypeAnnotation → ":" Type
...
```

#### 形式化类型系统

类型判断规则形式化表示：

```math
Γ ⊢ e: T  // 在上下文Γ中，表达式e具有类型T

// 数字字面量规则
--------------------- (T-Number)
Γ ⊢ NumberLiteral : number

// 函数应用规则
Γ ⊢ e1: (T → U)    Γ ⊢ e2: T
-------------------------------- (T-App)
        Γ ⊢ e1(e2): U
```

## 2. 控制流、数据流与执行流

### 2.1 控制流分析

#### 控制流图(CFG)

CFG是表示程序可能执行路径的图：

```typescript
function example(x: number): number { // 入口
    let y: number;              // B1
    if (x > 0) {                // B1 → B2 (true), B1 → B3 (false)
        y = x * 2;              // B2
    } else {
        y = x + 1;              // B3
    }                           // B2 → B4, B3 → B4
    return y;                   // B4 → 出口
}
```

文本表示的CFG：

```math
 B1 (入口): let y; if (x > 0)
  | T  | F
  v    v
 B2: y = x * 2;  B3: y = x + 1;
  |    |
  v    v
 B4: return y; (出口)
```

#### 类型守卫与流敏感分析

TypeScript通过控制流分析实现类型守卫，在特定代码路径上缩小类型范围：

```typescript
function process(value: string | number) {
    // value类型: string | number
    if (typeof value === "string") {
        // 此处value类型被缩小为string
        console.log(value.toUpperCase());
    } else {
        // 此处value类型被缩小为number
        console.log(value.toFixed(2));
    }
    // value类型恢复为string | number
}
```

### 2.2 数据流分析

#### 到达定义与活跃变量

- **到达定义**：程序某点可能到达的变量赋值
- **活跃变量**：程序某点后可能被使用的变量

```typescript
function example(): void {
    let x = 5;       // x活跃
    let y;           // y不活跃
    
    console.log(x);  // x使用后不再活跃
    
    y = 10;          // y赋值，变为活跃
    return;          // 此处y未使用，不活跃
}
```

#### TypeScript中的应用

- **类型推断**：根据赋值和使用推断变量类型
- **空值分析**：跟踪变量是否可能为`null`或`undefined`
- **未初始化检查**：确保变量在使用前已初始化

```typescript
// 类型推断示例
let message = "你好"; // 推断为string
let value = 42;       // 推断为number

// 空值分析
function process(text: string | null) {
    if (text !== null) {
        // 此处text类型为string
        console.log(text.length);
    }
}
```

### 2.3 执行流分析

#### 同步执行与调用栈

JavaScript/TypeScript使用调用栈处理函数调用：

```typescript
function first() {
    console.log("第一");
    second();
    console.log("第一结束");
}

function second() {
    console.log("第二");
    third();
    console.log("第二结束");
}

function third() {
    console.log("第三");
}

// 调用栈: [] → [first] → [first, second] → [first, second, third] 
//      → [first, second] → [first] → []
first();
```

#### 异步执行与事件循环

JavaScript采用事件循环模型处理异步操作：

```typescript
console.log("开始"); // 1. 同步执行

setTimeout(() => {
    console.log("定时器回调"); // 5. 任务队列回调执行
}, 0);

Promise.resolve().then(() => {
    console.log("Promise回调1"); // 3. 微任务队列回调执行
}).then(() => {
    console.log("Promise回调2"); // 4. 微任务队列回调执行
});

console.log("结束"); // 2. 同步执行

// 输出顺序:
// 开始
// 结束
// Promise回调1
// Promise回调2
// 定时器回调
```

执行模型组成部分：

1. **调用栈**：执行同步代码
2. **Web/Node.js APIs**：处理异步操作
3. **任务队列**：存放`setTimeout`等回调
4. **微任务队列**：存放Promise回调，优先级高于任务队列
5. **事件循环**：协调整个过程

### 2.4 形式化语义与验证

#### 操作语义

描述程序如何通过状态转换执行：

```math
// 小步操作语义示例（表达式求值）
⟨1 + 2, σ⟩ → ⟨3, σ⟩
⟨x, σ⟩ → ⟨σ(x), σ⟩  // σ是状态，σ(x)表示x在状态σ中的值
```

#### 指称语义

将语言构造映射到数学对象：

```math
[[P]] : Env -> Store -> Store  // 命令式语言语句可能的语义
```

#### 公理语义

用逻辑断言描述程序效果：

```math
{P} C {Q}  // 霍尔三元组，P是前置条件，C是命令，Q是后置条件
```

#### TypeScript类型系统作为轻量级形式化方法

- **规范**：类型注解是一种规范，描述数据的预期结构
- **验证**：类型检查器根据类型规则验证代码
- **证明**：通过类型检查相当于部分正确性证明

```typescript
// 类型作为规范
function add(a: number, b: number): number {
    return a + b; // 编译器验证这满足类型规范
}
```

## 3. TypeScript转换JavaScript

### 3.1 转换机制

TypeScript编译器（tsc）将TypeScript代码转换为JavaScript：

```typescript
// TypeScript代码
function greet(name: string): string {
    return `你好，${name}！`;
}

// 编译后的JavaScript代码
function greet(name) {
    return "你好，" + name + "！";
}
```

### 3.2 类型擦除

类型信息在编译时被完全移除，运行时不存在类型检查：

```typescript
// TypeScript
interface User {
    id: number;
    name: string;
}

function processUser(user: User) {
    console.log(user.id, user.name);
}

// 编译后的JavaScript
function processUser(user) {
    console.log(user.id, user.name);
}
```

### 3.3 双射性问题

TypeScript到JavaScript的转换不是双射的：

- **原因1**：类型信息丢失，无法从JavaScript完全恢复原始类型
- **原因2**：同一TypeScript代码可以编译到不同目标（ES5/ES6/ESNext）

## 4. 思维导图

```text
TypeScript深度分析
├── 变量、类型与控制
│   ├── 变量
│   │   ├── 声明方式 (let, const, var)
│   │   ├── 作用域 (块级, 函数, 全局)
│   │   └── 静态作用域机制
│   ├── 类型系统
│   │   ├── 基本类型 (number, string, boolean等)
│   │   ├── 对象类型 (对象, 数组, 元组, 函数)
│   │   ├── 特殊类型 (any, unknown, void, never)
│   │   ├── 类型操作 (联合, 交叉, 泛型, 条件)
│   │   └── 结构化类型系统
│   ├── 控制流语法
│   │   ├── 条件语句 (if, switch)
│   │   ├── 循环语句 (for, while, do-while)
│   │   ├── 跳转语句 (break, continue, return)
│   │   └── 异常处理 (try/catch/finally)
│   └── 语义与形式化
│       ├── 表达式求值规则
│       ├── 类型检查语义
│       ├── 形式化类型系统
│       └── 类型安全性证明
├── 流分析与形式化验证
│   ├── 控制流分析
│   │   ├── 控制流图 (CFG)
│   │   ├── 类型守卫机制
│   │   └── 不可达代码检测
│   ├── 数据流分析
│   │   ├── 到达定义分析
│   │   ├── 活跃变量分析
│   │   ├── 类型推断机制
│   │   └── 空值安全分析
│   ├── 执行流分析
│   │   ├── 同步执行与调用栈
│   │   ├── 异步执行与事件循环
│   │   ├── Promise与async/await
│   │   └── 任务队列与微任务队列
│   └── 形式化验证
│       ├── 操作语义 (如何计算)
│       ├── 指称语义 (计算什么)
│       ├── 公理语义 (逻辑属性)
│       └── 类型系统作为轻量级形式化方法
└── TypeScript与JavaScript
    ├── 编译转换过程
    ├── 类型擦除机制
    ├── 非双射性质
    └── 运行时类型安全考量
```
