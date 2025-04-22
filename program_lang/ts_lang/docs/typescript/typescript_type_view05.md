# TypeScript深度分析

## 目录

- [TypeScript深度分析](#typescript深度分析)
  - [目录](#目录)
  - [变量类型与控制](#变量类型与控制)
    - [变量声明与作用域](#变量声明与作用域)
    - [类型系统](#类型系统)
      - [基础类型](#基础类型)
      - [对象类型](#对象类型)
      - [特殊类型](#特殊类型)
      - [类型操作](#类型操作)
    - [控制流语法](#控制流语法)
      - [条件语句](#条件语句)
      - [循环语句](#循环语句)
    - [语义与作用域](#语义与作用域)
      - [类型擦除](#类型擦除)
      - [静态与动态作用域](#静态与动态作用域)
  - [形式化验证视角](#形式化验证视角)
    - [控制流分析](#控制流分析)
      - [控制流图](#控制流图)
      - [类型守卫与控制流](#类型守卫与控制流)
    - [数据流分析](#数据流分析)
      - [活动变量分析](#活动变量分析)
      - [类型推断](#类型推断)
    - [执行流分析](#执行流分析)
      - [同步执行](#同步执行)
      - [异步执行](#异步执行)
    - [语义与形式化验证](#语义与形式化验证)
      - [操作语义](#操作语义)
      - [类型系统验证](#类型系统验证)
  - [思维导图](#思维导图)

## 变量类型与控制

### 变量声明与作用域

TypeScript支持三种变量声明方式：

- **var**：函数作用域或全局作用域，允许重复声明，存在变量提升
- **let**：块级作用域，允许更新但不允许重复声明，有暂时性死区(TDZ)
- **const**：块级作用域，声明时必须初始化，引用不可变（内容可变）

```typescript
// var示例（不推荐使用）
function varTest() {
  if (true) {
    var x = 10;
  }
  console.log(x); // 输出10，函数作用域
}

// let示例
function letTest() {
  if (true) {
    let y = 20;
  }
  // console.log(y); // 错误：y未定义，块级作用域
}

// const示例
const obj = { value: 1 };
// obj = {}; // 错误：不能重新赋值
obj.value = 2; // 可以：修改内部属性
```

### 类型系统

TypeScript是静态类型系统，在编译时进行类型检查。

#### 基础类型

```typescript
let str: string = "hello";
let num: number = 42;
let bool: boolean = true;
let u: undefined = undefined;
let n: null = null;
let sym: symbol = Symbol("id");
let big: bigint = 100n;
```

#### 对象类型

```typescript
// 数组
let arr: number[] = [1, 2, 3];
let arr2: Array<number> = [1, 2, 3];

// 元组
let tuple: [string, number] = ["hello", 42];

// 对象
let person: { name: string; age: number } = { name: "张三", age: 30 };

// 接口
interface Person {
  name: string;
  age: number;
  sayHello(): void;
}
```

#### 特殊类型

```typescript
// any：绕过类型检查
let any_value: any = 42;
any_value = "hello"; // 可以

// unknown：类型安全的any
let unk: unknown = 42;
// unk.toFixed(); // 错误：需先进行类型检查
if (typeof unk === 'number') {
  unk.toFixed(); // 可以
}

// void：无返回值
function log(msg: string): void {
  console.log(msg);
}

// never：永不返回
function error(msg: string): never {
  throw new Error(msg);
}
```

#### 类型操作

```typescript
// 联合类型
type StringOrNumber = string | number;

// 交叉类型
type Employee = Person & { employeeId: number };

// 泛型
function identity<T>(arg: T): T {
  return arg;
}

// 类型断言
let someValue: unknown = "this is a string";
let strLength: number = (someValue as string).length;
```

### 控制流语法

#### 条件语句

```typescript
// if语句
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
type Direction = "north" | "east" | "south" | "west";

function getDirectionCode(dir: Direction): number {
  switch (dir) {
    case "north": return 0;
    case "east": return 1;
    case "south": return 2;
    case "west": return 3;
    default:
      // 穷尽性检查
      const exhaustiveCheck: never = dir;
      return exhaustiveCheck;
  }
}
```

#### 循环语句

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
function factorial(n: number): number {
  let result = 1;
  while (n > 1) {
    result *= n--;
  }
  return result;
}
```

### 语义与作用域

#### 类型擦除

TypeScript的类型信息在编译到JavaScript后会被擦除：

```typescript
// TypeScript
function greet(name: string): string {
  return `Hello, ${name}`;
}

// 编译后的JavaScript
function greet(name) {
  return `Hello, ${name}`;
}
```

#### 静态与动态作用域

TypeScript使用静态作用域（词法作用域），变量的可见性由其在代码中的位置决定：

```typescript
let x = 10;

function outer() {
  let y = 20;
  function inner() {
    let z = 30;
    console.log(x, y, z); // 可访问x, y, z
  }
  inner();
}
```

## 形式化验证视角

### 控制流分析

控制流分析(CFA)研究程序执行路径，在TypeScript中体现为：

#### 控制流图

一种描述程序执行顺序的图形表示，由基本块和边组成。

```typescript
// 控制流分析示例
function absolute(x: number): number {
  if (x >= 0) { // 条件节点
    return x;   // 返回节点1
  } else {
    return -x;  // 返回节点2
  }
}
```

#### 类型守卫与控制流

TypeScript利用控制流分析进行类型缩小：

```typescript
function process(value: string | number) {
  if (typeof value === "string") {
    // 此处value被缩小为string类型
    console.log(value.toUpperCase());
  } else {
    // 此处value被缩小为number类型
    console.log(value.toFixed(2));
  }
}
```

### 数据流分析

数据流分析(DFA)跟踪程序中数据的流动和变化。

#### 活动变量分析

```typescript
function example(): void {
  let x = 5;       // x活跃
  let y;           // y不活跃
  
  console.log(x);  // x使用，之后不活跃
  
  y = 10;          // y赋值，变为活跃
  return;          // y未使用，不活跃
}
```

#### 类型推断

```typescript
// 基于初始值推断类型
let message = "hello"; // 推断为string
let value = 42;        // 推断为number

// 上下文类型推断
function process(callback: (x: number) => void) {
  callback(10);
}

process(x => {
  // x被推断为number
  console.log(x.toFixed());
});
```

### 执行流分析

#### 同步执行

```typescript
function sequential() {
  let a = 1;
  let b = 2;
  let c = a + b;
  return c;
}
```

#### 异步执行

```typescript
async function fetchData(): Promise<string> {
  console.log("开始获取数据");
  const response = await fetch("/api/data");
  const data = await response.text();
  console.log("数据获取完成");
  return data;
}
```

### 语义与形式化验证

#### 操作语义

描述程序如何以一步步的状态转换执行：

```typescript
// 形式化规则(概念性):
// Γ ⊢ e1: number    Γ ⊢ e2: number
// -------------------------------------- (T-ADD)
//          Γ ⊢ e1 + e2: number

// 实际TypeScript代码
function add(a: number, b: number): number {
  return a + b;
}
```

#### 类型系统验证

TypeScript的类型系统可视为轻量级形式化验证：

```typescript
// 类型注解作为规范
function divide(a: number, b: number): number {
  if (b === 0) {
    throw new Error("除数不能为零");
  }
  return a / b;
}

// 类型检查器验证这个规范
const result = divide(10, 2); // 类型检查通过
// const error = divide("10", 2); // 类型错误
```

## 思维导图

```text
TypeScript分析
├── 变量与类型
│   ├── 变量声明
│   │   ├── var (函数作用域，提升)
│   │   ├── let (块作用域，TDZ)
│   │   └── const (块作用域，不可重赋值)
│   ├── 类型系统
│   │   ├── 基础类型 (string, number, boolean, null, undefined, symbol, bigint)
│   │   ├── 对象类型 (object, array, tuple, interface)
│   │   ├── 特殊类型 (any, unknown, void, never)
│   │   └── 高级类型 (联合, 交叉, 条件, 映射)
│   └── 类型操作
│       ├── 类型注解
│       ├── 类型推断
│       ├── 类型断言
│       └── 类型保护
├── 控制流与语法
│   ├── 条件语句 (if/else, switch)
│   ├── 循环语句 (for, while, do-while)
│   ├── 跳转语句 (break, continue, return)
│   └── 异常处理 (try/catch/finally)
├── 语义与作用域
│   ├── 类型擦除
│   ├── 静态作用域
│   ├── 编译时 vs 运行时
│   └── 闭包
└── 形式化验证
    ├── 控制流分析
    │   ├── 控制流图
    │   ├── 路径敏感分析
    │   └── 到达性分析
    ├── 数据流分析
    │   ├── 类型推断
    │   ├── 活跃变量分析
    │   └── 污点分析
    ├── 执行流
    │   ├── 同步执行
    │   ├── 异步执行 (Promise, async/await)
    │   └── 并发模型
    └── 形式化证明
        ├── 类型系统规则
        ├── 类型安全性
        ├── 不变量
        └── 前后置条件
```
