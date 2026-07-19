# JavaScript编程语言分析

## 目录

- [JavaScript编程语言分析](#javascript编程语言分析)
  - [目录](#目录)
  - [1. 变量、类型、控制、语法与语义](#1-变量类型控制语法与语义)
    - [1.1 变量](#11-变量)
      - [概念定义](#概念定义)
      - [形式化表示](#形式化表示)
      - [作用域规则](#作用域规则)
      - [变量提升](#变量提升)
    - [1.2 类型](#12-类型)
      - [类型系统特性](#类型系统特性)
      - [基本类型分类](#基本类型分类)
      - [类型检查与转换](#类型检查与转换)
      - [类型强制转换](#类型强制转换)
    - [1.3 控制流](#13-控制流)
      - [条件控制](#条件控制)
      - [循环控制](#循环控制)
      - [跳转控制](#跳转控制)
    - [1.4 语法](#14-语法)
      - [词法规则](#词法规则)
      - [语法结构](#语法结构)
      - [ECMAScript标准](#ecmascript标准)
    - [1.5 语义](#15-语义)
      - [执行上下文](#执行上下文)
      - [词法环境](#词法环境)
      - [语义模型](#语义模型)
    - [1.6 形式化证明](#16-形式化证明)
      - [类型安全性](#类型安全性)
      - [程序逻辑](#程序逻辑)
      - [不变量与断言](#不变量与断言)
  - [2. 控制流、数据流、执行流与语义](#2-控制流数据流执行流与语义)
    - [2.1 控制流分析](#21-控制流分析)
      - [控制流图(CFG)](#控制流图cfg)
      - [分支与循环分析](#分支与循环分析)
      - [异常控制流](#异常控制流)
    - [2.2 数据流分析](#22-数据流分析)
      - [定义-使用分析](#定义-使用分析)
      - [活跃变量分析](#活跃变量分析)
      - [闭包数据流](#闭包数据流)
    - [2.3 执行流分析](#23-执行流分析)
      - [调用图(Call Graph)](#调用图call-graph)
      - [异步执行流](#异步执行流)
      - [事件循环与任务队列](#事件循环与任务队列)
    - [2.4 语义分析](#24-语义分析)
      - [操作语义(Operational Semantics)](#操作语义operational-semantics)
      - [指称语义(Denotational Semantics)](#指称语义denotational-semantics)
      - [ECMAScript规范语义](#ecmascript规范语义)
    - [2.5 形式化验证](#25-形式化验证)
      - [静态分析工具](#静态分析工具)
      - [程序证明与验证](#程序证明与验证)
      - [模型检测](#模型检测)
  - [3. 思维导图](#3-思维导图)
  - [4. JavaScript高级特性](#4-javascript高级特性)
    - [4.1 原型与继承](#41-原型与继承)
      - [原型链机制](#原型链机制)
      - [继承模式](#继承模式)
      - [ES6类语法](#es6类语法)
    - [4.2 闭包与高阶函数](#42-闭包与高阶函数)
      - [闭包概念与用途](#闭包概念与用途)
      - [高阶函数](#高阶函数)
      - [柯里化(Currying)](#柯里化currying)
    - [4.3 异步编程模型](#43-异步编程模型)
      - [回调函数](#回调函数)
      - [Promise](#promise)
      - [Async/Await](#asyncawait)
    - [4.4 模块化系统](#44-模块化系统)
      - [CommonJS](#commonjs)
      - [ES模块(ESM)](#es模块esm)
      - [动态导入](#动态导入)
  - [5. JavaScript引擎与运行时](#5-javascript引擎与运行时)
    - [5.1 V8引擎架构](#51-v8引擎架构)
      - [编译流程](#编译流程)
      - [优化技术](#优化技术)
      - [垃圾回收](#垃圾回收)
    - [5.2 事件循环详解](#52-事件循环详解)
      - [执行栈与任务队列](#执行栈与任务队列)
      - [宏任务与微任务](#宏任务与微任务)
      - [Node.js事件循环](#nodejs事件循环)
    - [5.3 内存管理与优化](#53-内存管理与优化)
      - [内存生命周期](#内存生命周期)
      - [内存泄漏](#内存泄漏)
      - [性能优化](#性能优化)
  - [6. 思维导图扩展](#6-思维导图扩展)
  - [7. JavaScript函数式编程](#7-javascript函数式编程)
    - [7.1 函数式编程范式](#71-函数式编程范式)
      - [基本概念](#基本概念)
      - [函数组合](#函数组合)
      - [函数式编程库](#函数式编程库)
    - [7.2 JavaScript设计模式](#72-javascript设计模式)
      - [创建型模式](#创建型模式)
      - [结构型模式](#结构型模式)
      - [行为型模式](#行为型模式)
    - [7.3 Web API与DOM操作](#73-web-api与dom操作)
      - [DOM操作基础](#dom操作基础)
      - [浏览器API](#浏览器api)
      - [异步DOM操作](#异步dom操作)
  - [8. JavaScript形式化验证与规范](#8-javascript形式化验证与规范)
    - [8.1 形式化规范](#81-形式化规范)
      - [ECMAScript规范](#ecmascript规范)
      - [形式化语言规范](#形式化语言规范)
      - [形式化验证工具](#形式化验证工具)
    - [8.2 静态分析与验证](#82-静态分析与验证)
      - [8.2.1 静态分析工具](#821-静态分析工具)
      - [类型检查与推断](#类型检查与推断)
      - [形式化验证技术](#形式化验证技术)
    - [8.3 运行时验证与断言](#83-运行时验证与断言)
      - [断言库](#断言库)
      - [运行时类型检查](#运行时类型检查)
      - [不变量与契约](#不变量与契约)
  - [9. 思维导图扩展](#9-思维导图扩展)
  - [10. 现代JavaScript生态系统](#10-现代javascript生态系统)
    - [10.1 前端框架与库](#101-前端框架与库)
      - [声明式UI框架](#声明式ui框架)
      - [状态管理](#状态管理)
      - [构建工具与打包器](#构建工具与打包器)
    - [10.2 服务端JavaScript](#102-服务端javascript)
      - [Node.js生态系统](#nodejs生态系统)
      - [数据库集成](#数据库集成)
      - [微服务与API网关](#微服务与api网关)
    - [10.3 测试与质量保证](#103-测试与质量保证)
      - [测试框架](#测试框架)
      - [代码质量工具](#代码质量工具)
      - [持续集成/持续部署(CI/CD)](#持续集成持续部署cicd)
  - [11. JavaScript元编程与高级特性](#11-javascript元编程与高级特性)
    - [11.1 元编程技术](#111-元编程技术)
      - [反射API](#反射api)
      - [代理(Proxy)](#代理proxy)
      - [Symbol与Symbol.for](#symbol与symbolfor)
    - [11.2 装饰器模式与类增强](#112-装饰器模式与类增强)
      - [装饰器语法(@)](#装饰器语法)
      - [混入(Mixins)](#混入mixins)
      - [元属性与扩展操作符](#元属性与扩展操作符)
    - [11.3 高级异步模式](#113-高级异步模式)
      - [可取消的Promise](#可取消的promise)
      - [Promise并发控制](#promise并发控制)
      - [异步迭代器与生成器](#异步迭代器与生成器)
  - [12. 思维导图扩展](#12-思维导图扩展)

## 1. 变量、类型、控制、语法与语义

### 1.1 变量

#### 概念定义

- **变量**：JavaScript中的变量是对值的引用，而非直接存储值的容器
- **声明方式**：使用`var`、`let`和`const`关键字声明
- **动态绑定**：变量可随时绑定到不同类型的值

#### 形式化表示

- 设V为变量标识符集合，O为对象集合
- 绑定关系bind: V → O，表示变量指向的值
- 赋值操作x = y定义为bind(x) = eval(y)

```javascript
let x = 10;       // x绑定到数值10
let y = x;        // y绑定到数值10
x = "hello";      // x重新绑定到字符串"hello"，y仍为10
```

#### 作用域规则

- **词法作用域**：代码中变量的可见性由它在源代码中的位置决定
- **作用域链**：当访问变量时，从最内层作用域开始查找，直到全局作用域
- **块级作用域**：`let`和`const`具有块级作用域
- **函数作用域**：`var`具有函数作用域

```javascript
let global = "全局";
function outer() {
    let outer_var = "外层";
    function inner() {
        let inner_var = "内层";
        console.log(inner_var, outer_var, global);
    }
    inner();
}
```

#### 变量提升

- **var提升**：`var`声明的变量会提升到作用域顶部，但初始化不会提升
- **函数提升**：函数声明会完整提升
- **let/const**：不提升，有"暂时性死区"(TDZ)

```javascript
console.log(x); // undefined（提升了声明）
var x = 5;

console.log(y); // ReferenceError（暂时性死区）
let y = 5;
```

### 1.2 类型

#### 类型系统特性

- **动态类型**：类型检查在运行时进行
- **弱类型**：允许隐式类型转换
- **原型继承**：对象通过原型链实现继承

#### 基本类型分类

- **原始类型**：`undefined`, `null`, `boolean`, `number`, `string`, `symbol`, `bigint`
- **引用类型**：`object`（包括`array`, `function`, `date`等）

#### 类型检查与转换

```javascript
// 类型检查
typeof 42;           // "number"
typeof "hello";      // "string"
typeof {};           // "object"
typeof null;         // "object"（历史遗留问题）
typeof function(){}; // "function"

// 类型转换
Number("42");       // 42
String(42);         // "42"
Boolean(42);        // true
```

#### 类型强制转换

```javascript
// 隐式转换
"5" + 3;     // "53" (数字转为字符串)
"5" - 3;     // 2 (字符串转为数字)
if ("hello") // true (字符串转为布尔值)
```

### 1.3 控制流

#### 条件控制

- **if-else语句**：根据条件执行不同代码块
- **switch语句**：根据多个可能的值执行不同代码块
- **三元运算符**：简洁的条件表达式

```javascript
// if-else
if (age < 18) {
    status = "未成年";
} else if (age < 65) {
    status = "成年";
} else {
    status = "老年";
}

// 三元运算符
let status = age < 18 ? "未成年" : "成年";
```

#### 循环控制

- **for循环**：使用计数器遍历
- **while/do-while循环**：根据条件循环
- **for...in循环**：遍历对象属性
- **for...of循环**：遍历可迭代对象元素

```javascript
// for循环
for (let i = 0; i < 10; i++) {
    console.log(i);
}

// for...of循环
for (const item of [1, 2, 3]) {
    console.log(item);
}
```

#### 跳转控制

- **break**：跳出循环
- **continue**：跳过当前循环迭代
- **return**：从函数返回值
- **throw/try/catch**：异常处理

```javascript
try {
    if (condition) throw new Error("出错了");
    // 正常处理
} catch (error) {
    // 错误处理
} finally {
    // 总是执行
}
```

### 1.4 语法

#### 词法规则

- **标识符**：变量名、函数名等，遵循规范的命名规则
- **关键字**：具有特殊含义的保留字
- **字面量**：直接表示值的语法形式

#### 语法结构

- **表达式**：产生值的代码片段
- **语句**：执行操作的代码片段
- **声明**：创建变量、函数等的代码片段

```javascript
// 表达式
5 + 3
x = 10
function() { return 42; }

// 语句
if (condition) { ... }
for (let i = 0; i < 10; i++) { ... }

// 声明
let x = 5;
function add(a, b) { return a + b; }
```

#### ECMAScript标准

- **语法规范**：使用上下文无关文法(CFG)形式定义
- **ECMA-262**：JavaScript的官方规范，使用BNF符号定义语法

### 1.5 语义

#### 执行上下文

- **全局执行上下文**：代码最外层的默认环境
- **函数执行上下文**：函数调用时创建的环境
- **eval执行上下文**：执行eval函数内代码的环境

#### 词法环境

- **环境记录**：存储变量与值的映射关系
- **外部环境引用**：指向外部词法环境，实现作用域链

#### 语义模型

- **小步操作语义**：描述每个基本操作的状态转换
- **大步操作语义**：直接描述整个表达式的求值结果

```javascript
// 可以用小步操作语义描述以下代码的执行过程
let x = 1;
function inc() { x = x + 1; }
inc();
console.log(x); // 2
```

### 1.6 形式化证明

#### 类型安全性

JavaScript作为动态弱类型语言，类型安全性有限，但可以通过TypeScript等工具增强类型安全：

```javascript
// TypeScript中的类型定义与检查
function add(a: number, b: number): number {
    return a + b;
}
```

#### 程序逻辑

可以使用霍尔逻辑(Hoare Logic)对JavaScript程序进行形式化推理：

```javascript
// 使用前条件、后条件对程序进行推理
// {x >= 0}
function sumToN(n) {
    let total = 0;
    let i = 1;
    while (i <= n) {
        total += i;
        i++;
    }
    return total;
}
// {result = n*(n+1)/2}
```

#### 不变量与断言

在JavaScript中可以使用断言函数验证不变量：

```javascript
function assert(condition, message) {
    if (!condition) {
        throw new Error(message || "断言失败");
    }
}

function binarySearch(arr, target) {
    let left = 0;
    let right = arr.length - 1;
    
    // 循环不变量：如果target存在于arr中，它一定在[left, right]范围内
    while (left <= right) {
        assert(left >= 0 && right < arr.length, "索引越界");
        
        let mid = Math.floor((left + right) / 2);
        if (arr[mid] === target) return mid;
        if (arr[mid] < target) left = mid + 1;
        else right = mid - 1;
    }
    
    return -1;
}
```

## 2. 控制流、数据流、执行流与语义

### 2.1 控制流分析

#### 控制流图(CFG)

- **定义**：表示程序执行路径的图结构，节点为基本块，边表示可能的执行路径
- **基本块**：没有分支的最大代码序列

```javascript
function max(a, b) {
    if (a > b) {  // 条件节点
        return a; // 基本块1
    } else {
        return b; // 基本块2
    }
}
```

#### 分支与循环分析

- **分支覆盖**：确保测试涵盖所有可能的分支
- **循环不变量**：循环中保持不变的条件

```javascript
// 分析不同循环类型的控制流
for (let i = 0; i < arr.length; i++) { /* 线性循环 */ }
while (node !== null) { node = node.next; } /* 依赖数据的循环 */
```

#### 异常控制流

- **try/catch/finally**：扰乱正常控制流的异常处理机制
- **异常传播**：未捕获的异常沿调用栈向上传播

```javascript
function process() {
    try {
        riskyOperation(); // 可能抛出异常
        return "成功";    // 如果抛出异常，不会执行到这里
    } catch (error) {
        return "失败";    // 捕获异常后执行
    } finally {
        cleanup();       // 无论是否抛出异常都会执行
    }
}
```

### 2.2 数据流分析

#### 定义-使用分析

- **变量定义**：变量被赋值
- **变量使用**：变量的值被读取
- **定义-使用链**：连接变量定义与使用的关系

```javascript
function process(data) {
    let total = 0;              // total定义
    for (let i = 0; i < data.length; i++) { // i定义
        total += data[i];       // total和i使用，total重定义
    }
    let average = data.length ? total / data.length : 0;
                               // total使用，average定义
    return average;            // average使用
}
```

#### 活跃变量分析

- **活跃变量**：在当前程序点之后会被使用的变量
- **活跃分析**：确定每个程序点上哪些变量是活跃的

```javascript
function example() {
    let x = 10;  // x活跃（后面被使用）
    let y = 20;  // y活跃
    let z = x + y; // x,y活跃，z活跃
    return z;    // z活跃
    // 此点后没有变量活跃
}
```

#### 闭包数据流

JavaScript闭包可以捕获并延长外部变量的生命周期：

```javascript
function createCounter() {
    let count = 0;  // count在返回的函数中仍然活跃
    return function() {
        return ++count;
    };
}

const counter = createCounter();
console.log(counter()); // 1
console.log(counter()); // 2
```

### 2.3 执行流分析

#### 调用图(Call Graph)

- **节点**：函数
- **边**：函数调用关系

```javascript
function main() {
    helper1();
    helper2();
}

function helper1() {
    utility();
}

function helper2() {
    utility();
}

function utility() {
    // ...
}

// 调用图：main -> helper1 -> utility, main -> helper2 -> utility
```

#### 异步执行流

JavaScript的异步编程模型基于事件循环：

```javascript
console.log("开始");

setTimeout(() => {
    console.log("定时器回调");
}, 0);

Promise.resolve().then(() => {
    console.log("Promise回调");
});

console.log("结束");

// 输出顺序：开始、结束、Promise回调、定时器回调
```

#### 事件循环与任务队列

- **宏任务**：`setTimeout`, `setInterval`, I/O操作等
- **微任务**：Promise回调，MutationObserver等
- **执行顺序**：当前宏任务 -> 所有微任务 -> 下一个宏任务

```javascript
// 事件循环示例
function eventLoopExample() {
    console.log(1);
    
    setTimeout(() => {
        console.log(2);
        Promise.resolve().then(() => console.log(3));
    }, 0);
    
    Promise.resolve().then(() => {
        console.log(4);
        setTimeout(() => console.log(5), 0);
    });
    
    console.log(6);
}

// 输出：1, 6, 4, 2, 3, 5
```

### 2.4 语义分析

#### 操作语义(Operational Semantics)

- **小步语义**：描述程序执行的每个原子步骤
- **大步语义**：直接描述表达式求值结果

```javascript
// 小步语义示例：表达式求值
1 + (2 * 3) -> 1 + 6 -> 7

// 大步语义示例：直接给出结果
⟦1 + (2 * 3)⟧ = 7
```

#### 指称语义(Denotational Semantics)

- **数学映射**：将程序构造映射为数学对象
- **组合性**：整体语义由部分语义组合而成

```javascript
// 函数指称语义
⟦function(x) { return x * x; }⟧ = λx.x²
```

#### ECMAScript规范语义

ECMAScript规范使用伪代码和算法步骤定义JavaScript语义：

```javascript
// ES规范中的数组map方法语义（简化）
Array.prototype.map = function(callback /*, thisArg*/) {
    var O = Object(this);
    var len = O.length >>> 0;
    var A = new Array(len);
    var k = 0;
    var mappedValue;
    
    // 可选的this参数
    var T = arguments.length > 1 ? arguments[1] : undefined;
    
    while (k < len) {
        if (k in O) {
            mappedValue = callback.call(T, O[k], k, O);
            A[k] = mappedValue;
        }
        k++;
    }
    
    return A;
};
```

### 2.5 形式化验证

#### 静态分析工具

JavaScript静态分析工具可以检测潜在问题：

- **ESLint**：代码风格和潜在问题
- **Flow**：类型检查
- **TypeScript**：类型系统和静态分析

```javascript
// TypeScript类型检查示例
function divide(a: number, b: number): number {
    if (b === 0) {
        throw new Error("除数不能为零");
    }
    return a / b;
}
```

#### 程序证明与验证

使用霍尔逻辑（Hoare Logic）可以推理JavaScript程序的正确性：

```javascript
// {precondition: n ≥ 0}
function factorial(n) {
    // 循环不变量：i ≤ n+1 且 result = (i-1)!
    let result = 1;
    let i = 1;
    
    while (i <= n) {
        // 循环前：result = (i-1)!
        result = result * i;
        // 循环后：result = i!
        i++;
        // 恢复循环不变量：i ≤ n+1 且 result = (i-1)!
    }
    
    return result;
}
// {postcondition: result = n!}
```

#### 模型检测

可以使用模型检测验证JavaScript程序的属性：

```javascript
// 简单状态机，验证不变量
class StateMachine {
    constructor() {
        this.state = 'initial';
        this.validTransitions = {
            'initial': ['processing'],
            'processing': ['success', 'error'],
            'success': [],
            'error': ['initial']
        };
    }
    
    transition(newState) {
        // 不变量：状态转换必须有效
        if (!this.validTransitions[this.state].includes(newState)) {
            throw new Error(`Invalid transition from ${this.state} to ${newState}`);
        }
        this.state = newState;
    }
}
```

## 3. 思维导图

```text
JavaScript编程语言分析
├── 1. 变量、类型、控制、语法与语义
│   ├── 1.1 变量
│   │   ├── 概念定义
│   │   │   ├── 变量是对值的引用
│   │   │   ├── 声明方式：var、let、const
│   │   │   └── 动态绑定
│   │   ├── 形式化表示
│   │   │   ├── 绑定关系
│   │   │   └── 赋值操作
│   │   ├── 作用域规则
│   │   │   ├── 词法作用域
│   │   │   ├── 作用域链
│   │   │   ├── 块级作用域
│   │   │   └── 函数作用域
│   │   └── 变量提升
│   │       ├── var提升
│   │       ├── 函数提升
│   │       └── let/const不提升(TDZ)
│   ├── 1.2 类型
│   │   ├── 类型系统特性
│   │   │   ├── 动态类型
│   │   │   ├── 弱类型
│   │   │   └── 原型继承
│   │   ├── 基本类型分类
│   │   │   ├── 原始类型
│   │   │   └── 引用类型
│   │   ├── 类型检查与转换
│   │   └── 类型强制转换
│   ├── 1.3 控制流
│   │   ├── 条件控制
│   │   │   ├── if-else语句
│   │   │   ├── switch语句
│   │   │   └── 三元运算符
│   │   ├── 循环控制
│   │   │   ├── for循环
│   │   │   ├── while/do-while循环
│   │   │   ├── for...in循环
│   │   │   └── for...of循环
│   │   └── 跳转控制
│   │       ├── break
│   │       ├── continue
│   │       ├── return
│   │       └── throw/try/catch
│   ├── 1.4 语法
│   │   ├── 词法规则
│   │   │   ├── 标识符
│   │   │   ├── 关键字
│   │   │   └── 字面量
│   │   ├── 语法结构
│   │   │   ├── 表达式
│   │   │   ├── 语句
│   │   │   └── 声明
│   │   └── ECMAScript标准
│   ├── 1.5 语义
│   │   ├── 执行上下文
│   │   │   ├── 全局执行上下文
│   │   │   ├── 函数执行上下文
│   │   │   └── eval执行上下文
│   │   ├── 词法环境
│   │   │   ├── 环境记录
│   │   │   └── 外部环境引用
│   │   └── 语义模型
│   │       ├── 小步操作语义
│   │       └── 大步操作语义
│   └── 1.6 形式化证明
│       ├── 类型安全性
│       ├── 程序逻辑
│       └── 不变量与断言
├── 2. 控制流、数据流、执行流与语义
│   ├── 2.1 控制流分析
│   │   ├── 控制流图(CFG)
│   │   │   ├── 基本块
│   │   │   └── 控制依赖
│   │   ├── 分支与循环分析
│   │   │   ├── 分支覆盖
│   │   │   └── 循环不变量
│   │   └── 异常控制流
│   │       ├── try/catch/finally
│   │       └── 异常传播
│   ├── 2.2 数据流分析
│   │   ├── 定义-使用分析
│   │   │   ├── 变量定义
│   │   │   ├── 变量使用
│   │   │   └── 定义-使用链
│   │   ├── 活跃变量分析
│   │   │   ├── 活跃变量定义
│   │   │   └── 活跃性优化
│   │   └── 闭包数据流
│   │       ├── 捕获变量
│   │       └── 延长生命周期
│   ├── 2.3 执行流分析
│   │   ├── 调用图(Call Graph)
│   │   │   ├── 函数调用关系
│   │   │   └── 动态调用
│   │   ├── 异步执行流
│   │   │   ├── 回调函数
│   │   │   ├── Promise
│   │   │   └── async/await
│   │   └── 事件循环与任务队列
│   │       ├── 宏任务
│   │       ├── 微任务
│   │       └── 执行顺序
│   ├── 2.4 语义分析
│   │   ├── 操作语义(Operational Semantics)
│   │   │   ├── 小步语义
│   │   │   └── 大步语义
│   │   ├── 指称语义(Denotational Semantics)
│   │   │   ├── 数学映射
│   │   │   └── 组合性
│   │   └── ECMAScript规范语义
│   │       ├── 伪代码定义
│   │       └── 算法步骤
│   └── 2.5 形式化验证
│       ├── 静态分析工具
│       │   ├── ESLint
│       │   ├── Flow
│       │   └── TypeScript
│       ├── 程序证明与验证
│       │   ├── 霍尔逻辑
│       │   ├── 前置条件与后置条件
│       │   └── 循环不变量
│       └── 模型检测
│           ├── 状态转换系统
│           ├── 属性规范
│           └── 反例生成
```

## 4. JavaScript高级特性

### 4.1 原型与继承

#### 原型链机制

- **原型对象**：每个JavaScript对象都有一个原型对象（`__proto__`）
- **原型链**：通过`__proto__`链接形成的对象层次结构
- **属性查找**：当访问对象属性时，如果对象本身没有该属性，会沿原型链向上查找

```javascript
// 原型链示例
function Animal(name) {
    this.name = name;
}

Animal.prototype.speak = function() {
    return `${this.name}发出声音`;
};

function Dog(name, breed) {
    Animal.call(this, name);
    this.breed = breed;
}

// 设置继承关系
Dog.prototype = Object.create(Animal.prototype);
Dog.prototype.constructor = Dog;

// 添加子类特有方法
Dog.prototype.bark = function() {
    return `${this.name}汪汪叫`;
};

const dog = new Dog("小黑", "拉布拉多");
console.log(dog.speak()); // "小黑发出声音"
console.log(dog.bark());  // "小黑汪汪叫"
```

#### 继承模式

- **原型继承**：通过原型链实现继承
- **构造函数继承**：使用`call`/`apply`继承构造函数属性
- **组合继承**：结合原型继承和构造函数继承
- **寄生组合继承**：优化组合继承，避免重复调用父类构造函数

#### ES6类语法

```javascript
// ES6类语法实现继承
class Animal {
    constructor(name) {
        this.name = name;
    }
    
    speak() {
        return `${this.name}发出声音`;
    }
}

class Dog extends Animal {
    constructor(name, breed) {
        super(name);
        this.breed = breed;
    }
    
    bark() {
        return `${this.name}汪汪叫`;
    }
}

const dog = new Dog("小黑", "拉布拉多");
```

### 4.2 闭包与高阶函数

#### 闭包概念与用途

- **定义**：函数及其引用的外部词法环境的组合
- **特性**：可以访问创建它的函数作用域中的变量
- **应用**：数据封装、模块化、柯里化等

```javascript
// 闭包实现私有变量
function createCounter() {
    let count = 0;  // 私有变量
    
    return {
        increment() {
            return ++count;
        },
        decrement() {
            return --count;
        },
        getValue() {
            return count;
        }
    };
}

const counter = createCounter();
console.log(counter.increment()); // 1
console.log(counter.getValue());  // 1
console.log(counter.increment()); // 2
```

#### 高阶函数

- **定义**：接收函数作为参数或返回函数的函数
- **常用高阶函数**：`map`, `filter`, `reduce`, `forEach`等
- **函数式编程**：使用高阶函数进行函数组合

```javascript
// 函数组合
const compose = (...fns) => x => fns.reduceRight((y, f) => f(y), x);

const addOne = x => x + 1;
const double = x => x * 2;
const square = x => x * x;

const compute = compose(square, double, addOne);
console.log(compute(3)); // ((3+1)*2)² = 64
```

#### 柯里化(Currying)

- **定义**：将接受多个参数的函数转换为一系列接受单个参数的函数
- **应用**：参数复用、延迟计算、函数组合优化

```javascript
// 柯里化函数实现
function curry(fn) {
    return function curried(...args) {
        if (args.length >= fn.length) {
            return fn.apply(this, args);
        } else {
            return function(...args2) {
                return curried.apply(this, args.concat(args2));
            };
        }
    };
}

// 应用示例
function add(a, b, c) {
    return a + b + c;
}

const curriedAdd = curry(add);
console.log(curriedAdd(1)(2)(3)); // 6
console.log(curriedAdd(1, 2)(3)); // 6
console.log(curriedAdd(1)(2, 3)); // 6
```

### 4.3 异步编程模型

#### 回调函数

- **定义**：传递给另一个函数的函数，在特定事件发生时被调用
- **回调地狱**：嵌套过深的回调函数导致代码难以维护
- **错误处理**：通常采用错误优先回调模式

```javascript
// 回调示例
function fetchData(url, callback) {
    // 模拟异步请求
    setTimeout(() => {
        if (url) {
            callback(null, { data: "成功获取数据" });
        } else {
            callback(new Error("URL无效"), null);
        }
    }, 1000);
}

fetchData("https://example.com/api", (error, data) => {
    if (error) {
        console.error("出错:", error);
    } else {
        console.log("数据:", data);
    }
});
```

#### Promise

- **定义**：表示异步操作最终完成或失败的对象
- **状态**：`pending`（进行中）、`fulfilled`（已成功）、`rejected`（已失败）
- **链式调用**：通过`.then()`和`.catch()`处理结果和错误

```javascript
// Promise示例
function fetchData(url) {
    return new Promise((resolve, reject) => {
        // 模拟异步请求
        setTimeout(() => {
            if (url) {
                resolve({ data: "成功获取数据" });
            } else {
                reject(new Error("URL无效"));
            }
        }, 1000);
    });
}

fetchData("https://example.com/api")
    .then(data => {
        console.log("数据:", data);
        return fetchData("https://example.com/api2");
    })
    .then(data2 => {
        console.log("数据2:", data2);
    })
    .catch(error => {
        console.error("出错:", error);
    })
    .finally(() => {
        console.log("请求完成");
    });
```

#### Async/Await

- **定义**：基于Promise的语法糖，使异步代码更易于编写和阅读
- **async函数**：返回Promise对象的函数
- **await表达式**：暂停async函数执行，等待Promise解决

```javascript
// Async/Await示例
async function fetchAllData() {
    try {
        const data1 = await fetchData("https://example.com/api1");
        console.log("数据1:", data1);
        
        const data2 = await fetchData("https://example.com/api2");
        console.log("数据2:", data2);
        
        return { data1, data2 };
    } catch (error) {
        console.error("出错:", error);
        throw error;
    } finally {
        console.log("请求完成");
    }
}

// 调用异步函数
fetchAllData().then(result => {
    console.log("最终结果:", result);
});
```

### 4.4 模块化系统

#### CommonJS

- **定义**：Node.js采用的模块系统，使用`require()`和`module.exports`
- **特点**：同步加载，服务器端优先
- **实现**：每个模块都有自己的作用域，通过闭包实现变量隔离

```javascript
// math.js
function add(a, b) {
    return a + b;
}

function subtract(a, b) {
    return a - b;
}

module.exports = {
    add,
    subtract
};

// app.js
const math = require('./math');
console.log(math.add(5, 3)); // 8
```

#### ES模块(ESM)

- **定义**：ES6标准的官方模块系统，使用`import`和`export`
- **特点**：静态分析，支持树摇(tree-shaking)，异步加载
- **实现**：编译时确定模块依赖关系

```javascript
// math.js
export function add(a, b) {
    return a + b;
}

export function subtract(a, b) {
    return a - b;
}

// app.js
import { add, subtract } from './math.js';
console.log(add(5, 3)); // 8
```

#### 动态导入

- **定义**：在运行时按需导入模块的机制
- **语法**：`import()`函数返回Promise
- **应用**：代码分割，懒加载

```javascript
// 动态导入示例
button.addEventListener('click', async () => {
    try {
        const module = await import('./features.js');
        module.initFeature();
    } catch (error) {
        console.error("模块加载失败:", error);
    }
});
```

## 5. JavaScript引擎与运行时

### 5.1 V8引擎架构

#### 编译流程

- **解析(Parsing)**：源代码解析为抽象语法树(AST)
- **解释(Interpretation)**：Ignition解释器将AST转换为字节码并执行
- **编译(Compilation)**：TurboFan优化编译器将热点代码编译为机器码

#### 优化技术

- **内联缓存(Inline Caching)**：缓存对象属性访问路径
- **隐藏类(Hidden Classes)**：优化对象属性访问
- **即时编译(JIT)**：运行时将热点代码编译为机器码

#### 垃圾回收

- **分代收集**：分为新生代和老生代，使用不同算法
- **标记-清除(Mark-Sweep)**：标记所有可达对象，清除未标记对象
- **标记-整理(Mark-Compact)**：标记后整理内存，减少碎片化

```javascript
// 垃圾回收示例
function createObjects() {
    let array = [];
    for (let i = 0; i < 1000; i++) {
        array.push({ id: i, data: new Array(1000).fill(i) });
    }
    return array[0]; // 只返回一个对象，其余999个成为垃圾
}

let obj = createObjects(); // 函数返回后，未引用的对象将被回收
```

### 5.2 事件循环详解

#### 执行栈与任务队列

- **执行栈(Call Stack)**：函数调用形成的栈，遵循后进先出(LIFO)原则
- **任务队列(Task Queue)**：待执行的回调函数队列
- **事件循环(Event Loop)**：不断检查执行栈是否为空，若为空则从任务队列取出回调并执行

#### 宏任务与微任务

- **宏任务(Macrotask)**：`setTimeout`, `setInterval`, I/O, UI渲染等
- **微任务(Microtask)**：`Promise.then/catch/finally`, `queueMicrotask()`, MutationObserver等
- **执行顺序**：执行当前宏任务 -> 清空微任务队列 -> 执行下一个宏任务

```javascript
// 复杂事件循环示例
console.log('1 - 同步代码开始');

setTimeout(() => {
    console.log('2 - 第一个宏任务');
    Promise.resolve().then(() => {
        console.log('3 - 第一个宏任务中的微任务');
    });
}, 0);

Promise.resolve().then(() => {
    console.log('4 - 第一个微任务');
    setTimeout(() => {
        console.log('5 - 微任务中的宏任务');
    }, 0);
});

Promise.resolve().then(() => {
    console.log('6 - 第二个微任务');
});

console.log('7 - 同步代码结束');

// 输出顺序：1, 7, 4, 6, 2, 3, 5
```

#### Node.js事件循环

- **阶段**：定时器 -> 待处理回调 -> 空转 -> 准备 -> 轮询 -> 检查 -> 关闭事件回调
- **特点**：每个阶段结束后执行微任务
- **与浏览器区别**：阶段更细致，多了I/O相关阶段

### 5.3 内存管理与优化

#### 内存生命周期

- **分配**：声明变量，创建对象时分配内存
- **使用**：读写内存，访问对象属性等
- **释放**：垃圾回收器自动回收不再使用的内存

#### 内存泄漏

- **常见原因**：全局变量、闭包、事件监听器未移除、循环引用等
- **识别方法**：Chrome DevTools内存分析器、堆快照比较
- **优化策略**：及时清理引用，使用WeakMap/WeakSet，避免不必要的闭包

```javascript
// 内存泄漏示例
function createLeakingClosure() {
    const largeData = new Array(1000000).fill('x');
    return function leakingClosure() {
        // 引用了外部的largeData，即使不使用也会保持在内存中
        console.log('闭包被调用');
    };
}

// 解决方法：重构为不捕获不需要的变量
function createOptimizedClosure() {
    const largeData = new Array(1000000).fill('x');
    const processed = largeData.length; // 只保留需要的值
    largeData = null; // 允许大数组被回收
    
    return function optimizedClosure() {
        console.log(`处理了${processed}个项目`);
    };
}
```

#### 性能优化

- **减少DOM操作**：DOM操作代价高昂，应批量进行
- **避免频繁创建对象**：使用对象池、原型链共享方法
- **防抖与节流**：限制函数调用频率

```javascript
// 防抖函数
function debounce(func, wait) {
    let timeout;
    return function(...args) {
        clearTimeout(timeout);
        timeout = setTimeout(() => {
            func.apply(this, args);
        }, wait);
    };
}

// 节流函数
function throttle(func, limit) {
    let lastFunc;
    let lastRan;
    return function(...args) {
        if (!lastRan) {
            func.apply(this, args);
            lastRan = Date.now();
        } else {
            clearTimeout(lastFunc);
            lastFunc = setTimeout(() => {
                if ((Date.now() - lastRan) >= limit) {
                    func.apply(this, args);
                    lastRan = Date.now();
                }
            }, limit - (Date.now() - lastRan));
        }
    };
}

// 应用示例
window.addEventListener('resize', debounce(() => {
    console.log('窗口大小改变！');
}, 300));
```

## 6. 思维导图扩展

```text
JavaScript高级特性与运行机制
├── 4. JavaScript高级特性
│   ├── 4.1 原型与继承
│   │   ├── 原型链机制
│   │   │   ├── 原型对象
│   │   │   ├── 原型链
│   │   │   └── 属性查找
│   │   ├── 继承模式
│   │   │   ├── 原型继承
│   │   │   ├── 构造函数继承
│   │   │   ├── 组合继承
│   │   │   └── 寄生组合继承
│   │   └── ES6类语法
│   │       ├── class声明
│   │       ├── extends继承
│   │       └── super关键字
│   ├── 4.2 闭包与高阶函数
│   │   ├── 闭包概念与用途
│   │   │   ├── 定义
│   │   │   ├── 特性
│   │   │   └── 应用
│   │   ├── 高阶函数
│   │   │   ├── 定义
│   │   │   ├── 常用高阶函数
│   │   │   └── 函数式编程
│   │   └── 柯里化(Currying)
│   │       ├── 定义
│   │       ├── 实现
│   │       └── 应用
│   ├── 4.3 异步编程模型
│   │   ├── 回调函数
│   │   │   ├── 定义
│   │   │   ├── 回调地狱
│   │   │   └── 错误处理
│   │   ├── Promise
│   │   │   ├── 定义
│   │   │   ├── 状态
│   │   │   └── 链式调用
│   │   └── Async/Await
│   │       ├── async函数
│   │       ├── await表达式
│   │       └── 错误处理
│   └── 4.4 模块化系统
│       ├── CommonJS
│       │   ├── require/exports
│       │   ├── 同步加载
│       │   └── Node.js环境
│       ├── ES模块(ESM)
│       │   ├── import/export
│       │   ├── 静态分析
│       │   └── 树摇(tree-shaking)
│       └── 动态导入
│           ├── import()函数
│           ├── 代码分割
│           └── 懒加载
├── 5. JavaScript引擎与运行时
│   ├── 5.1 V8引擎架构
│   │   ├── 编译流程
│   │   │   ├── 解析(Parsing)
│   │   │   ├── 解释(Interpretation)
│   │   │   └── 编译(Compilation)
│   │   ├── 优化技术
│   │   │   ├── 内联缓存
│   │   │   ├── 隐藏类
│   │   │   └── 即时编译(JIT)
│   │   └── 垃圾回收
│   │       ├── 分代收集
│   │       ├── 标记-清除
│   │       └── 标记-整理
│   ├── 5.2 事件循环详解
│   │   ├── 执行栈与任务队列
│   │   │   ├── 执行栈(Call Stack)
│   │   │   ├── 任务队列(Task Queue)
│   │   │   └── 事件循环(Event Loop)
│   │   ├── 宏任务与微任务
│   │   │   ├── 宏任务(Macrotask)
│   │   │   ├── 微任务(Microtask)
│   │   │   └── 执行顺序
│   │   └── Node.js事件循环
│   │       ├── 事件循环阶段
│   │       ├── 阶段特点
│   │       └── 与浏览器区别
│   └── 5.3 内存管理与优化
│       ├── 内存生命周期
│       │   ├── 分配
│       │   ├── 使用
│       │   └── 释放
│       ├── 内存泄漏
│       │   ├── 常见原因
│       │   ├── 识别方法
│       │   └── 优化策略
│       └── 性能优化
│           ├── DOM操作优化
│           ├── 对象创建优化
│           └── 防抖与节流
```

## 7. JavaScript函数式编程

### 7.1 函数式编程范式

#### 基本概念

- **纯函数**：相同输入总是产生相同输出，无副作用
- **不可变性**：数据创建后不可修改，修改时返回新数据
- **高阶函数**：接受函数作为参数或返回函数的函数
- **声明式编程**：描述要做什么，而非如何做

```javascript
// 纯函数示例
function add(a, b) {
    return a + b; // 相同输入总是返回相同结果，无副作用
}

// 非纯函数
function addWithSideEffect(a, b) {
    console.log(`Adding ${a} and ${b}`); // 副作用：I/O操作
    return a + b;
}
```

#### 函数组合

- **组合(compose)**：将多个函数组合成一个函数，从右向左应用
- **管道(pipe)**：将多个函数组合成一个函数，从左向右应用
- **点自由(point-free)风格**：不直接引用函数参数的编程风格

```javascript
// 函数组合
const compose = (...fns) => x => fns.reduceRight((y, f) => f(y), x);
const pipe = (...fns) => x => fns.reduce((y, f) => f(y), x);

// 点自由风格示例
const add = a => b => a + b;
const multiply = a => b => a * b;
const subtract = a => b => b - a;

// 使用pipe创建计算流水线：((x + 2) * 3) - 5
const calculate = pipe(
    add(2),
    multiply(3),
    subtract(5)
);

console.log(calculate(10)); // ((10 + 2) * 3) - 5 = 31
```

#### 函数式编程库

- **Ramda**：专为函数式编程设计的库，支持自动柯里化和函数组合
- **Lodash/FP**：Lodash的函数式编程变体
- **Immutable.js**：提供不可变数据结构的库

```javascript
// 使用Ramda的示例
const R = require('ramda');

const users = [
    { name: '张三', age: 25, active: true },
    { name: '李四', age: 30, active: false },
    { name: '王五', age: 28, active: true }
];

// 找出所有活跃用户的名字
const getActiveUserNames = R.pipe(
    R.filter(R.prop('active')),
    R.map(R.prop('name')),
    R.join(', ')
);

console.log(getActiveUserNames(users)); // "张三, 王五"
```

### 7.2 JavaScript设计模式

#### 创建型模式

- **单例模式**：确保一个类只有一个实例
- **工厂模式**：创建对象的接口，让子类决定实例化哪个类
- **构建者模式**：分步创建复杂对象

```javascript
// 单例模式
const Singleton = (function() {
    let instance;
    
    function createInstance() {
        return {
            data: "单例数据",
            method() { return this.data; }
        };
    }
    
    return {
        getInstance: function() {
            if (!instance) {
                instance = createInstance();
            }
            return instance;
        }
    };
})();

const instance1 = Singleton.getInstance();
const instance2 = Singleton.getInstance();
console.log(instance1 === instance2); // true
```

#### 结构型模式

- **适配器模式**：使接口不兼容的类能一起工作
- **装饰器模式**：动态地给对象添加额外的责任
- **代理模式**：控制对另一个对象的访问

```javascript
// 装饰器模式
function Car() {
    this.cost = function() {
        return 20000;
    };
}

// 装饰器：添加GPS
function carWithGPS(car) {
    const originalCost = car.cost();
    car.cost = function() {
        return originalCost + 1000;
    };
    car.hasGPS = true;
}

// 装饰器：添加豪华座椅
function carWithLuxurySeats(car) {
    const originalCost = car.cost();
    car.cost = function() {
        return originalCost + 2000;
    };
    car.hasLuxurySeats = true;
}

const myCar = new Car();
console.log("基本车型价格:", myCar.cost()); // 20000

carWithGPS(myCar);
console.log("带GPS车型价格:", myCar.cost()); // 21000

carWithLuxurySeats(myCar);
console.log("带GPS和豪华座椅车型价格:", myCar.cost()); // 23000
```

#### 行为型模式

- **观察者模式**：定义对象间一对多的依赖关系
- **策略模式**：定义一系列算法，使它们可以互相替换
- **迭代器模式**：提供顺序访问集合元素的方法

```javascript
// 观察者模式
class Subject {
    constructor() {
        this.observers = [];
    }
    
    subscribe(observer) {
        this.observers.push(observer);
    }
    
    unsubscribe(observer) {
        this.observers = this.observers.filter(obs => obs !== observer);
    }
    
    notify(data) {
        this.observers.forEach(observer => observer.update(data));
    }
}

class Observer {
    constructor(name) {
        this.name = name;
    }
    
    update(data) {
        console.log(`${this.name} 收到数据: ${data}`);
    }
}

// 使用观察者模式
const subject = new Subject();

const observer1 = new Observer("观察者1");
const observer2 = new Observer("观察者2");

subject.subscribe(observer1);
subject.subscribe(observer2);

subject.notify("重要通知"); // 通知所有观察者
// 输出:
// 观察者1 收到数据: 重要通知
// 观察者2 收到数据: 重要通知
```

### 7.3 Web API与DOM操作

#### DOM操作基础

- **DOM选择**：`document.querySelector`, `document.getElementById`等
- **DOM修改**：`createElement`, `appendChild`, `removeChild`等
- **DOM事件**：`addEventListener`, `removeEventListener`

```javascript
// DOM操作示例
document.addEventListener('DOMContentLoaded', () => {
    // 选择元素
    const container = document.querySelector('.container');
    
    // 创建新元素
    const paragraph = document.createElement('p');
    paragraph.textContent = '这是一个动态创建的段落';
    paragraph.classList.add('dynamic-paragraph');
    
    // 添加到DOM
    container.appendChild(paragraph);
    
    // 添加事件监听
    paragraph.addEventListener('click', function() {
        this.style.color = 'red';
        console.log('段落被点击');
    });
    
    // 移除元素（3秒后）
    setTimeout(() => {
        container.removeChild(paragraph);
    }, 3000);
});
```

#### 浏览器API

- **Fetch API**：用于网络请求
- **Web Storage API**：`localStorage`和`sessionStorage`
- **Canvas API**：绘制图形
- **Web Workers**：后台线程处理

```javascript
// Fetch API示例
async function fetchData() {
    try {
        const response = await fetch('https://api.example.com/data');
        
        if (!response.ok) {
            throw new Error(`HTTP错误: ${response.status}`);
        }
        
        const data = await response.json();
        console.log('获取的数据:', data);
        return data;
    } catch (error) {
        console.error('获取数据失败:', error);
        throw error;
    }
}

// Web Storage API示例
function saveUserPreferences(preferences) {
    try {
        localStorage.setItem('userPreferences', JSON.stringify(preferences));
        return true;
    } catch (error) {
        console.error('保存偏好设置失败:', error);
        return false;
    }
}

function getUserPreferences() {
    try {
        const preferences = localStorage.getItem('userPreferences');
        return preferences ? JSON.parse(preferences) : null;
    } catch (error) {
        console.error('获取偏好设置失败:', error);
        return null;
    }
}
```

#### 异步DOM操作

- **requestAnimationFrame**：优化动画效果
- **IntersectionObserver**：检测元素可见性
- **MutationObserver**：监听DOM变化

```javascript
// requestAnimationFrame示例
function animateElement(element) {
    let position = 0;
    
    function step(timestamp) {
        position += 5;
        element.style.transform = `translateX(${position}px)`;
        
        if (position < 300) {
            requestAnimationFrame(step);
        }
    }
    
    requestAnimationFrame(step);
}

// IntersectionObserver示例
function lazyLoadImages() {
    const images = document.querySelectorAll('.lazy-image');
    
    const observer = new IntersectionObserver((entries, observer) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                const img = entry.target;
                img.src = img.dataset.src;
                img.classList.remove('lazy-image');
                observer.unobserve(img);
            }
        });
    });
    
    images.forEach(image => {
        observer.observe(image);
    });
}
```

## 8. JavaScript形式化验证与规范

### 8.1 形式化规范

#### ECMAScript规范

- **ECMA-262**：JavaScript的官方规范
- **规范内容**：语法、语义、内置对象、执行模型等
- **TC39流程**：新特性从Stage 0到Stage 4的演进

#### 形式化语言规范

- **BNF语法**：描述JavaScript语法的上下文无关文法
- **操作语义**：通过抽象机器和状态转换定义语义
- **类型规则**：定义类型检查和类型转换规则

```javascript
// ECMA-262规范中的Array.prototype.map的形式化描述(简化)
/*
22.1.3.18 Array.prototype.map ( callbackfn [ , thisArg ] )

1. Let O be ? ToObject(this value).
2. Let len be ? LengthOfArrayLike(O).
3. If IsCallable(callbackfn) is false, throw a TypeError exception.
4. Let A be ? ArraySpeciesCreate(O, len).
5. Let k be 0.
6. Repeat, while k < len
   a. Let Pk be ! ToString(k).
   b. Let kPresent be ? HasProperty(O, Pk).
   c. If kPresent is true, then
      i. Let kValue be ? Get(O, Pk).
      ii. Let mappedValue be ? Call(callbackfn, thisArg, « kValue, k, O »).
      iii. Perform ? CreateDataPropertyOrThrow(A, Pk, mappedValue).
   d. Increase k by 1.
7. Return A.
*/
```

#### 形式化验证工具

- **TypeScript**：静态类型检查
- **Flow**：渐进式类型检查
- **JSDoc**：通过注释提供类型信息

```javascript
// TypeScript示例
interface User {
    id: number;
    name: string;
    age?: number; // 可选属性
    readonly createdAt: Date; // 只读属性
}

function getUserName(user: User): string {
    return user.name;
}

// 泛型函数
function firstElement<T>(array: T[]): T | undefined {
    return array[0];
}

// 联合类型
type Result<T> = { success: true, data: T } | { success: false, error: string };

function fetchUser(id: number): Promise<Result<User>> {
    // 实现...
}
```

### 8.2 静态分析与验证

#### 8.2.1 静态分析工具

- **ESLint**：静态代码分析工具，检查代码质量和风格
- **JSHint**：检测潜在问题和错误
- **SonarJS**：检测代码气味和漏洞

```javascript
// ESLint配置示例
module.exports = {
    "env": {
        "browser": true,
        "es2021": true
    },
    "extends": "eslint:recommended",
    "parserOptions": {
        "ecmaVersion": 12,
        "sourceType": "module"
    },
    "rules": {
        "no-unused-vars": "error",
        "no-console": "warn",
        "prefer-const": "error",
        "complexity": ["warn", 10]
    }
};
```

#### 类型检查与推断

- **类型系统**：TypeScript的结构化类型系统
- **类型推断**：自动推断变量类型
- **类型断言**：明确指定类型

```typescript
// TypeScript类型检查示例
function calculateDiscount(price: number, discountPercent: number): number {
    if (discountPercent < 0 || discountPercent > 100) {
        throw new Error("折扣百分比必须在0-100之间");
    }
    return price * (1 - discountPercent / 100);
}

// 类型推断
let price = 100; // 推断为number类型
let name = "产品"; // 推断为string类型

// 联合类型
function printId(id: number | string) {
    if (typeof id === "string") {
        // 在这个分支，id的类型被缩小为string
        console.log(id.toUpperCase());
    } else {
        // 在这个分支，id的类型被缩小为number
        console.log(id);
    }
}
```

#### 形式化验证技术

- **契约式编程**：前置条件、后置条件和不变量
- **模型检查**：验证程序是否满足特定属性
- **符号执行**：分析程序可能执行路径

```javascript
// 契约式编程示例(使用JSDoc)
/**
 * 计算数组元素的平均值
 * @param {number[]} numbers - 输入数字数组
 * @pre numbers不为空且只包含数字
 * @post 返回数组元素的算术平均值
 * @throws {Error} 如果数组为空
 * @returns {number} 平均值
 */
function average(numbers) {
    // 前置条件检查
    if (!Array.isArray(numbers) || numbers.length === 0) {
        throw new Error("输入必须是非空数组");
    }
    
    if (!numbers.every(n => typeof n === 'number')) {
        throw new Error("数组必须只包含数字");
    }
    
    // 计算平均值
    const sum = numbers.reduce((acc, val) => acc + val, 0);
    const avg = sum / numbers.length;
    
    // 后置条件检查（在调试模式下）
    if (process.env.NODE_ENV === 'development') {
        if (isNaN(avg)) {
            throw new Error("计算结果不是一个数字");
        }
    }
    
    return avg;
}
```

### 8.3 运行时验证与断言

#### 断言库

- **Chai**：断言库，支持BDD和TDD风格
- **Assert**：Node.js内置断言模块
- **Jest Expect**：Jest测试框架的断言API

```javascript
// Chai断言示例
const { expect } = require('chai');

function testUserFunctions() {
    const user = { id: 1, name: "张三", role: "admin" };
    
    // 对象属性断言
    expect(user).to.have.property('id').that.equals(1);
    expect(user).to.have.property('name').that.is.a('string');
    
    // 函数行为断言
    const getUserRole = (user) => user.role;
    expect(getUserRole(user)).to.equal('admin');
    
    // 异常断言
    const throwingFunction = () => { throw new Error("测试错误"); };
    expect(throwingFunction).to.throw();
    
    // 数组断言
    const users = [user, { id: 2, name: "李四", role: "user" }];
    expect(users).to.have.lengthOf(2);
    expect(users.map(u => u.id)).to.include(1);
}
```

#### 运行时类型检查

- **PropTypes**：React组件属性类型检查
- **Ajv**：JSON Schema验证
- **io-ts**：运行时类型检查

```javascript
// PropTypes示例
import React from 'react';
import PropTypes from 'prop-types';

function UserProfile({ user, onUpdate }) {
    return (
        <div>
            <h2>{user.name}</h2>
            <p>ID: {user.id}</p>
            <p>角色: {user.role}</p>
            <button onClick={() => onUpdate(user.id)}>更新</button>
        </div>
    );
}

UserProfile.propTypes = {
    user: PropTypes.shape({
        id: PropTypes.number.isRequired,
        name: PropTypes.string.isRequired,
        role: PropTypes.string.isRequired
    }).isRequired,
    onUpdate: PropTypes.func.isRequired
};
```

#### 不变量与契约

- **不变量**：在程序执行过程中始终为真的条件
- **前置条件**：函数调用前必须满足的条件
- **后置条件**：函数执行后保证满足的条件

```javascript
// 自定义契约断言系统
function assert(condition, message) {
    if (!condition) {
        throw new Error(message || "断言失败");
    }
}

function Contract(preconditions = [], postconditions = []) {
    return function(target, propertyKey, descriptor) {
        const originalMethod = descriptor.value;
        
        descriptor.value = function(...args) {
            // 检查前置条件
            preconditions.forEach(pre => {
                assert(pre.condition(...args), pre.message);
            });
            
            // 调用原始方法
            const result = originalMethod.apply(this, args);
            
            // 检查后置条件
            postconditions.forEach(post => {
                assert(post.condition(result, ...args), post.message);
            });
            
            return result;
        };
        
        return descriptor;
    };
}

// 使用示例
class MathUtils {
    @Contract(
        [
            { 
                condition: (a, b) => b !== 0,
                message: "除数不能为零"
            }
        ],
        [
            {
                condition: (result) => !isNaN(result),
                message: "结果必须是数字"
            }
        ]
    )
    static divide(a, b) {
        return a / b;
    }
}
```

## 9. 思维导图扩展

```text
JavaScript函数式编程与形式化验证
├── 7. JavaScript函数式编程
│   ├── 7.1 函数式编程范式
│   │   ├── 基本概念
│   │   │   ├── 纯函数
│   │   │   ├── 不可变性
│   │   │   ├── 高阶函数
│   │   │   └── 声明式编程
│   │   ├── 函数组合
│   │   │   ├── 组合(compose)
│   │   │   ├── 管道(pipe)
│   │   │   └── 点自由风格
│   │   └── 函数式编程库
│   │       ├── Ramda
│   │       ├── Lodash/FP
│   │       └── Immutable.js
│   ├── 7.2 JavaScript设计模式
│   │   ├── 创建型模式
│   │   │   ├── 单例模式
│   │   │   ├── 工厂模式
│   │   │   └── 构建者模式
│   │   ├── 结构型模式
│   │   │   ├── 适配器模式
│   │   │   ├── 装饰器模式
│   │   │   └── 代理模式
│   │   └── 行为型模式
│   │       ├── 观察者模式
│   │       ├── 策略模式
│   │       └── 迭代器模式
│   └── 7.3 Web API与DOM操作
│       ├── DOM操作基础
│       │   ├── DOM选择
│       │   ├── DOM修改
│       │   └── DOM事件
│       ├── 浏览器API
│       │   ├── Fetch API
│       │   ├── Web Storage API
│       │   ├── Canvas API
│       │   └── Web Workers
│       └── 异步DOM操作
│           ├── requestAnimationFrame
│           ├── IntersectionObserver
│           └── MutationObserver
└── 8. JavaScript形式化验证与规范
    ├── 8.1 形式化规范
    │   ├── ECMAScript规范
    │   │   ├── ECMA-262
    │   │   ├── 规范内容
    │   │   └── TC39流程
    │   ├── 形式化语言规范
    │   │   ├── BNF语法
    │   │   ├── 操作语义
    │   │   └── 类型规则
    │   └── 形式化验证工具
    │       ├── TypeScript
    │       ├── Flow
    │       └── JSDoc
    ├── 8.2 静态分析与验证
    │   ├── 静态分析工具
    │   │   ├── ESLint
    │   │   ├── JSHint
    │   │   └── SonarJS
    │   ├── 类型检查与推断
    │   │   ├── 类型系统
    │   │   ├── 类型推断
    │   │   └── 类型断言
    │   └── 形式化验证技术
    │       ├── 契约式编程
    │       ├── 模型检查
    │       └── 符号执行
    └── 8.3 运行时验证与断言
        ├── 断言库
        │   ├── Chai
        │   ├── Assert
        │   └── Jest Expect
        ├── 运行时类型检查
        │   ├── PropTypes
        │   ├── Ajv
        │   └── io-ts
        └── 不变量与契约
            ├── 不变量
            ├── 前置条件
            └── 后置条件
```

## 10. 现代JavaScript生态系统

### 10.1 前端框架与库

#### 声明式UI框架

- **React**：基于组件的声明式UI库，使用虚拟DOM
- **Vue**：渐进式JavaScript框架，响应式数据绑定
- **Angular**：完整的前端MVC框架，基于TypeScript

```javascript
// React组件示例
import React, { useState, useEffect } from 'react';

function Counter() {
    const [count, setCount] = useState(0);
    
    useEffect(() => {
        document.title = `点击了${count}次`;
    }, [count]);
    
    return (
        <div>
            <p>你点击了{count}次</p>
            <button onClick={() => setCount(count + 1)}>
                点击我
            </button>
        </div>
    );
}

// Vue组件示例
const Counter = {
    data() {
        return {
            count: 0
        };
    },
    watch: {
        count(newValue) {
            document.title = `点击了${newValue}次`;
        }
    },
    template: `
        <div>
            <p>你点击了{{ count }}次</p>
            <button @click="count++">点击我</button>
        </div>
    `
};
```

#### 状态管理

- **Redux**：可预测的状态容器，强调单向数据流
- **MobX**：通过透明的函数响应式编程使状态管理简单
- **Vuex/Pinia**：Vue专用的状态管理解决方案

```javascript
// Redux状态管理示例
import { createStore } from 'redux';

// 定义初始状态和reducer
const initialState = { count: 0 };

function counterReducer(state = initialState, action) {
    switch (action.type) {
        case 'INCREMENT':
            return { ...state, count: state.count + 1 };
        case 'DECREMENT':
            return { ...state, count: state.count - 1 };
        default:
            return state;
    }
}

// 创建store
const store = createStore(counterReducer);

// 订阅变化
store.subscribe(() => {
    console.log('当前状态:', store.getState());
});

// 发送动作
store.dispatch({ type: 'INCREMENT' }); // 计数器加1
store.dispatch({ type: 'INCREMENT' }); // 计数器加1
store.dispatch({ type: 'DECREMENT' }); // 计数器减1
```

#### 构建工具与打包器

- **Webpack**：模块打包器，处理依赖关系
- **Rollup**：适用于库的ES模块打包器
- **Vite**：基于ES模块的新一代前端构建工具
- **esbuild**：极速JavaScript打包器

```javascript
// webpack配置示例
const path = require('path');
const HtmlWebpackPlugin = require('html-webpack-plugin');

module.exports = {
    entry: './src/index.js',
    output: {
        path: path.resolve(__dirname, 'dist'),
        filename: 'bundle.[contenthash].js'
    },
    module: {
        rules: [
            {
                test: /\.js$/,
                exclude: /node_modules/,
                use: {
                    loader: 'babel-loader',
                    options: {
                        presets: ['@babel/preset-env', '@babel/preset-react']
                    }
                }
            },
            {
                test: /\.css$/,
                use: ['style-loader', 'css-loader']
            }
        ]
    },
    plugins: [
        new HtmlWebpackPlugin({
            template: './src/index.html'
        })
    ],
    devServer: {
        contentBase: path.join(__dirname, 'dist'),
        port: 3000
    }
};
```

### 10.2 服务端JavaScript

#### Node.js生态系统

- **Express**：极简Web框架
- **Koa**：由Express团队设计的新一代Web框架
- **NestJS**：受Angular启发的服务端框架
- **Fastify**：高性能的低开销框架

```javascript
// Express服务器示例
const express = require('express');
const app = express();
const port = 3000;

// 中间件
app.use(express.json());
app.use(express.urlencoded({ extended: true }));

// 路由
app.get('/', (req, res) => {
    res.send('Hello World!');
});

app.get('/api/users', (req, res) => {
    // 获取用户列表
    res.json([{ id: 1, name: '张三' }, { id: 2, name: '李四' }]);
});

app.post('/api/users', (req, res) => {
    // 创建新用户
    const { name } = req.body;
    res.status(201).json({ id: 3, name });
});

// 错误处理
app.use((err, req, res, next) => {
    console.error(err.stack);
    res.status(500).send('服务器出错了!');
});

// 启动服务器
app.listen(port, () => {
    console.log(`服务器运行在 http://localhost:${port}`);
});
```

#### 数据库集成

- **Mongoose**：MongoDB的优雅对象建模
- **Sequelize**：适用于MySQL, PostgreSQL等的ORM
- **Prisma**：下一代ORM，类型安全的数据库客户端
- **Knex.js**：灵活的SQL查询构建器

```javascript
// Mongoose示例
const mongoose = require('mongoose');
mongoose.connect('mongodb://localhost:27017/myapp');

// 定义Schema
const userSchema = new mongoose.Schema({
    name: { type: String, required: true },
    email: { type: String, required: true, unique: true },
    password: { type: String, required: true },
    createdAt: { type: Date, default: Date.now }
});

// 添加方法
userSchema.methods.generateAuthToken = function() {
    return jwt.sign({ id: this._id }, 'secretKey');
};

// 创建模型
const User = mongoose.model('User', userSchema);

// 使用模型
async function createUser(userData) {
    try {
        const user = new User(userData);
        await user.save();
        return user;
    } catch (error) {
        console.error('创建用户失败:', error);
        throw error;
    }
}
```

#### 微服务与API网关

- **gRPC**：高性能的RPC框架
- **GraphQL**：用于API的查询语言
- **Apollo Server**：GraphQL服务器
- **tRPC**：端到端的类型安全API

```javascript
// GraphQL服务器示例(Apollo Server)
const { ApolloServer, gql } = require('apollo-server');

// 类型定义
const typeDefs = gql`
    type User {
        id: ID!
        name: String!
        email: String!
        posts: [Post!]!
    }
    
    type Post {
        id: ID!
        title: String!
        content: String!
        author: User!
    }
    
    type Query {
        user(id: ID!): User
        users: [User!]!
        posts: [Post!]!
    }
    
    type Mutation {
        createUser(name: String!, email: String!): User!
        createPost(title: String!, content: String!, authorId: ID!): Post!
    }
`;

// 解析器
const resolvers = {
    Query: {
        user: (_, { id }) => users.find(user => user.id === id),
        users: () => users,
        posts: () => posts
    },
    Mutation: {
        createUser: (_, { name, email }) => {
            const newUser = { id: String(users.length + 1), name, email, posts: [] };
            users.push(newUser);
            return newUser;
        },
        createPost: (_, { title, content, authorId }) => {
            const author = users.find(user => user.id === authorId);
            if (!author) throw new Error('作者不存在');
            
            const newPost = { id: String(posts.length + 1), title, content, authorId };
            posts.push(newPost);
            return newPost;
        }
    },
    User: {
        posts: (user) => posts.filter(post => post.authorId === user.id)
    },
    Post: {
        author: (post) => users.find(user => user.id === post.authorId)
    }
};

// 创建服务器
const server = new ApolloServer({ typeDefs, resolvers });

// 启动服务器
server.listen().then(({ url }) => {
    console.log(`GraphQL服务器运行在 ${url}`);
});
```

### 10.3 测试与质量保证

#### 测试框架

- **Jest**：Facebook开发的零配置测试框架
- **Mocha**：灵活的JavaScript测试框架
- **Cypress**：端到端测试框架
- **Testing Library**：用户界面测试工具

```javascript
// Jest单元测试示例
import { sum, multiply } from './math';

describe('数学工具函数', () => {
    test('sum函数能正确相加两个数', () => {
        expect(sum(1, 2)).toBe(3);
        expect(sum(-1, 1)).toBe(0);
        expect(sum(0, 0)).toBe(0);
    });
    
    test('multiply函数能正确相乘两个数', () => {
        expect(multiply(2, 3)).toBe(6);
        expect(multiply(0, 5)).toBe(0);
        expect(multiply(-2, 3)).toBe(-6);
    });
});

// React组件测试示例
import { render, screen, fireEvent } from '@testing-library/react';
import Counter from './Counter';

describe('Counter组件', () => {
    test('初始计数为0', () => {
        render(<Counter />);
        const countElement = screen.getByText(/点击了0次/i);
        expect(countElement).toBeInTheDocument();
    });
    
    test('点击按钮后计数增加', () => {
        render(<Counter />);
        const button = screen.getByText(/点击我/i);
        
        fireEvent.click(button);
        expect(screen.getByText(/点击了1次/i)).toBeInTheDocument();
        
        fireEvent.click(button);
        expect(screen.getByText(/点击了2次/i)).toBeInTheDocument();
    });
});
```

#### 代码质量工具

- **ESLint**：JavaScript静态代码分析工具
- **Prettier**：代码格式化工具
- **Husky**：Git钩子集成
- **lint-staged**：对暂存的文件运行linters

```javascript
// .eslintrc.js配置
module.exports = {
    env: {
        browser: true,
        es2021: true,
        node: true,
        jest: true
    },
    extends: [
        'eslint:recommended',
        'plugin:react/recommended',
        'plugin:react-hooks/recommended',
        'prettier'
    ],
    parserOptions: {
        ecmaFeatures: {
            jsx: true
        },
        ecmaVersion: 12,
        sourceType: 'module'
    },
    plugins: [
        'react',
        'react-hooks'
    ],
    rules: {
        'react/prop-types': 'warn',
        'react-hooks/rules-of-hooks': 'error',
        'react-hooks/exhaustive-deps': 'warn',
        'no-console': ['warn', { allow: ['warn', 'error'] }]
    },
    settings: {
        react: {
            version: 'detect'
        }
    }
};

// package.json中的lint-staged和husky配置
{
    "scripts": {
        "lint": "eslint src --ext .js,.jsx",
        "format": "prettier --write \"src/**/*.{js,jsx,css,scss}\""
    },
    "husky": {
        "hooks": {
            "pre-commit": "lint-staged",
            "pre-push": "npm test"
        }
    },
    "lint-staged": {
        "src/**/*.{js,jsx}": [
            "eslint --fix",
            "prettier --write"
        ],
        "src/**/*.{css,scss}": [
            "prettier --write"
        ]
    }
}
```

#### 持续集成/持续部署(CI/CD)

- **GitHub Actions**：GitHub集成的CI/CD解决方案
- **CircleCI**：持续集成和交付平台
- **Jenkins**：开源自动化服务器
- **GitLab CI**：GitLab集成的CI/CD

```yaml
# .github/workflows/ci.yml - GitHub Actions工作流配置
name: CI/CD流程

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  build-and-test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v2
    
    - name: 设置Node.js
      uses: actions/setup-node@v2
      with:
        node-version: '16'
        cache: 'npm'
    
    - name: 安装依赖
      run: npm ci
    
    - name: 代码检查
      run: npm run lint
    
    - name: 运行测试
      run: npm test
    
    - name: 构建应用
      run: npm run build
    
    - name: 部署到生产环境
      if: github.ref == 'refs/heads/main'
      run: |
        # 部署步骤
        npm run deploy
```

## 11. JavaScript元编程与高级特性

### 11.1 元编程技术

#### 反射API

- **Reflect**：提供与对象反射相关的方法
- **获取/设置属性**：`Reflect.get()`, `Reflect.set()`
- **定义属性**：`Reflect.defineProperty()`
- **删除属性**：`Reflect.deleteProperty()`

```javascript
// Reflect API示例
const user = {
    name: '张三',
    age: 30
};

// 获取属性
console.log(Reflect.get(user, 'name')); // '张三'

// 设置属性
Reflect.set(user, 'age', 31);
console.log(user.age); // 31

// 检查属性是否存在
console.log(Reflect.has(user, 'name')); // true
console.log(Reflect.has(user, 'address')); // false

// 删除属性
Reflect.deleteProperty(user, 'age');
console.log(user.age); // undefined

// 获取所有自有属性键
console.log(Reflect.ownKeys(user)); // ['name']
```

#### 代理(Proxy)

- **定义**：允许自定义对象基本操作的行为
- **拦截器**：`get`, `set`, `apply`, `construct`等
- **应用**：数据绑定、权限控制、API包装

```javascript
// Proxy示例 - 实现响应式数据
function reactive(obj) {
    return new Proxy(obj, {
        get(target, key, receiver) {
            console.log(`获取属性: ${key}`);
            return Reflect.get(target, key, receiver);
        },
        set(target, key, value, receiver) {
            console.log(`设置属性: ${key} = ${value}`);
            return Reflect.set(target, key, value, receiver);
        },
        deleteProperty(target, key) {
            console.log(`删除属性: ${key}`);
            return Reflect.deleteProperty(target, key);
        }
    });
}

const user = reactive({
    name: '张三',
    age: 30
});

user.name; // 输出: 获取属性: name
user.age = 31; // 输出: 设置属性: age = 31
delete user.name; // 输出: 删除属性: name

// Proxy实现权限控制
function createProtectedObject(target, allowedOperations) {
    return new Proxy(target, {
        get(target, key, receiver) {
            if (allowedOperations.includes('read')) {
                return Reflect.get(target, key, receiver);
            } else {
                throw new Error('没有读取权限');
            }
        },
        set(target, key, value, receiver) {
            if (allowedOperations.includes('write')) {
                return Reflect.set(target, key, value, receiver);
            } else {
                throw new Error('没有写入权限');
            }
        }
    });
}

const data = { secret: '机密信息' };
const readOnlyData = createProtectedObject(data, ['read']);
const writeOnlyData = createProtectedObject(data, ['write']);

console.log(readOnlyData.secret); // '机密信息'
readOnlyData.secret = '新信息'; // 错误: 没有写入权限

writeOnlyData.secret = '新信息'; // 成功
console.log(writeOnlyData.secret); // 错误: 没有读取权限
```

#### Symbol与Symbol.for

- **定义**：唯一标识符，用作对象属性键
- **内置Symbol**：`Symbol.iterator`, `Symbol.toStringTag`等
- **全局符号注册表**：`Symbol.for()`与`Symbol.keyFor()`

```javascript
// Symbol用法示例
// 创建唯一的Symbol
const id = Symbol('id');
const user = {
    name: '张三',
    age: 30,
    [id]: 1001 // 使用Symbol作为属性键
};

console.log(user[id]); // 1001
console.log(Object.keys(user)); // ['name', 'age'] - Symbol属性不会出现在这里

// 全局符号注册表
const globalId = Symbol.for('userId'); // 创建或查找全局符号
const sameId = Symbol.for('userId'); // 返回相同的符号

console.log(globalId === sameId); // true
console.log(Symbol.keyFor(globalId)); // 'userId'

// 内置Symbol
const collection = {
    items: ['a', 'b', 'c'],
    [Symbol.iterator]: function* () {
        for (let item of this.items) {
            yield item;
        }
    }
};

for (let item of collection) {
    console.log(item); // 依次输出: 'a', 'b', 'c'
}
```

### 11.2 装饰器模式与类增强

#### 装饰器语法(@)

- **类装饰器**：修改类的行为
- **方法装饰器**：修改类方法的行为
- **属性装饰器**：修改类属性的行为
- **参数装饰器**：修改方法参数的行为

```javascript
// 类装饰器示例
function sealed(constructor) {
    Object.seal(constructor);
    Object.seal(constructor.prototype);
    return constructor;
}

// 方法装饰器示例
function log(target, key, descriptor) {
    const original = descriptor.value;
    
    descriptor.value = function(...args) {
        console.log(`调用方法 ${key} 参数:`, args);
        const result = original.apply(this, args);
        console.log(`方法 ${key} 返回:`, result);
        return result;
    };
    
    return descriptor;
}

// 属性装饰器示例
function uppercaseGetter(target, key) {
    let value = target[key];
    
    const getter = function() {
        return value;
    };
    
    const setter = function(newValue) {
        value = typeof newValue === 'string' ? newValue.toUpperCase() : newValue;
    };
    
    Object.defineProperty(target, key, {
        get: getter,
        set: setter,
        enumerable: true,
        configurable: true
    });
}

// 使用装饰器
@sealed
class Person {
    @uppercaseGetter
    name;
    
    constructor(name) {
        this.name = name;
    }
    
    @log
    greet(greeting) {
        return `${greeting}, ${this.name}!`;
    }
}

const person = new Person('张三');
console.log(person.name); // '张三' (自动转换为大写)
person.greet('你好'); // 输出调用日志和返回值
```

#### 混入(Mixins)

- **定义**：一种代码复用技术，将方法从源对象混入目标对象
- **实现**：通过`Object.assign`或类继承实现
- **应用**：扩展类功能，避免多重继承问题

```javascript
// 混入示例
// 定义混入对象
const loggingMixin = {
    log(message) {
        console.log(`[${this.constructor.name}] ${message}`);
    },
    error(message) {
        console.error(`[${this.constructor.name}] ERROR: ${message}`);
    }
};

const timestampMixin = {
    getTimestamp() {
        return new Date().toISOString();
    },
    logWithTimestamp(message) {
        console.log(`[${this.getTimestamp()}] ${message}`);
    }
};

// 应用混入
class Logger {
    constructor(name) {
        this.name = name;
    }
}

Object.assign(Logger.prototype, loggingMixin, timestampMixin);

const logger = new Logger('AppLogger');
logger.log('应用启动'); // '[AppLogger] 应用启动'
logger.logWithTimestamp('服务器已连接'); // '[2023-05-15T12:34:56.789Z] 服务器已连接'

// 使用类混入实现
function applyMixins(derivedCtor, baseCtors) {
    baseCtors.forEach(baseCtor => {
        Object.getOwnPropertyNames(baseCtor.prototype).forEach(name => {
            if (name !== 'constructor') {
                derivedCtor.prototype[name] = baseCtor.prototype[name];
            }
        });
    });
}

class Timestamped {
    getTimestamp() {
        return new Date().toISOString();
    }
}

class Loggable {
    log(message) {
        console.log(`[${this.name}] ${message}`);
    }
}

class AdvancedLogger {
    constructor(name) {
        this.name = name;
    }
}

applyMixins(AdvancedLogger, [Timestamped, Loggable]);
```

#### 元属性与扩展操作符

- **new.target**：判断函数是否通过`new`调用
- **super**：访问父类方法和属性
- **扩展操作符(...)**：数组和对象展开与解构

```javascript
// new.target示例
function User(name) {
    if (!new.target) {
        return new User(name); // 如果不是通过new调用，则自动修正
    }
    this.name = name;
}

const user1 = new User('张三');
const user2 = User('李四'); // 自动使用new调用
console.log(user1.name); // '张三'
console.log(user2.name); // '李四'

// super示例
class Animal {
    constructor(name) {
        this.name = name;
    }
    
    speak() {
        return `${this.name}发出声音`;
    }
}

class Dog extends Animal {
    constructor(name, breed) {
        super(name); // 调用父类构造函数
        this.breed = breed;
    }
    
    speak() {
        return `${super.speak()}，具体是：汪汪汪`; // 调用父类方法
    }
}

// 扩展操作符示例
// 数组展开
const numbers = [1, 2, 3];
const moreNumbers = [...numbers, 4, 5]; // [1, 2, 3, 4, 5]

// 对象展开
const defaults = { theme: 'dark', fontSize: 14 };
const userSettings = { fontSize: 16, showSidebar: true };
const settings = { ...defaults, ...userSettings }; // { theme: 'dark', fontSize: 16, showSidebar: true }

// 函数参数收集
function sum(...numbers) {
    return numbers.reduce((total, num) => total + num, 0);
}

console.log(sum(1, 2, 3, 4)); // 10
```

### 11.3 高级异步模式

#### 可取消的Promise

- **定义**：可以中途取消的Promise
- **实现**：通过AbortController或自定义Token实现
- **应用**：网络请求、长时间操作的取消

```javascript
// 使用AbortController实现可取消的Promise
function fetchWithTimeout(url, options = {}, timeoutMs = 5000) {
    const controller = new AbortController();
    const { signal } = controller;
    
    // 设置超时取消
    const timeout = setTimeout(() => {
        controller.abort();
    }, timeoutMs);
    
    // 创建可取消的请求
    const promise = fetch(url, { ...options, signal })
        .then(response => {
            clearTimeout(timeout);
            return response;
        })
        .catch(error => {
            clearTimeout(timeout);
            if (error.name === 'AbortError') {
                throw new Error(`请求超时: ${timeoutMs}ms`);
            }
            throw error;
        });
    
    // 添加取消方法
    promise.cancel = () => {
        clearTimeout(timeout);
        controller.abort();
    };
    
    return promise;
}

// 使用示例
const request = fetchWithTimeout('https://api.example.com/data', {}, 3000);

request
    .then(response => response.json())
    .then(data => console.log('获取数据:', data))
    .catch(error => console.error('错误:', error));

// 在某些条件下取消请求
setTimeout(() => {
    request.cancel();
    console.log('请求已取消');
}, 1000);
```

#### Promise并发控制

- **定义**：限制同时执行的Promise数量
- **实现**：队列与信号量机制
- **应用**：防止过多并发请求导致系统过载

```javascript
// Promise并发控制器
class PromisePool {
    constructor(concurrency) {
        this.concurrency = concurrency; // 最大并发数
        this.running = 0; // 当前运行的任务数
        this.queue = []; // 等待执行的任务队列
    }
    
    // 添加任务
    add(promiseFactory) {
        return new Promise((resolve, reject) => {
            this.queue.push({
                promiseFactory,
                resolve,
                reject
            });
            
            this._next();
        });
    }
    
    // 执行下一个任务
    _next() {
        if (this.running >= this.concurrency || this.queue.length === 0) {
            return;
        }
        
        const { promiseFactory, resolve, reject } = this.queue.shift();
        this.running++;
        
        promiseFactory()
            .then(result => {
                this.running--;
                resolve(result);
                this._next();
            })
            .catch(error => {
                this.running--;
                reject(error);
                this._next();
            });
    }
    
    // 并行执行一批任务，限制最大并发数
    static map(items, mapper, concurrency) {
        const pool = new PromisePool(concurrency);
        return Promise.all(items.map(item => pool.add(() => mapper(item))));
    }
}

// 使用示例
const urls = [
    'https://api.example.com/1',
    'https://api.example.com/2',
    'https://api.example.com/3',
    'https://api.example.com/4',
    'https://api.example.com/5'
];

// 限制最多同时执行2个请求
PromisePool.map(urls, url => fetch(url).then(res => res.json()), 2)
    .then(results => console.log('所有结果:', results))
    .catch(error => console.error('发生错误:', error));
```

#### 异步迭代器与生成器

- **异步迭代器**：`for await...of`循环处理异步数据流
- **异步生成器**：使用`async function*`创建异步数据源
- **应用**：处理大型数据集、分页API、流处理

```javascript
// 异步迭代器示例
class AsyncPaginatedAPI {
    constructor(baseUrl, pageSize = 10) {
        this.baseUrl = baseUrl;
        this.pageSize = pageSize;
    }
    
    // 创建异步迭代器
    async *[Symbol.asyncIterator]() {
        let page = 1;
        let hasMore = true;
        
        while (hasMore) {
            const url = `${this.baseUrl}?page=${page}&pageSize=${this.pageSize}`;
            const response = await fetch(url);
            const data = await response.json();
            
            // 假设API返回items数组和hasMore标志
            hasMore = data.hasMore;
            page++;
            
            // 逐个产出每个item
            for (const item of data.items) {
                yield item;
            }
        }
    }
}

// 使用异步迭代器处理分页数据
async function processAllUsers() {
    const api = new AsyncPaginatedAPI('https://api.example.com/users');
    
    let count = 0;
    for await (const user of api) {
        console.log(`处理用户: ${user.name}`);
        count++;
        
        // 可以随时中断循环
        if (count >= 100) {
            console.log('已处理100个用户，停止处理');
            break;
        }
    }
    
    console.log(`共处理${count}个用户`);
}

// 异步生成器函数
async function* generateAsyncSequence(start, end, delay) {
    for (let i = start; i <= end; i++) {
        await new Promise(resolve => setTimeout(resolve, delay));
        yield i;
    }
}

// 使用异步生成器
async function useAsyncGenerator() {
    const sequence = generateAsyncSequence(1, 5, 1000);
    
    for await (const num of sequence) {
        console.log(`异步生成的数字: ${num}`);
    }
}
```

## 12. 思维导图扩展

```text
现代JavaScript生态系统与高级特性
├── 10. 现代JavaScript生态系统
│   ├── 10.1 前端框架与库
│   │   ├── 声明式UI框架
│   │   │   ├── React
│   │   │   ├── Vue
│   │   │   └── Angular
│   │   ├── 状态管理
│   │   │   ├── Redux
│   │   │   ├── MobX
│   │   │   └── Vuex/Pinia
│   │   └── 构建工具与打包器
│   │       ├── Webpack
│   │       ├── Rollup
│   │       ├── Vite
│   │       └── esbuild
│   ├── 10.2 服务端JavaScript
│   │   ├── Node.js生态系统
│   │   │   ├── Express
│   │   │   ├── Koa
│   │   │   ├── NestJS
│   │   │   └── Fastify
│   │   ├── 数据库集成
│   │   │   ├── Mongoose
│   │   │   ├── Sequelize
│   │   │   ├── Prisma
│   │   │   └── Knex.js
│   │   └── 微服务与API网关
│   │       ├── gRPC
│   │       ├── GraphQL
│   │       ├── Apollo Server
│   │       └── tRPC
│   └── 10.3 测试与质量保证
│       ├── 测试框架
│       │   ├── Jest
│       │   ├── Mocha
│       │   ├── Cypress
│       │   └── Testing Library
│       ├── 代码质量工具
│       │   ├── ESLint
│       │   ├── Prettier
│       │   ├── Husky
│       │   └── lint-staged
│       └── 持续集成/持续部署(CI/CD)
│           ├── GitHub Actions
│           ├── CircleCI
│           ├── Jenkins
│           └── GitLab CI
└── 11. JavaScript元编程与高级特性
    ├── 11.1 元编程技术
    │   ├── 反射API
    │   │   ├── Reflect对象
    │   │   ├── 获取/设置属性
    │   │   ├── 定义属性
    │   │   └── 删除属性
    │   ├── 代理(Proxy)
    │   │   ├── 拦截器
    │   │   ├── 数据绑定
    │   │   └── 权限控制
    │   └── Symbol与Symbol.for
    │       ├── 唯一标识符
    │       ├── 内置Symbol
    │       └── 全局符号注册表
    ├── 11.2 装饰器模式与类增强
    │   ├── 装饰器语法(@)
    │   │   ├── 类装饰器
    │   │   ├── 方法装饰器
    │   │   ├── 属性装饰器
    │   │   └── 参数装饰器
    │   ├── 混入(Mixins)
    │   │   ├── 定义与实现
    │   │   ├── Object.assign
    │   │   └── 类混入
    │   └── 元属性与扩展操作符
    │       ├── new.target
    │       ├── super
    │       └── 扩展操作符(...)
    └── 11.3 高级异步模式
        ├── 可取消的Promise
        │   ├── AbortController
        │   ├── 超时控制
        │   └── 手动取消
        ├── Promise并发控制
        │   ├── 并发限制
        │   ├── 队列处理
        │   └── 批量执行
        └── 异步迭代器与生成器
            ├── for await...of
            ├── Symbol.asyncIterator
            └── async function*
```
