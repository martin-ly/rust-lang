# TypeScript 深度分析：从基础到转换

## 目录

- [TypeScript 深度分析：从基础到转换](#typescript-深度分析从基础到转换)
  - [目录](#目录)
  - [1. TypeScript 核心概念](#1-typescript-核心概念)
    - [变量 (Variables)](#变量-variables)
    - [类型系统 (Type System)](#类型系统-type-system)
    - [控制流 (Control Flow)](#控制流-control-flow)
    - [语法与语义 (Syntax vs. Semantics)](#语法与语义-syntax-vs-semantics)
    - [作用域详解 (Scope Deep Dive)](#作用域详解-scope-deep-dive)
  - [2. 形式化视角 (Formal Perspectives)](#2-形式化视角-formal-perspectives)
  - [3. TypeScript 到 JavaScript 的转换 (Transformation)](#3-typescript-到-javascript-的转换-transformation)
  - [4. 执行模型 (Execution Model)](#4-执行模型-execution-model)
  - [5. 总结与思维导图](#5-总结与思维导图)

## 1. TypeScript 核心概念

TypeScript 是 JavaScript 的一个超集，它添加了可选的静态类型和其他特性，最终编译成纯 JavaScript。

### 变量 (Variables)

- **声明 (Declaration):** 使用 `var`, `let`, `const` 声明变量。`let` 和 `const` 引入了块级作用域。
  - `let`: 声明块级作用域的变量，可以被重新赋值。
  - `const`: 声明块级作用域的常量，声明时必须初始化，且不能被重新赋值（对于对象或数组，是引用不可变，但内容可变）。
  - `var`: 声明函数作用域或全局作用域的变量，存在变量提升 (hoisting) 问题。

    ```typescript
    let message: string = "Hello";
    const count: number = 10;
    // count = 11; // Error: Cannot assign to 'count' because it is a constant.

    if (true) {
        let blockScoped = "I'm inside";
        var functionScoped = "I'm potentially outside";
    }
    // console.log(blockScoped); // Error: blockScoped is not defined
    console.log(functionScoped); // "I'm potentially outside"
    ```

- **作用域 (Scope) - 静态/词法作用域:** TypeScript（和 JavaScript）使用**词法作用域 (Lexical Scoping)**，也称为**静态作用域 (Static Scoping)**。这意味着变量的作用域在代码编写时（词法分析阶段）就确定了，由变量声明的位置决定，而不是在运行时由函数调用栈决定（动态作用域）。

### 类型系统 (Type System)

- **静态类型 (Static Typing):** TypeScript 的核心特性。在编译时进行类型检查，可以捕获许多在运行时才会暴露的错误。类型可以通过显式注解 (`:` 后面跟类型) 或类型推断来确定。

    ```typescript
    function add(a: number, b: number): number {
        return a + b;
    }

    let result = add(5, 3); // result is inferred as number
    // let error = add("5", 3); // Error: Argument of type 'string' is not assignable to parameter of type 'number'.
    ```

- **基础与高级类型:**
  - **基础:** `number`, `string`, `boolean`, `null`, `undefined`, `symbol`, `bigint`, `void`, `any`, `unknown`, `never`.
  - **高级:**
    - **对象类型 (Object Types):** `interface`, `type` 别名。
    - **数组 (Arrays):** `number[]` 或 `Array<number>`.
    - **元组 (Tuples):** `[string, number]`.
    - **枚举 (Enums):** `enum Color { Red, Green, Blue }`.
    - **联合类型 (Union Types):** `string | number`.
    - **交叉类型 (Intersection Types):** `TypeA & TypeB`.
    - **字面量类型 (Literal Types):** `"hello"`, `123`, `true`.
    - **泛型 (Generics):** `<T>` 提供代码重用性和类型安全。
    - **索引类型 (Index Types):** `keyof`, `T[K]`.
    - **映射类型 (Mapped Types):** `{ [P in K]: T }`.
    - **条件类型 (Conditional Types):** `T extends U ? X : Y`.

    ```typescript
    // Interface (Object Type)
    interface Point {
        x: number;
        y: number;
    }

    // Type Alias with Union and Literal
    type Status = "pending" | "running" | "completed" | "failed";

    // Generic Function
    function identity<T>(arg: T): T {
        return arg;
    }
    let output = identity<string>("myString"); // type of output will be 'string'
    ```

- **类型推断 (Type Inference):** 当没有显式类型注解时，TypeScript 编译器会尝试根据上下文推断变量或表达式的类型。

    ```typescript
    let x = 3; // TypeScript infers x as number
    // x = "hello"; // Error: Type 'string' is not assignable to type 'number'.
    ```

- **类型兼容性 (Type Compatibility) - 结构化类型:** TypeScript 使用**结构化类型系统 (Structural Typing)**，也称为**鸭子类型 (Duck Typing)**。如果两个类型具有相同的结构（相同的属性和方法签名），即使它们没有显式继承关系，也被认为是兼容的。

    ```typescript
    interface Named {
        name: string;
    }

    class Person {
        name: string;
        age: number;
        constructor(name: string, age: number) {
            this.name = name;
            this.age = age;
        }
    }

    let p: Named;
    // OK, because Person has a 'name' property of type string
    // It matches the structure of Named.
    p = new Person("Alice", 30);

    function greet(n: Named) {
        console.log("Hello, " + n.name);
    }
    greet(p); // Works
    greet({ name: "Bob" }); // Works, object literal matches the structure
    // greet({ firstName: "Charlie" }); // Error: Argument of type '{ firstName: string; }' is not assignable to parameter of type 'Named'.
                                     // Property 'name' is missing.
    ```

### 控制流 (Control Flow)

- **语句 (Statements):** 代码执行的基本单元。
- **条件语句 (Conditional Statements):** 根据条件执行不同代码块。
  - `if...else if...else`
  - `switch...case`

    ```typescript
    let value: number = 10;
    if (value > 5) {
        console.log("Greater than 5");
    } else {
        console.log("Less than or equal to 5");
    }

    type Fruit = "apple" | "banana" | "orange";
    let myFruit: Fruit = "banana";
    switch (myFruit) {
        case "apple": console.log("It's an apple."); break;
        case "banana": console.log("It's a banana."); break;
        default: console.log("Some other fruit.");
    }
    ```

- **循环语句 (Looping Statements):** 重复执行代码块。
  - `for`
  - `for...in` (遍历对象的可枚举属性键)
  - `for...of` (遍历可迭代对象的值，如数组、字符串、Map、Set)
  - `while`
  - `do...while`

    ```typescript
    let items: number[] = [1, 2, 3];

    // for loop
    for (let i = 0; i < items.length; i++) {
        console.log(items[i]);
    }

    // for...of loop (preferred for arrays/iterables)
    for (const item of items) {
        console.log(item);
    }

    let obj = { a: 1, b: 2 };
    // for...in loop (for object keys)
    for (const key in obj) {
        if (Object.prototype.hasOwnProperty.call(obj, key)) {
             console.log(`key: ${key}, value: ${obj[key as keyof typeof obj]}`);
        }
    }

    let count = 0;
    // while loop
    while (count < 3) {
        console.log(count);
        count++;
    }
    ```

- **控制转移语句:** `break`, `continue`, `return`, `throw`.

### 语法与语义 (Syntax vs. Semantics)

- **语法 (Syntax):** 指构成有效程序的规则和结构。例如，`let x: number = 5;` 是有效的 TypeScript 语法，而 `let x number = 5;` 则不是。编译器首先进行**语法分析 (Parsing)** 来检查代码是否符合语法规则，并构建**抽象语法树 (Abstract Syntax Tree - AST)**。
- **语义 (Semantics):** 指代码的含义和行为。
  - **静态语义 (Static Semantics):** 在编译时可确定的语义规则，主要是类型检查。例如，`add("a", 1)` 在语法上可能有效（取决于 `add` 的定义），但在 TypeScript 中，如果 `add` 的参数被定义为 `number`，则这违反了静态语义（类型错误）。
  - **动态语义 (Dynamic Semantics):** 代码在运行时的实际行为。例如，`1 / 0` 在 JavaScript 中会得到 `Infinity`，这是其动态语义的一部分。TypeScript 的动态语义与其编译后的 JavaScript 代码的动态语义一致。

### 作用域详解 (Scope Deep Dive)

- **静态作用域 (Static/Lexical Scope):**
  - **定义:** 变量的可见性（作用域）由其在源代码中的物理位置决定。函数在定义时就确定了其能访问哪些外部变量，而不是在调用时。
  - **示例:**

```typescript
let x = 10;

function outer() {
    let y = 20;

    function inner() {
        let z = 30;
        console.log(x, y, z); // Can access x, y, z
    }

    inner();
    // console.log(z); // Error: z is not defined here
}

outer(); // Output: 10 20 30
// console.log(y); // Error: y is not defined here
```

在 `inner` 函数中，它可以访问自身的变量 `z`，以及定义它的外部函数 `outer` 的变量 `y`，以及全局变量 `x`。这是因为在词法分析阶段，作用域链就已经确定了：`inner` -> `outer` -> `global`.

- **动态作用域 (Dynamic Scope) - 对比:**
  - **定义:** 变量的可见性取决于函数调用时的上下文（调用栈），而不是函数定义时的位置。如果一个函数内部引用了一个未在其内部定义的变量，它会沿着调用栈向上查找，直到找到该变量的定义。
  - **TypeScript/JavaScript 不使用动态作用域。** 某些语言（如早期的 Lisp 方言、Bash shell 脚本的某些情况）使用动态作用域。
  - **伪代码示例 (说明概念):**

```javascript
// Hypothetical language with dynamic scope
var x = 1;

function foo() {
    print x; // Prints based on where foo is called from
}

function bar() {
    var x = 2;
    foo(); // foo() will find x=2 from bar's scope
}

bar(); // Output: 2 (in dynamic scope)
        // Output: 1 (in static/lexical scope, which TS/JS use)
```

## 2. 形式化视角 (Formal Perspectives)

形式化方法使用数学和逻辑来精确描述和推理系统（如编程语言）的属性。对于 TypeScript 这样复杂的语言，完全的形式化是极其困难的，但我们可以讨论一些关键概念。

- **类型系统形式化 (Type System Formalization):**
  - **概念:** 使用数学符号和规则（如类型规则、判断式 `Γ ⊢ e : τ` 表示在上下文 `Γ` 中表达式 `e` 具有类型 `τ`）来精确定义类型系统及其行为。
  - **TypeScript:** TypeScript 的类型系统是**结构化 (Structural)** 的，并且是**逐渐类型 (Gradual Typing)** 的（允许 `any` 类型绕过类型检查）。形式化 TypeScript 具有挑战性，因为它结合了标称类型（如类和枚举的某些方面）和结构化类型，并包含许多高级特性（泛型、条件类型等）。研究人员已对 TypeScript 的子集进行了形式化研究，以理解其属性和健全性（类型系统是否能保证没有运行时类型错误，对于有 `any` 的 TypeScript 来说，它不是完全健全的）。
  - **证明:** 形式化证明通常涉及归纳法，证明类型规则的应用保留了某些属性（如类型安全）。例如，证明 "如果 `e` 的类型是 `number`，那么 `e` 在运行时求值的结果确实是一个数字"。

- **控制流图 (Control Flow Graphs - CFG):**
  - **概念:** 一种图形表示，其中节点代表基本块（顺序执行的指令序列，只有一个入口和一个出口），边代表可能的执行转移（如跳转、函数调用、条件分支）。
  - **用途:** 用于编译器优化（如死代码消除、寄存器分配）、静态分析（如可达性分析）。
  - **TypeScript 示例:**

```typescript
function example(a: number): number { // Entry Node
    let x: number;                   // B1
    if (a > 0) {                     // B1 -> B2 (true), B1 -> B3 (false)
        x = a * 2;                   // B2
    } else {
        x = a / 2;                   // B3
    }                                // B2 -> B4, B3 -> B4
    return x;                        // B4 -> Exit Node
}
```

CFG 可视化：

```text
    [Entry]
        |
        v
    [B1: let x; a > 0?]
    /        \
    / (true)   \ (false)
    v            v
[B2: x = a*2]  [B3: x = a/2]
    \            /
    \          /
    v        v
    [B4: return x]
        |
        v
    [Exit]
```

- **数据流分析 (Data Flow Analysis - DFA):**
  - **概念:** 一组用于收集程序在执行过程中计算值的流动信息的静态分析技术。分析在 CFG 上进行。
  - **类型:**
    - **可达性定义 (Reaching Definitions):** 哪些变量的赋值（定义）可能到达程序的某个点？
    - **活性变量分析 (Live Variable Analysis):** 在程序的某个点之后，哪些变量的值可能会被使用？（用于死代码消除）
    - **可用表达式分析 (Available Expression Analysis):** 哪些表达式在程序的某个点已经被计算过，并且其操作数的值没有改变？（用于公共子表达式消除）
  - **TypeScript 中的应用:** 虽然开发者不直接进行 DFA，但 TypeScript 编译器和相关工具（如 Linter）可能使用类似技术进行优化、错误检测（如检测未使用的变量 - 基于活性分析）和代码理解。类型信息极大地帮助了数据流分析，因为类型限制了变量可能持有的值的范围和类型。
  - **示例 (活性变量):**

    ```typescript
    function liveExample(a: number) {
        let x = a + 1; // x is defined
        let y = 5;     // y is defined
        if (a > 0) {
            console.log(x); // x is live here
        } else {
            y = x + 1;   // x is live here, y is redefined
            console.log(y); // y is live here
        }
        // After the if/else, is y live? Depends on what follows.
        // If nothing follows, y is not live after the block where it's logged.
        // x might not be live after the if block if not used later.
    }
    ```

## 3. TypeScript 到 JavaScript 的转换 (Transformation)

TypeScript 代码通过 **TypeScript Compiler (tsc)** 转换为 JavaScript 代码。这个过程主要是**类型擦除 (Type Erasure)**。

- **编译过程：类型擦除 (Compilation: Type Erasure):**
  - **核心:** TypeScript 的类型注解、`interface`、`type` 别名等在编译后会被完全移除，不出现在最终的 JavaScript 代码中。
  - **原因:** JavaScript 运行时没有静态类型系统。TypeScript 的类型检查只发生在编译时。
  - **示例:**

    ```typescript
    // TypeScript
    function greet(name: string): void {
        console.log(`Hello, ${name}!`);
    }
    interface User { id: number; name: string; }
    let user: User = { id: 1, name: "Alice" };
    greet(user.name);
    ```

    编译为 JavaScript (ES5/ES6):

    ```javascript
    // JavaScript (target ES5)
    function greet(name) {
        console.log("Hello, " + name + "!");
    }
    // Interface User is gone
    var user = { id: 1, name: "Alice" }; // Type annotation is gone
    greet(user.name);
    ```

- **变量与作用域转换:**
  - `let` 和 `const` (块级作用域) 会被转换为目标 JavaScript 版本支持的等效语法。如果目标是 ES6 或更高版本，它们通常保持不变。如果目标是 ES5，`tsc` 会使用 `var` 结合函数闭包或重命名等技巧来模拟块级作用域。
  - 作用域规则（词法作用域）在转换后保持一致，因为 JavaScript 本身就是词法作用域。

    ```typescript
    // TypeScript
    if (true) {
        const blockConst = 1;
        let blockLet = 2;
        console.log(blockConst, blockLet);
    }
    ```

    编译为 JavaScript (target ES5):

    ```javascript
    // JavaScript (ES5) - Simplified example of potential transformation
    if (true) {
        var blockConst = 1; // Renamed/Scoped differently in reality
        var blockLet = 2;   // by tsc to avoid collisions
        console.log(blockConst, blockLet);
    }
    ```

- **类型转换:**
  - 如上所述，类型信息被**擦除**。
  - 枚举 (Enums) 是个例外，它们通常会被编译成一个 JavaScript 对象（或反向映射对象），以便在运行时可以访问枚举成员的值。

    ```typescript
    // TypeScript
    enum Direction { Up, Down, Left, Right }
    let dir: Direction = Direction.Up;
    ```

    编译为 JavaScript (target ES5):

    ```javascript
    // JavaScript (ES5)
    var Direction;
    (function (Direction) {
        Direction[Direction["Up"] = 0] = "Up";
        Direction[Direction["Down"] = 1] = "Down";
        Direction[Direction["Left"] = 2] = "Left";
        Direction[Direction["Right"] = 3] = "Right";
    })(Direction || (Direction = {}));
    var dir = Direction.Up; // dir is 0
    console.log(Direction[0]); // "Up"
    ```

- **控制流转换:**
  - 基本的控制流结构 (`if`, `switch`, `for`, `while`) 通常直接映射到等效的 JavaScript 结构。
  - TypeScript 特有的语法糖（如 `for...of` 在 ES5 目标下）会被转换为更兼容的循环结构。
  - 控制流图 (CFG) 的**结构**在转换前后基本保持一致。

- **执行流转换 (同步/异步):**
  - `async`/`await` 是 ES2017 的特性。如果编译目标低于 ES2017 (如 ES5, ES6/ES2015)，`tsc` 会将 `async` 函数转换为**状态机**，通常使用**生成器 (Generators)** (如果目标支持) 或复杂的**Promise 链**。
  - 这个转换保留了异步操作的**语义**，即非阻塞行为，但在底层实现上有所不同。

    ```typescript
    // TypeScript
    async function fetchData(url: string): Promise<string> {
        console.log("Fetching...");
        const response = await fetch(url); // Pause point
        const data = await response.text(); // Pause point
        console.log("Fetched");
        return data;
    }
    ```

    编译为 JavaScript (target ES5 - 概念性，实际更复杂):

    ```javascript
    // JavaScript (ES5) - Simplified concept using Promises
    function fetchData(url) {
        return new Promise(function (resolve, reject) {
            console.log("Fetching...");
            fetch(url)
                .then(function (response) {
                    return response.text(); // Chain the next async operation
                })
                .then(function (data) {
                    console.log("Fetched");
                    resolve(data); // Resolve the outer promise
                })
                .catch(function (err) {
                    reject(err); // Handle errors
                });
        });
    }
    // Or using generators if targeting ES6/ES2015
    // var _awaiter = ... (helper function)
    // function fetchData(url) {
    //    return _awaiter(this, void 0, void 0, function* () {
    //        console.log("Fetching...");
    //        const response = yield fetch(url);
    //        const data = yield response.text();
    //        console.log("Fetched");
    //        return data;
    //    });
    // }
    ```

- **双射转换讨论 (Bijective Transformation?):**
  - **定义:** 双射（Bijection）意味着一个一对一且映上的映射，存在一个逆映射可以将目标转换回源。
  - **TypeScript -> JavaScript:** 这个转换是**多对一 (Many-to-One)** 而**不是双射**。
    - **原因 1 (类型擦除):** 不同的 TypeScript 代码（例如，具有不同类型注解但逻辑相同的函数）可以编译成**完全相同**的 JavaScript 代码。丢失的类型信息无法从 JavaScript 代码中恢复。

        ```typescript
        // TS 1
        function process(val: number): void { console.log(val); }
        // TS 2
        function process(val: any): void { console.log(val); }
        // Both compile to JS:
        function process(val) { console.log(val); }
        ```

    - **原因 2 (编译目标):** 同一个 TypeScript 代码可以根据不同的编译目标 (ES5, ES6, ESNext) 编译成不同的 JavaScript 代码。
  - **结论:** 从 TypeScript 到 JavaScript 的转换是单向的编译过程，丢失了类型信息，因此不是双射。无法可靠地将任意 JavaScript 代码“反编译”回具有原始、精确类型信息的 TypeScript 代码。

## 4. 执行模型 (Execution Model)

TypeScript 代码最终作为 JavaScript 在 JavaScript 引擎（如 V8, SpiderMonkey）中执行。因此，其执行模型与 JavaScript 一致。

- **控制流、数据流、执行流:**
  - **控制流 (Control Flow):** 指令执行的顺序，由条件、循环、函数调用、`await` 等决定。在 JavaScript 中是单线程的（主线程）。
  - **数据流 (Data Flow):** 值如何在变量和表达式之间传递。TypeScript 的类型系统在编译时帮助理解和验证数据流，但在运行时，数据流遵循 JavaScript 的动态类型规则（尽管编译后的代码逻辑通常确保类型符合预期）。
  - **执行流 (Execution Flow):** 代码如何被引擎实际处理。对于同步代码，按顺序执行。对于异步代码，涉及事件循环、回调队列、微任务队列等机制。

- **同步与异步机制 (Sync/Async Mechanisms):**
  - **同步 (Synchronous):** 操作阻塞主线程，直到完成。例如，一个复杂的计算循环。
  - **异步 (Asynchronous):** 操作不阻塞主线程，允许其他代码（如图形渲染、用户交互）继续执行。结果在未来某个时间点通过回调、Promise 或 `async/await` 返回。
  - **核心机制 (JavaScript Runtime):**
    - **调用栈 (Call Stack):** 跟踪函数调用。同步代码执行时，函数压栈，返回时弹栈。
    - **Web APIs / Node APIs:** 处理 I/O、定时器 (`setTimeout`) 等异步操作的环境（浏览器或 Node.js）。这些 API 在后台处理任务。
    - **任务队列 (Task Queue / Callback Queue):** 存放来自 Web APIs 的已完成异步操作的回调函数。
    - **微任务队列 (Microtask Queue):** 存放 Promise 回调 (`.then`, `.catch`, `.finally`) 和 `queueMicrotask` 的回调。微任务优先级高于宏任务（Task Queue）。
    - **事件循环 (Event Loop):** 持续监控调用栈和任务/微任务队列。当调用栈为空时，它会先清空微任务队列，然后取出一个宏任务（如果存在）压入调用栈执行。

    ```typescript
    console.log("Start"); // 1. Sync - Logged first

    setTimeout(() => {
        console.log("Timeout Callback"); // 5. Macro Task - Logged last
    }, 0);

    Promise.resolve().then(() => {
        console.log("Promise Resolved"); // 3. Micro Task - Logged third
    });

    console.log("End"); // 2. Sync - Logged second

    // Expected Output:
    // Start
    // End
    // Promise Resolved
    // Timeout Callback
    ```

    TypeScript 的 `async/await` 语法糖极大地简化了基于 Promise 的异步代码的编写和阅读，但底层仍然依赖于事件循环和 Promise 机制。

## 5. 总结与思维导图

TypeScript 通过引入强大的静态类型系统，极大地增强了 JavaScript 的开发体验和代码健壮性，尤其是在大型项目中。它在编译时进行类型检查并将类型信息擦除，生成可在任何标准 JavaScript 环境中运行的代码。其核心概念围绕变量、类型、控制流和作用域展开，并且与 JavaScript 共享相同的词法作用域和基于事件循环的异步执行模型。理解 TypeScript 到 JavaScript 的转换过程（主要是类型擦除和对新语法的降级编译）对于深入掌握 TypeScript 至关重要。

---

**思维导图 (Text Format):**

```text
TypeScript Analysis
├── Core Concepts
│   ├── Variables
│   │   ├── Declaration (let, const, var)
│   │   └── Scope (Static/Lexical)
│   ├── Type System
│   │   ├── Static Typing (Compile-time checks)
│   │   ├── Basic Types (number, string, boolean, ...)
│   │   ├── Advanced Types (interface, type, union, intersection, generics, ...)
│   │   ├── Type Inference
│   │   └── Type Compatibility (Structural/Duck Typing)
│   ├── Control Flow
│   │   ├── Statements
│   │   ├── Conditionals (if, switch)
│   │   ├── Loops (for, while, for...of, for...in)
│   │   └── Control Transfer (break, continue, return, throw)
│   ├── Syntax vs. Semantics
│   │   ├── Syntax (Grammar, AST)
│   │   └── Semantics (Meaning: Static - Types, Dynamic - Runtime Behavior)
│   └── Scope Deep Dive
│       ├── Static/Lexical Scope (Definition-time binding)
│       └── Dynamic Scope (Call-time binding - Contrast, not used in TS/JS)
├── Formal Perspectives
│   ├── Type System Formalization (Rules, Judgements, Structural, Gradual)
│   ├── Control Flow Graphs (CFG) (Nodes=Basic Blocks, Edges=Transfers)
│   └── Data Flow Analysis (DFA) (Reaching Defs, Liveness, Available Exprs)
├── TS -> JS Transformation
│   ├── Compiler (tsc)
│   ├── Type Erasure (Interfaces, Type Annotations removed)
│   ├── Variable/Scope Conversion (let/const -> var for older targets)
│   ├── Type Conversion (Enums -> JS Objects)
│   ├── Control Flow Preservation (if/loops map directly)
│   ├── Execution Flow Conversion (async/await -> Generators/Promises)
│   └── Not Bijective (Many-to-one, Info Loss)
└── Execution Model (Same as JavaScript)
    ├── Runtime Engine (V8, etc.)
    ├── Single Threaded (Main Thread)
    ├── Control Flow (Execution Order)
    ├── Data Flow (Value Propagation)
    ├── Execution Flow (Stack, Queues, Loop)
    └── Sync/Async Mechanisms
        ├── Call Stack
        ├── Web/Node APIs
        ├── Task Queue (Macro tasks - setTimeout, I/O)
        ├── Microtask Queue (Promise callbacks)
        └── Event Loop
```
