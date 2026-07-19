# C++编程语言分析

## 目录

- [C++编程语言分析](#c编程语言分析)
  - [目录](#目录)
  - [思维导图 (Text)](#思维导图-text)
  - [1. 变量、类型、控制、语法与语义](#1-变量类型控制语法与语义)
    - [1.1 变量](#11-变量)
      - [概念定义](#概念定义)
      - [变量类别](#变量类别)
      - [形式化表示](#形式化表示)
    - [1.2 类型](#12-类型)
      - [类型系统特质](#类型系统特质)
      - [类型分类](#类型分类)
        - [基本类型](#基本类型)
        - [复合类型](#复合类型)
        - [函数类型](#函数类型)
      - [范畴论视角下的类型](#范畴论视角下的类型)
      - [类型安全与型变](#类型安全与型变)
    - [1.3 控制流](#13-控制流)
      - [1.3.1 控制结构](#131-控制结构)
      - [1.3.2 形式化定义](#132-形式化定义)
    - [1.4 语法与语义](#14-语法与语义)
      - [1.4.1 语法](#141-语法)
      - [1.4.2 语义](#142-语义)
    - [1.5 作用域](#15-作用域)
      - [1.5.1 作用域类型](#151-作用域类型)
      - [1.5.2 作用域链与名称查找](#152-作用域链与名称查找)
    - [1.6 形式化证明](#16-形式化证明)
      - [1.6.1 类型系统的形式化](#161-类型系统的形式化)
      - [1.6.2 霍尔逻辑](#162-霍尔逻辑)
  - [2. 控制流、数据流、执行流与语义](#2-控制流数据流执行流与语义)
    - [2.1 控制流分析](#21-控制流分析)
      - [2.1.1 控制流表示](#211-控制流表示)
      - [2.1.2 控制结构形式化](#212-控制结构形式化)
      - [2.1.3 控制流分析技术](#213-控制流分析技术)
    - [2.2 数据流分析](#22-数据流分析)
      - [2.2.1 数据流概念](#221-数据流概念)
      - [2.2.2 数据依赖关系](#222-数据依赖关系)
      - [2.2.3 数据流分析应用](#223-数据流分析应用)
    - [2.3 执行流分析](#23-执行流分析)
      - [2.3.1 执行模型](#231-执行模型)
      - [2.3.2 执行状态与转换](#232-执行状态与转换)
      - [2.3.4 调用栈机制](#234-调用栈机制)
    - [2.4 同步与异步机制](#24-同步与异步机制)
      - [同步执行](#同步执行)
      - [异步执行](#异步执行)
    - [2.5 形式化验证](#25-形式化验证)
      - [形式化方法](#形式化方法)
      - [不变量与断言](#不变量与断言)
      - [形式化证明技术](#形式化证明技术)
  - [3. 类型系统的深层分析](#3-类型系统的深层分析)
    - [3.1 类型的代数结构](#31-类型的代数结构)
      - [代数数据类型](#代数数据类型)
      - [范畴论解读](#范畴论解读)
    - [3.2 类型转换机制](#32-类型转换机制)
      - [隐式类型转换](#隐式类型转换)
      - [显式类型转换](#显式类型转换)
      - [形式化分析](#形式化分析)
    - [3.3 模板与泛型编程](#33-模板与泛型编程)
      - [模板机制](#模板机制)
      - [模板特化与SFINAE](#模板特化与sfinae)
      - [范畴论视角](#范畴论视角)
    - [3.4 类型推导](#34-类型推导)
      - [类型推导机制](#类型推导机制)
      - [类型推导规则](#类型推导规则)
  - [4. 面向对象编程的形式化分析](#4-面向对象编程的形式化分析)
    - [4.1 封装与抽象](#41-封装与抽象)
      - [4.1.1 封装机制](#411-封装机制)
      - [4.1.2 形式化定义](#412-形式化定义)
    - [4.2 继承与多态](#42-继承与多态)
      - [4.2.1 继承类型](#421-继承类型)
      - [4.2.2 多态机制](#422-多态机制)
      - [4.2.3 形式化分析](#423-形式化分析)
    - [4.3 组合与聚合](#43-组合与聚合)
      - [组合关系](#组合关系)
      - [设计模式中的应用](#设计模式中的应用)
    - [4.4 SOLID原则](#44-solid原则)
      - [单一责任原则 (SRP)](#单一责任原则-srp)
      - [开放封闭原则 (OCP)](#开放封闭原则-ocp)
      - [里氏替换原则 (LSP)](#里氏替换原则-lsp)
      - [接口隔离原则 (ISP)](#接口隔离原则-isp)
      - [依赖倒置原则 (DIP)](#依赖倒置原则-dip)
  - [5. 内存管理与资源控制](#5-内存管理与资源控制)
    - [5.1 内存模型](#51-内存模型)
      - [C++内存布局](#c内存布局)
      - [对象内存布局](#对象内存布局)
    - [5.2 动态内存管理](#52-动态内存管理)
      - [5.2.1 内存分配机制](#521-内存分配机制)
      - [5.2.2 内存管理问题](#522-内存管理问题)
      - [5.2.3 形式化分析](#523-形式化分析)
    - [5.3 智能指针与所有权](#53-智能指针与所有权)
      - [5.3.1 智能指针类型](#531-智能指针类型)
      - [5.3.2 所有权模型](#532-所有权模型)
      - [5.3.3 形式化定义](#533-形式化定义)
    - [5.4 RAII范式](#54-raii范式)
      - [5.4.1 RAII核心概念](#541-raii核心概念)
      - [5.4.2 RAII应用](#542-raii应用)
      - [5.4.3 形式化分析](#543-形式化分析)
  - [6. 并发与同步模型](#6-并发与同步模型)
    - [6.1 线程模型](#61-线程模型)
      - [C++线程库](#c线程库)
      - [线程生命周期](#线程生命周期)
    - [6.2 同步原语](#62-同步原语)
      - [互斥与锁](#互斥与锁)
      - [条件变量](#条件变量)
      - [同步形式化](#同步形式化)
    - [6.3 内存序与原子操作](#63-内存序与原子操作)
      - [6.3.1 原子操作](#631-原子操作)
      - [6.3.2 内存序模型](#632-内存序模型)
      - [6.3.3 形式化定义](#633-形式化定义)
    - [6.4 并发模式](#64-并发模式)
      - [常见并发模式](#常见并发模式)
      - [并发安全技术](#并发安全技术)
  - [7. 类型特质与元编程](#7-类型特质与元编程)
    - [7.1 类型特质](#71-类型特质)
      - [类型特质机制](#类型特质机制)
      - [类型特质应用](#类型特质应用)
    - [7.2 模板元编程](#72-模板元编程)
      - [编译期计算](#编译期计算)
      - [编译期算法](#编译期算法)
    - [7.3 标签分派与特化](#73-标签分派与特化)
      - [标签分派技术](#标签分派技术)
      - [特化技术](#特化技术)
  - [8. 函数式编程特质](#8-函数式编程特质)
    - [8.1 Lambda表达式](#81-lambda表达式)
      - [Lambda语法与特质](#lambda语法与特质)
      - [Lambda底层原理](#lambda底层原理)
    - [8.2 高阶函数](#82-高阶函数)
      - [高阶函数概念](#高阶函数概念)
      - [C++中的实现](#c中的实现)
    - [8.3 范畴论视角的函子与单子](#83-范畴论视角的函子与单子)
      - [函子概念](#函子概念)
      - [单子模式](#单子模式)
  - [9. 形式语义与验证](#9-形式语义与验证)
    - [9.1 操作语义](#91-操作语义)
      - [形式语义模型](#形式语义模型)
      - [C++语句语义](#c语句语义)
    - [9.2 类型安全与约束](#92-类型安全与约束)
      - [9.2.1 类型安全机制](#921-类型安全机制)
      - [9.2.2 形式化定义](#922-形式化定义)
    - [9.3 程序验证](#93-程序验证)
      - [9.3.1 验证技术](#931-验证技术)
      - [9.3.2 形式化证明](#932-形式化证明)
  - [10. 总结与前沿发展](#10-总结与前沿发展)
    - [10.1 C++类型系统总结](#101-c类型系统总结)
      - [关键特质](#关键特质)
      - [优缺点分析](#优缺点分析)
    - [10.2 前沿发展](#102-前沿发展)
      - [现代C++特质](#现代c特质)
      - [与其他语言的对比](#与其他语言的对比)
    - [10.3 实际应用与最佳实践](#103-实际应用与最佳实践)
      - [工程实践](#工程实践)
      - [性能优化](#性能优化)
  - [11. C++20/23新特质深入分析](#11-c2023新特质深入分析)
    - [11.1 概念与约束](#111-概念与约束)
      - [概念机制](#概念机制)
      - [核心概念](#核心概念)
    - [11.2 协程机制](#112-协程机制)
      - [协程基础](#协程基础)
      - [协程组件](#协程组件)
    - [11.3 模块系统](#113-模块系统)
      - [模块基础](#模块基础)
      - [模块组件](#模块组件)
    - [11.4 范围与视图](#114-范围与视图)
      - [范围库](#范围库)
      - [主要特质](#主要特质)
    - [11.5 格式库](#115-格式库)
      - [11.5.1 格式库基础](#1151-格式库基础)
      - [11.5.2 主要特质](#1152-主要特质)
  - [12. 特定领域C++应用](#12-特定领域c应用)
    - [12.1 嵌入式系统](#121-嵌入式系统)
      - [嵌入式C++特点](#嵌入式c特点)
      - [嵌入式编程技术](#嵌入式编程技术)
    - [12.2 游戏开发](#122-游戏开发)
      - [游戏引擎设计](#游戏引擎设计)
      - [游戏开发技术](#游戏开发技术)
    - [12.3 高性能计算](#123-高性能计算)
      - [高性能计算特点](#高性能计算特点)
      - [HPC技术](#hpc技术)
    - [12.4 金融系统](#124-金融系统)
      - [金融软件特质](#金融软件特质)
      - [金融编程技术](#金融编程技术)
  - [13. C++系统级编程](#13-c系统级编程)
    - [13.1 与操作系统交互](#131-与操作系统交互)
      - [系统接口封装](#系统接口封装)
    - [13.2 内存映射](#132-内存映射)
      - [内存映射文件](#内存映射文件)
    - [13.3 系统调用封装](#133-系统调用封装)
      - [系统调用接口](#系统调用接口)
    - [13.4 进程与线程管理](#134-进程与线程管理)
      - [进程管理](#进程管理)
      - [线程管理](#线程管理)
  - [14. 高级设计模式与实践](#14-高级设计模式与实践)
    - [14.1 现代C++设计模式](#141-现代c设计模式)
      - [经典设计模式的C++实现](#经典设计模式的c实现)
      - [现代C++特质优化](#现代c特质优化)
    - [14.2 C++中的函数式模式](#142-c中的函数式模式)
      - [函数式编程概念](#函数式编程概念)
      - [C++实现](#c实现)
    - [14.3 元编程设计模式](#143-元编程设计模式)
      - [模板元编程技术](#模板元编程技术)
      - [元编程模式](#元编程模式)
    - [14.4 性能优化模式](#144-性能优化模式)
      - [性能关键模式](#性能关键模式)
      - [常见优化实践](#常见优化实践)
  - [C++编程语言分析总结](#c编程语言分析总结)

## 思维导图 (Text)

```text
C++语言分析
├── 变量、类型、控制
│   ├── 变量
│   │   ├── 定义：命名的内存位置
│   │   ├── 作用域：局部、全局、命名空间
│   │   ├── 存储类：auto、static、extern
│   │   └── 可变性：const、mutable、volatile
│   ├── 类型
│   │   ├── 基本类型：整型、浮点型、字符、布尔
│   │   ├── 复合类型：数组、结构体、类、联合、枚举
│   │   ├── 指针与借用
│   │   ├── 函数类型
│   │   ├── 类型安全：强类型、静态类型检查
│   │   └── 类型代数：积类型、和类型、指数类型
│   └── 控制
│       ├── 条件语句：if-else、switch
│       ├── 循环：for、while、do-while
│       ├── 跳转：break、continue、return、goto
│       ├── 异常处理：try-catch-throw
│       └── 函数调用与返回
├── 控制流、数据流、执行流
│   ├── 控制流
│   │   ├── 有向图表示
│   │   ├── 顺序、分支、循环
│   │   ├── 递归与迭代
│   │   └── 控制流分析：CFG、优化
│   ├── 数据流
│   │   ├── 变量定义与使用
│   │   ├── 数据依赖关系
│   │   ├── 数据流分析：活跃变量、常量传播
│   │   └── 内存模型与可见性
│   ├── 执行流
│   │   ├── 指令级执行
│   │   ├── 函数调用栈
│   │   ├── 异步执行模型
│   │   └── 并发与并发
│   └── 同步异步机制
│       ├── 线程：std::thread
│       ├── 互斥与同步：mutex、condition_variable
│       ├── 原子操作：atomic
│       ├── 期物与承诺：future、promise
│       └── 异步任务：async、packaged_task
└── 形式化验证
    ├── 语法分析
    ├── 类型检查
    ├── 静态分析
    ├── 形式化证明
    └── 不变量与断言
```

## 1. 变量、类型、控制、语法与语义

### 1.1 变量

#### 概念定义

- **变量**：在C++中，变量是命名的内存位置，用于存储程序数据
- **生命周期**：从变量创建到销毁的时间段，受作用域和存储类限制
- **定义与声明**：定义分配存储空间，声明告知编译器变量存在

#### 变量类别

- **自动变量**：默认存储类，局部作用域内自动创建和销毁
- **静态变量**：程序执行期间保持存在，保留状态
- **线程局部变量**：每个线程拥有独立副本
- **寄存器变量**：建议存储在寄存器中（现代编译器通常忽略）

#### 形式化表示

在形式化上，可以定义变量为内存状态映射：

- 设 V 为变量标识符集合，A 为内存地址集合，T 为类型集合
- 变量定义函数：var: V → A，将变量名映射到内存地址
- 类型函数：type: V → T，将变量映射到其类型

```cpp
int x = 10;       // 自动变量，局部作用域
static int y = 5; // 静态变量，保持状态
thread_local int z = 1; // 线程局部存储
```

### 1.2 类型

#### 类型系统特质

- **静态类型**：变量类型在编译时确定
- **强类型**：类型错误在编译时检测，隐式转换受限
- **显式/隐式转换**：支持显式类型转换与有限的安全隐式转换

#### 类型分类

##### 基本类型

- **整型**：`char`、`short`、`int`、`long`、`long long`
- **浮点型**：`float`、`double`、`long double`
- **字符**：`char`、`wchar_t`、`char16_t`、`char32_t`
- **布尔**：`bool`

##### 复合类型

- **数组**：`T[N]`，固定大小的同类型元素序列
- **指针**：`T*`，存储内存地址的变量
- **借用**：`T&`，变量别名，借用不变性
- **结构体**：`struct`，不同类型数据的集合（积类型）
- **类**：`class`，带成员函数的数据结构
- **联合**：`union`，共享内存的多类型（不安全的和类型）
- **枚举**：`enum`，命名的整型常量集合

##### 函数类型

- **函数**：`R(T1, T2, ...)`，接受参数返回结果的计算单元
- **函数指针**：`R(*)(T1, T2, ...)`，指向函数的指针
- **函数对象**：重载函数调用运算符的类实例
- **Lambda表达式**：匿名函数对象

#### 范畴论视角下的类型

- **类型作为范畴中的对象**：每种类型是一个对象
- **函数作为态射**：函数 `f: A → B` 是从类型A到类型B的态射
- **积类型**：结构体、类、`std::pair`、`std::tuple`表示类型乘积
- **和类型**：`union`、`std::variant`、继承层次表示类型之和
- **指数类型**：函数类型 `B^A` 表示从A到B的所有函数

```cpp
// 积类型示例
struct Point {
    double x;
    double y;
}; // 相当于 double × double

// 和类型示例
std::variant<int, std::string> v; // 相当于 int + std::string

// 指数类型示例
std::function<std::string(int)> f; // 相当于 string^int
```

#### 类型安全与型变

- **型变分类**：
  - **不变（invariant）**：如`std::vector<T>`、`T&`
  - **协变（covariant）**：如指针`T*`、返回类型
  - **逆变（contravariant）**：如函数参数
- **类型安全保证**：编译时检查防止非法操作

### 1.3 控制流

#### 1.3.1 控制结构

- **顺序执行**：按代码顺序执行语句
- **条件分支**：
  - `if-else`：基于条件选择执行路径
  - `switch-case`：多路分支选择
- **循环**：
  - `for`：初始化、条件、迭代三部分组成
  - `while`：条件为真时循环
  - `do-while`：至少执行一次的条件循环
- **跳转**：
  - `break`：跳出循环或switch
  - `continue`：跳过循环当前迭代
  - `return`：从函数返回
  - `goto`：无条件跳转（不推荐使用）

#### 1.3.2 形式化定义

- **控制流图（CFG）**：G = (V, E)，其中 V是基本块集合，E是控制转移边
- **路径**：从入口到出口的执行序列

```cpp
// 条件控制示例
int max(int a, int b) {
    if (a > b) {
        return a;
    } else {
        return b;
    }
}

// 循环控制示例
int sum(int n) {
    int result = 0;
    for (int i = 1; i <= n; i++) {
        result += i;
    }
    return result;
}
```

### 1.4 语法与语义

#### 1.4.1 语法

- **词法**：关键字、标识符、运算符、字面量等基本单元
- **语法规则**：C++语言构造的形式化规则

#### 1.4.2 语义

- **静态语义**：编译时可确定的含义（类型检查）
- **动态语义**：运行时确定的含义（执行行为）
- **操作语义**：定义程序执行如何改变状态

```cpp
// 语法示例：合法但语义错误
int* p = nullptr;
*p = 10; // 语法正确，但有未定义行为
```

### 1.5 作用域

#### 1.5.1 作用域类型

- **块作用域**：大括号内的局部变量
- **函数作用域**：函数内的标签
- **文件作用域**：全局变量和函数
- **类作用域**：类成员
- **命名空间作用域**：命名空间内的声明

#### 1.5.2 作用域链与名称查找

- **名称查找过程**：从最内层作用域开始，逐层向外查找
- **名称隐藏**：内层声明隐藏外层同名声明

```cpp
int x = 1; // 全局作用域

void func() {
    int x = 2; // 局部作用域，隐藏全局x
    {
        int x = 3; // 嵌套块作用域，隐藏外层x
        std::cout << x; // 输出3
    }
    std::cout << x; // 输出2
}
```

### 1.6 形式化证明

#### 1.6.1 类型系统的形式化

- **类型规则**：定义何时表达式具有特定类型
- **进度定理**：形式化证明"良好类型的程序不会卡住"
- **类型安全定理**：形式化证明"良好类型的程序不会陷入未定义状态"

#### 1.6.2 霍尔逻辑

- **霍尔三元组**：{P} S {Q}，表示前置条件P下执行语句S后，后置条件Q成立
- **循环不变量**：循环各次迭代之间保持不变的条件

```cpp
// 形式化证明示例
// {n >= 0}
int factorial(int n) {
    // 循环不变量：result = k!
    int result = 1;
    for (int k = 1; k <= n; k++) {
        result *= k;
    }
    return result;
}
// {result = n!}
```

## 2. 控制流、数据流、执行流与语义

### 2.1 控制流分析

#### 2.1.1 控制流表示

- **控制流图（CFG）**：程序的流程图表示
  - 节点：基本块（无分支的代码序列）
  - 边：可能的控制转移

#### 2.1.2 控制结构形式化

- **顺序**：A; B（执行A后执行B）
- **选择**：if C then A else B（根据C选择A或B）
- **循环**：while C do A（当C为真时重复执行A）

#### 2.1.3 控制流分析技术

- **可达性分析**：确定代码是否可执行
- **循环分析**：识别和优化循环结构
- **分支预测**：优化条件分支执行

```cpp
// 控制流分析示例
int binary_search(int arr[], int n, int target) {
    int left = 0, right = n - 1;
    while (left <= right) {        // 循环头
        int mid = left + (right - left) / 2;
        if (arr[mid] == target) {  // 分支1
            return mid;
        } else if (arr[mid] < target) { // 分支2
            left = mid + 1;
        } else {                   // 分支3
            right = mid - 1;
        }
    }
    return -1;
}
// 这段代码的控制流图包含多个基本块和条件分支
```

### 2.2 数据流分析

#### 2.2.1 数据流概念

- **定义-使用链**：变量定义与使用之间的关系
- **活跃变量**：当前值在未来可能被使用的变量
- **到达定义**：可能影响程序点变量值的定义

#### 2.2.2 数据依赖关系

- **数据依赖**：一条语句使用另一条语句定义的变量
- **控制依赖**：一条语句的执行依赖于另一条语句的条件

#### 2.2.3 数据流分析应用

- **死代码消除**：删除无效果的代码
- **常量传播**：编译时计算常量表达式
- **变量活跃期分析**：优化寄存器分配

```cpp
// 数据流分析示例
void data_flow_example() {
    int x = 10;     // x的定义
    int y = x + 5;  // 使用x定义y
    if (y > 20) {   // 使用y
        x = 20;     // x的重定义，但这个分支不会执行
    }
    int z = x + 1;  // 使用x，x = 10
} // x、y、z在此处不再活跃
```

### 2.3 执行流分析

#### 2.3.1 执行模型

- **顺序执行**：单线程按指令顺序执行
- **并发执行**：多线程并发执行，可能交错
- **并发执行**：多处理器同时执行指令

#### 2.3.2 执行状态与转换

- **程序状态**：包括所有变量值、控制点的快照
- **状态转换**：执行指令导致状态变化

#### 2.3.4 调用栈机制

- **函数调用过程**：参数压栈、保存返回地址、跳转
- **栈帧**：包含局部变量、参数、返回地址的内存区域

```cpp
// 执行流示例：递归函数的调用栈
int factorial(int n) {
    // 栈帧：保存n、返回地址
    if (n <= 1) {
        return 1;
    }
    // 递归调用：创建新栈帧
    return n * factorial(n - 1);
}
```

### 2.4 同步与异步机制

#### 同步执行

- **阻塞操作**：当前线程等待操作完成
- **锁与互斥**：使用`std::mutex`保护共享资源

#### 异步执行

- **线程**：使用`std::thread`创建并发执行单元
- **期物与承诺**：使用`std::future`和`std::promise`处理异步结果
- **异步任务**：使用`std::async`启动异步操作

```cpp
// 异步执行示例
# include <future>
# include <iostream>

int compute_value() {
    // 耗时计算
    std::this_thread::sleep_for(std::chrono::seconds(2));
    return 42;
}

void async_example() {
    // 启动异步任务
    std::future<int> result = std::async(std::launch::async, compute_value);
    
    // 做其他工作
    std::cout << "等待计算结果...\n";
    
    // 获取结果（如果尚未完成会阻塞）
    int value = result.get();
    std::cout << "结果: " << value << "\n";
}
```

### 2.5 形式化验证

#### 形式化方法

- **类型检查**：确保操作类型安全
- **静态分析**：在编译时检测潜在问题
- **符号执行**：以符号形式执行程序，探索所有路径
- **模型检验**：验证系统是否满足形式化规范

#### 不变量与断言

- **程序不变量**：代码执行过程中始终保持的条件
- **断言**：使用`assert`检查运行时条件

#### 形式化证明技术

- **归纳法证明**：循环与递归的正确性证明
- **霍尔逻辑**：基于前置和后置条件的程序证明

```cpp
// 形式化验证示例
# include <cassert>

// 使用循环不变量证明排序正确性
void bubble_sort(int arr[], int n) {
    for (int i = 0; i < n - 1; i++) {
        // 循环不变量：arr[0..i-1]已排序且不大于arr[i..n-1]中的任何元素
        for (int j = n - 1; j > i; j--) {
            if (arr[j] < arr[j-1]) {
                std::swap(arr[j], arr[j-1]);
            }
        }
        // 不变量仍然成立：arr[0..i]已排序且不大于arr[i+1..n-1]中的任何元素
    }
    // 终止时：arr[0..n-1]已排序
}

void verify_sort() {
    int arr[] = {5, 2, 9, 1, 5, 6};
    int n = sizeof(arr) / sizeof(arr[0]);
    
    bubble_sort(arr, n);
    
    // 验证排序结果
    for (int i = 0; i < n - 1; i++) {
        assert(arr[i] <= arr[i+1]); // 形式化验证排序正确性
    }
}
```

## 3. 类型系统的深层分析

### 3.1 类型的代数结构

#### 代数数据类型

- **积类型**：类似于笛卡尔积，组合多个值
  - 结构体、类、`std::pair`、`std::tuple`
  - 形式化：`T₁ × T₂ = {(a, b) | a ∈ T₁, b ∈ T₂}`
- **和类型**：类似于不相交并集
  - `union`、`std::variant`、继承层次
  - 形式化：`T₁ + T₂ = {(0, a) | a ∈ T₁} ∪ {(1, b) | b ∈ T₂}`
- **指数类型**：函数类型
  - 函数指针、函数对象、Lambda表达式
  - 形式化：`T₂^T₁ = {f | f: T₁ → T₂}`

```cpp
// 积类型示例
struct Person {
    std::string name;  // string类型
    int age;           // int类型
}; // Person = string × int

// 和类型示例
std::variant<int, double, std::string> v;
// v = int + double + string

// 指数类型示例
std::function<int(double, char)> f;
// f ∈ int^(double×char)
```

#### 范畴论解读

- **类型作为对象**：范畴中的对象
- **函数作为态射**：对象间的映射
- **函数组合**：态射组合
- **恒等函数**：恒等态射

```cpp
// 函数组合示例
std::string intToString(int i) { return std::to_string(i); }
int stringLength(const std::string& s) { return s.length(); }

// 组合函数：f ∘ g
auto composed = [](int i) { return stringLength(intToString(i)); };
// 等价于 int -> string -> int 的组合态射
```

### 3.2 类型转换机制

#### 隐式类型转换

- **数值提升**：如`char`到`int`
- **数值转换**：如`int`到`double`
- **用户定义转换**：转换构造函数和转换运算符

#### 显式类型转换

- **C风格转换**：`(type)expression`
- **C++风格转换**：
  - `static_cast<T>`：编译时类型检查的转换
  - `dynamic_cast<T>`：运行时类型安全的向下转换
  - `const_cast<T>`：添加或移除`const`修饰符
  - `reinterpret_cast<T>`：底层重新解释，类型不安全

#### 形式化分析

- **安全转换**：不丢失信息的转换（如`int`到`double`）
- **不安全转换**：可能丢失信息的转换（如`double`到`int`）
- **类型转换作为映射**：f: T₁ → T₂，但可能不是单射或满射

```cpp
// 类型转换示例
int i = 42;
double d = i;     // 隐式安全转换
int j = static_cast<int>(3.14); // 显式不安全转换，丢失小数部分

class Number {
    int value;
public:
    Number(int v) : value(v) {} // 转换构造函数
    operator double() const { return value; } // 转换运算符
};

Number n = 10;    // 隐式转换：int -> Number
double d2 = n;    // 隐式转换：Number -> double
```

### 3.3 模板与泛型编程

#### 模板机制

- **函数模板**：参数化的函数
- **类模板**：参数化的类
- **变量模板**：参数化的变量
- **别名模板**：参数化的类型别名

#### 模板特化与SFINAE

- **特化**：为特定类型提供专门实现
- **偏特化**：为类型模式提供专门实现
- **SFINAE**：替换失败不是错误，实现编译时分派

#### 范畴论视角

- **模板作为高阶函子**：类型到类型的映射的参数化
- **类型约束作为子类别**：限制可接受的类型范围

```cpp
// 模板示例
template<typename T>
T max(T a, T b) {
    return (a > b) ? a : b;
}

// 类模板与特化
template<typename T>
class Container {
    T data;
public:
    void store(T value) { data = value; }
    T retrieve() const { return data; }
};

// 模板特化
template<>
class Container<bool> {
    unsigned char data : 1;
public:
    void store(bool value) { data = value ? 1 : 0; }
    bool retrieve() const { return data == 1; }
};

// SFINAE示例
template<typename T>
typename std::enable_if<std::is_integral<T>::value, bool>::type
is_even(T t) { return t % 2 == 0; }

template<typename T>
typename std::enable_if<!std::is_integral<T>::value, bool>::type
is_even(T) { return false; } // 非整型始终返回false
```

### 3.4 类型推导

#### 类型推导机制

- **自动类型推导**：使用`auto`关键字
- **模板参数推导**：函数模板的参数类型推导
- **`decltype`表达式**：获取表达式的精确类型
- **`decltype(auto)`**：保留借用和CV限定符

#### 类型推导规则

- **值类别**：左值、右值、纯右值、将亡值
- **CV限定符**：const、volatile修饰符
- **借用折叠**：借用的借用规则

```cpp
// 类型推导示例
int i = 42;
const int& ri = i;

auto a = i;          // a是int
auto b = ri;         // b是int（丢弃了const和借用）
const auto& c = i;   // c是const int&
decltype(i) d = 0;   // d是int
decltype(ri) e = i;  // e是const int&
decltype(i + 1) f;   // f是int
decltype(auto) g = ri; // g是const int&（保留了借用）

// 模板参数推导
template<typename T>
void func(T param);

func(42);   // T推导为int
func(ri);   // T推导为int（传值参数）

template<typename T>
void func_ref(T& param);

func_ref(i); // T推导为int
func_ref(ri); // T推导为const int
```

## 4. 面向对象编程的形式化分析

### 4.1 封装与抽象

#### 4.1.1 封装机制

- **访问控制**：public、protected、private
- **抽象数据类型**：数据与操作的绑定
- **实现隐藏**：接口与实现分离

#### 4.1.2 形式化定义

- **抽象与约束**：通过接口约束实现
- **信息隐藏**：限制状态直接访问
- **不变量维护**：保证对象内部状态一致性

```cpp
// 封装示例
class BankAccount {
private:
    double balance;  // 私有状态
    
    // 不变量：balance >= 0
    void validateTransaction(double amount) {
        if (balance + amount < 0) {
            throw std::invalid_argument("Insufficient funds");
        }
    }
    
public:
    BankAccount(double initialBalance = 0) : balance(initialBalance) {
        if (initialBalance < 0) {
            throw std::invalid_argument("Initial balance cannot be negative");
        }
    }
    
    void deposit(double amount) {
        if (amount <= 0) {
            throw std::invalid_argument("Deposit amount must be positive");
        }
        balance += amount;
    }
    
    void withdraw(double amount) {
        if (amount <= 0) {
            throw std::invalid_argument("Withdrawal amount must be positive");
        }
        validateTransaction(-amount);
        balance -= amount;
    }
    
    double getBalance() const {
        return balance;
    }
};
```

### 4.2 继承与多态

#### 4.2.1 继承类型

- **公有继承**：is-a关系，子类型多态
- **保护继承**：限制外部访问基类接口
- **私有继承**：实现继承，不建立子类型关系
- **多重继承**：从多个基类继承
- **虚拟继承**：解决菱形继承问题

#### 4.2.2 多态机制

- **静态多态**：编译时通过重载解析
- **动态多态**：运行时通过虚函数表实现
- **接口抽象**：纯虚函数定义接口

#### 4.2.3 形式化分析

- **子类型关系**：S <: T 表示S是T的子类型
- **里氏替换原则**：子类型必须能够替换其基类型
- **虚函数表**：动态分派的实现机制

```cpp
// 继承与多态示例
class Shape {
public:
    virtual ~Shape() = default;  // 虚析构函数
    virtual double area() const = 0;  // 纯虚函数
    virtual void draw() const {
        std::cout << "Drawing a shape\n";
    }
};

class Circle : public Shape {
private:
    double radius;
    
public:
    Circle(double r) : radius(r) {}
    
    double area() const override {
        return 3.14159 * radius * radius;
    }
    
    void draw() const override {
        std::cout << "Drawing a circle with radius " << radius << "\n";
    }
};

class Rectangle : public Shape {
private:
    double width, height;
    
public:
    Rectangle(double w, double h) : width(w), height(h) {}
    
    double area() const override {
        return width * height;
    }
    
    void draw() const override {
        std::cout << "Drawing a rectangle " << width << "x" << height << "\n";
    }
};

// 使用多态
void printArea(const Shape& shape) {
    std::cout << "Area: " << shape.area() << std::endl;
    shape.draw();  // 动态分派
}

int main() {
    Circle c(5);
    Rectangle r(4, 6);
    
    printArea(c);  // 通过Shape借用调用Circle实现
    printArea(r);  // 通过Shape借用调用Rectangle实现
}
```

### 4.3 组合与聚合

#### 组合关系

- **组合**：has-a关系，强生命周期依赖
- **聚合**：contains-a关系，弱生命周期依赖
- **关联**：uses-a关系，生命周期独立

#### 设计模式中的应用

- **组合优于继承**：更灵活的代码复用机制
- **依赖注入**：通过组合实现松耦合
- **策略模式**：行为组合与动态替换

```cpp
// 组合与聚合示例
class Engine {
public:
    void start() { std::cout << "Engine started\n"; }
    void stop() { std::cout << "Engine stopped\n"; }
};

class Wheel {
public:
    void inflate(int pressure) {
        std::cout << "Wheel inflated to " << pressure << " psi\n";
    }
};

// 组合关系 - Car拥有Engine，强生命周期依赖
class Car {
private:
    Engine engine;  // 组合：引擎是汽车的组成部分
    std::vector<Wheel> wheels;  // 组合：轮子是汽车的组成部分
    
public:
    Car() : wheels(4) {}  // 创建4个轮子
    
    void start() {
        engine.start();
        std::cout << "Car started\n";
    }
    
    void stop() {
        engine.stop();
        std::cout << "Car stopped\n";
    }
    
    void inflateTires(int pressure) {
        for (auto& wheel : wheels) {
            wheel.inflate(pressure);
        }
    }
};

// 聚合关系 - Driver使用Car，但生命周期独立
class Driver {
private:
    std::string name;
    Car* car;  // 聚合：驾驶员使用汽车，但不拥有它
    
public:
    Driver(const std::string& n) : name(n), car(nullptr) {}
    
    void setCar(Car* c) {
        car = c;
    }
    
    void drive() {
        if (car) {
            std::cout << name << " is driving the car\n";
            car->start();
        } else {
            std::cout << name << " has no car to drive\n";
        }
    }
};
```

### 4.4 SOLID原则

#### 单一责任原则 (SRP)

- **定义**：一个类应该有且只有一个改变的理由
- **形式化**：每个类C应对应一组相关的函数F，使得F的变化原因一致

#### 开放封闭原则 (OCP)

- **定义**：软件实体应该对扩展开放，对修改关闭
- **形式化**：对于任何扩展E，系统S应能通过添加而非修改现有代码来实现E

#### 里氏替换原则 (LSP)

- **定义**：子类型必须能够替换其基类型
- **形式化**：若S <: T，则程序P 中所有T类型对象可被S类型对象替换而不改变P的行为

#### 接口隔离原则 (ISP)

- **定义**：客户端不应被迫依赖于它们不使用的方法
- **形式化**：接口I应细分为多个特定接口I₁, I₂, ..., Iₙ，使得每个客户端只依赖其需要的接口

#### 依赖倒置原则 (DIP)

- **定义**：高层模块不应依赖低层模块，二者都应依赖于抽象
- **形式化**：对于模块H依赖模块L，应存在抽象A使得H和L都依赖A

```cpp
// SOLID示例：开放封闭原则与依赖倒置原则
// 抽象接口
class Logger {
public:
    virtual ~Logger() = default;
    virtual void log(const std::string& message) = 0;
};

// 具体实现
class ConsoleLogger : public Logger {
public:
    void log(const std::string& message) override {
        std::cout << "LOG: " << message << std::endl;
    }
};

class FileLogger : public Logger {
private:
    std::string filename;
public:
    FileLogger(const std::string& file) : filename(file) {}
    
    void log(const std::string& message) override {
        // 将日志写入文件
        std::cout << "Writing to " << filename << ": " << message << std::endl;
    }
};

// 使用依赖注入实现依赖倒置
class UserManager {
private:
    Logger& logger;  // 依赖抽象，非具体实现
    
public:
    UserManager(Logger& log) : logger(log) {}
    
    void createUser(const std::string& username) {
        // 创建用户逻辑...
        logger.log("Created user: " + username);
    }
};

// 系统可以轻松扩展新的日志记录方式（开放封闭原则）
class DatabaseLogger : public Logger {
public:
    void log(const std::string& message) override {
        std::cout << "DB LOG: " << message << std::endl;
    }
};
```

## 5. 内存管理与资源控制

### 5.1 内存模型

#### C++内存布局

- **代码段**：存储编译后的程序指令
- **数据段**：存储全局变量和静态变量
- **堆**：动态分配的内存
- **栈**：函数调用栈，局部变量与参数

#### 对象内存布局

- **对象布局**：数据成员、虚函数表指针
- **内存对齐**：提高访问效率的成员对齐规则
- **空基类优化**：避免空基类占用内存

```cpp
// 内存模型示例
class Base {
    virtual void foo() {}  // 添加虚函数表指针
};

class Empty {};  // 空类

class Derived : public Empty {  // 空基类优化
    int x;      // 4字节
    char c;     // 1字节
    double d;   // 8字节，通常会对齐
};

std::cout << "Size of Base: " << sizeof(Base) << std::endl;
std::cout << "Size of Empty: " << sizeof(Empty) << std::endl;
std::cout << "Size of Derived: " << sizeof(Derived) << std::endl;
```

### 5.2 动态内存管理

#### 5.2.1 内存分配机制

- **操作符**：`new`/`delete`, `new[]`/`delete[]`
- **分配器**：`std::allocator`自定义内存分配
- **低级函数**：`malloc`/`free`, `operator new`/`operator delete`

#### 5.2.2 内存管理问题

- **内存泄漏**：分配但未释放的内存
- **悬空指针**：指向已释放内存的指针
- **缓冲区溢出**：访问越界内存
- **内存碎片**：分配模式导致的内存不连续

#### 5.2.3 形式化分析

- **内存安全**：程序不能访问未分配或已释放的内存
- **资源安全**：所有资源都能正确释放
- **生命周期管理**：确保内存在适当时机分配和释放

```cpp
// 动态内存管理示例
void memory_issues() {
    // 内存泄漏
    int* leak = new int(42);
    // 缺少 delete leak;
    
    // 悬空指针
    int* dangling;
    {
        int x = 10;
        dangling = &x;  // x离开作用域后指针悬空
    }
    // *dangling = 20;  // 未定义行为
    
    // 缓冲区溢出
    int* buffer = new int[5];
    // buffer[10] = 0;  // 越界访问
    delete[] buffer;
    
    // 双重释放
    int* doubleFree = new int(5);
    delete doubleFree;
    // delete doubleFree;  // 未定义行为
}
```

### 5.3 智能指针与所有权

#### 5.3.1 智能指针类型

- **unique_ptr**：唯一所有权，不可复制
- **shared_ptr**：共享所有权，借用计数
- **weak_ptr**：弱借用，不影响生命周期
- **auto_ptr**：已弃用的早期智能指针

#### 5.3.2 所有权模型

- **独占所有权**：资源只有一个所有者
- **共享所有权**：资源可以有多个所有者
- **借用**：临时访问但不拥有资源

#### 5.3.3 形式化定义

- **所有权传递**：A拥有r，转移给B后A不再拥有r
- **所有权共享**：A和B同时拥有r，直到两者都不再借用
- **借用计数**：记录共享资源的借用数量，归零时释放

```cpp
// 智能指针与所有权示例
# include <memory>

class Resource {
public:
    Resource() { std::cout << "Resource acquired\n"; }
    ~Resource() { std::cout << "Resource released\n"; }
    void use() { std::cout << "Resource used\n"; }
};

void ownership_example() {
    // 独占所有权
    std::unique_ptr<Resource> uniq = std::make_unique<Resource>();
    uniq->use();
    
    // 所有权转移
    std::unique_ptr<Resource> uniq2 = std::move(uniq);
    // uniq->use();  // 错误：uniq现在是空指针
    uniq2->use();
    
    // 共享所有权
    std::shared_ptr<Resource> shared1 = std::make_shared<Resource>();
    {
        std::shared_ptr<Resource> shared2 = shared1;  // 借用计数增加
        std::cout << "Ref count: " << shared1.use_count() << std::endl;
        // 离开作用域，shared2销毁，借用计数减少
    }
    std::cout << "Ref count: " << shared1.use_count() << std::endl;
    
    // 弱借用
    std::weak_ptr<Resource> weak = shared1;
    std::cout << "Is expired? " << weak.expired() << std::endl;
    
    // 提升弱借用
    if (auto sp = weak.lock()) {
        sp->use();
    }
    
    // 释放共享指针
    shared1.reset();
    std::cout << "Is expired? " << weak.expired() << std::endl;
}
```

### 5.4 RAII范式

#### 5.4.1 RAII核心概念

- **定义**：资源获取即初始化（Resource Acquisition Is Initialization）
- **原则**：将资源管理与对象生命周期绑定
- **保证**：自动资源释放，异常安全

#### 5.4.2 RAII应用

- **内存管理**：智能指针
- **文件操作**：文件句柄封装
- **锁管理**：互斥锁的自动加锁解锁
- **事务管理**：自动提交或回滚

#### 5.4.3 形式化分析

- **资源获取时机**：构造函数中获取资源
- **资源释放时机**：析构函数中释放资源
- **异常安全保证**：即使发生异常，资源也能释放

```cpp
// RAII示例
# include <mutex>
# include <fstream>

// RAII 文件处理
class File {
private:
    std::fstream file;
    
public:
    File(const std::string& filename, std::ios::openmode mode)
        : file(filename, mode) {
        if (!file.is_open()) {
            throw std::runtime_error("Could not open file");
        }
    }
    
    ~File() {
        if (file.is_open()) {
            file.close();
        }
    }
    
    void write(const std::string& data) {
        file << data;
    }
    
    std::string read() {
        std::string content;
        std::string line;
        while (std::getline(file, line)) {
            content += line + "\n";
        }
        return content;
    }
};

// RAII锁管理
class LockGuard {
private:
    std::mutex& mutex;
    
public:
    explicit LockGuard(std::mutex& m) : mutex(m) {
        mutex.lock();
    }
    
    ~LockGuard() {
        mutex.unlock();
    }
    
    // 禁止复制和移动
    LockGuard(const LockGuard&) = delete;
    LockGuard& operator=(const LockGuard&) = delete;
};

void raii_example() {
    std::mutex m;
    
    try {
        // 自动锁管理
        LockGuard lock(m);  // 获取锁
        // 加锁的临界区...
        throw std::runtime_error("Something went wrong");
        // LockGuard析构函数自动解锁，即使发生异常
    } catch (const std::exception& e) {
        std::cout << "Caught exception: " << e.what() << std::endl;
        // 此时锁已经释放
    }
    
    // 文件自动管理
    try {
        File logFile("log.txt", std::ios::out | std::ios::app);
        logFile.write("Log entry\n");
        // File析构函数自动关闭文件
    } catch (const std::exception& e) {
        std::cout << "File error: " << e.what() << std::endl;
    }
}
```

## 6. 并发与同步模型

### 6.1 线程模型

#### C++线程库

- **std::thread**：线程对象，表示控制线程
- **线程创建与等待**：通过构造函数创建，join等待完成
- **线程分离**：detach使线程独立运行

#### 线程生命周期

- **创建**：构造std::thread对象时创建线程
- **运行**：线程函数执行
- **阻塞**：等待条件或资源
- **终止**：线程函数返回或抛出异常
- **可连接**：可以通过join等待
- **分离**：通过detach成为后台线程

```cpp
// 线程模型示例
# include <thread>
# include <chrono>

void work(int id, int duration) {
    std::cout << "Thread " << id << " starting\n";
    std::this_thread::sleep_for(std::chrono::seconds(duration));
    std::cout << "Thread " << id << " finished\n";
}

void thread_example() {
    // 创建线程
    std::thread t1(work, 1, 2);
    
    // 创建另一个线程
    std::thread t2(work, 2, 3);
    
    std::cout << "Main thread continues execution\n";
    
    // 等待线程完成
    t1.join();
    std::cout << "Thread 1 joined\n";
    
    // 分离线程
    t2.detach();
    std::cout << "Thread 2 detached\n";
    
    // 检查线程是否可连接
    if (t1.joinable()) {
        std::cout << "T1 is still joinable\n";
    } else {
        std::cout << "T1 is not joinable\n";
    }
    
    if (t2.joinable()) {
        std::cout << "T2 is still joinable\n";
    } else {
        std::cout << "T2 is not joinable\n";
    }
}
```

### 6.2 同步原语

#### 互斥与锁

- **std::mutex**：互斥锁，防止多线程同时访问共享资源
- **std::recursive_mutex**：允许同一线程多次获取的互斥锁
- **std::shared_mutex**：读写锁，多读单写
- **std::lock_guard**：RAII风格的互斥锁管理
- **std::unique_lock**：更灵活的RAII锁，支持延迟锁定

#### 条件变量

- **std::condition_variable**：线程间的条件等待与通知
- **等待**：wait、wait_for、wait_until
- **通知**：notify_one、notify_all

#### 同步形式化

- **临界区**：一次只允许一个线程访问的代码区域
- **互斥保证**：确保资源互斥访问
- **条件同步**：基于条件的线程控制

```cpp
// 同步原语示例
# include <mutex>
# include <condition_variable>
# include <queue>

template<typename T>
class ThreadSafeQueue {
private:
    std::queue<T> queue;
    mutable std::mutex mutex;
    std::condition_variable cv;
    
public:
    void push(T value) {
        {
            std::lock_guard<std::mutex> lock(mutex);
            queue.push(std::move(value));
        }
        cv.notify_one();  // 通知等待的线程
    }
    
    bool try_pop(T& value) {
        std::lock_guard<std::mutex> lock(mutex);
        if (queue.empty()) {
            return false;
        }
        value = std::move(queue.front());
        queue.pop();
        return true;
    }
    
    void wait_and_pop(T& value) {
        std::unique_lock<std::mutex> lock(mutex);
        cv.wait(lock, [this]{ return !queue.empty(); });
        value = std::move(queue.front());
        queue.pop();
    }
    
    bool empty() const {
        std::lock_guard<std::mutex> lock(mutex);
        return queue.empty();
    }
};

void thread_safe_queue_example() {
    ThreadSafeQueue<int> queue;
    
    std::thread producer([&queue]{
        for (int i = 0; i < 10; ++i) {
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            std::cout << "Producing: " << i << std::endl;
            queue.push(i);
        }
    });
    
    std::thread consumer([&queue]{
        for (int i = 0; i < 10; ++i) {
            int value;
            queue.wait_and_pop(value);
            std::cout << "Consuming: " << value << std::endl;
        }
    });
    
    producer.join();
    consumer.join();
}
```

### 6.3 内存序与原子操作

#### 6.3.1 原子操作

- **std::atomic**：原子类型，不可分割的操作
- **原子操作**：load、store、exchange、compare_exchange
- **原子标志**：std::atomic_flag，无锁编程基础

#### 6.3.2 内存序模型

- **顺序一致性**：memory_order_seq_cst，最严格
- **获取-释放**：memory_order_acquire, memory_order_release
- **松散序**：memory_order_relaxed，最少限制
- **消费**：memory_order_consume，数据依赖保证

#### 6.3.3 形式化定义

- **happens-before关系**：操作间的因果顺序
- **同步操作**：建立线程间happens-before关系
- **数据竞争**：同时访问同一内存位置且至少一个是写操作

```cpp
// 内存模型与原子操作示例
# include <atomic>
# include <thread>

std::atomic<int> counter(0);
std::atomic<bool> ready(false);

void atomic_example() {
    std::thread worker([]{
        // 等待ready信号
        while (!ready.load(std::memory_order_acquire)) {
            std::this_thread::yield();
        }
        
        // ready为true后，counter增加
        for (int i = 0; i < 1000; ++i) {
            counter.fetch_add(1, std::memory_order_relaxed);
        }
    });
    
    // 准备工作...
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    
    // 设置ready标志
    ready.store(true, std::memory_order_release);
    worker.join();
    
    std::cout << "Final counter: " << counter.load() << std::endl;
}

// 实现自旋锁
class SpinLock {
private:
    std::atomic_flag flag = ATOMIC_FLAG_INIT;
    
public:
    void lock() {
        while (flag.test_and_set(std::memory_order_acquire)) {
            // 自旋等待
        }
    }
    
    void unlock() {
        flag.clear(std::memory_order_release);
    }
};
```

### 6.4 并发模式

#### 常见并发模式

- **生产者-消费者**：通过队列传递数据
- **读写锁**：多读者单写者模式
- **线程池**：复用线程处理任务
- **异步计算**：通过future获取结果

#### 并发安全技术

- **无锁编程**：使用原子操作实现无锁数据结构
- **细粒度锁**：最小化锁的范围
- **避免死锁**：资源获取顺序一致
- **无共享设计**：线程间不共享数据，通过消息通信

```cpp
// 并发模式示例：线程池
# include <vector>
# include <queue>
# include <functional>
# include <future>

class ThreadPool {
private:
    std::vector<std::thread> workers;
    std::queue<std::function<void()>> tasks;
    std::mutex queue_mutex;
    std::condition_variable condition;
    bool stop;
    
public:
    ThreadPool(size_t threads) : stop(false) {
        for (size_t i = 0; i < threads; ++i) {
            workers.emplace_back([this]{
                while (true) {
                    std::function<void()> task;
                    {
                        std::unique_lock<std::mutex> lock(queue_mutex);
                        condition.wait(lock, [this]{
                            return stop || !tasks.empty();
                        });
                        
                        if (stop && tasks.empty()) {
                            return;
                        }
                        
                        task = std::move(tasks.front());
                        tasks.pop();
                    }
                    
                    task();
                }
            });
        }
    }
    
    template<class F, class... Args>
    auto enqueue(F&& f, Args&&... args) 
        -> std::future<typename std::result_of<F(Args...)>::type> {
        using return_type = typename std::result_of<F(Args...)>::type;
        
        auto task = std::make_shared<std::

# C++编程语言分析（续2）

```cpp
// ThreadPool实现（续）
        auto task = std::make_shared<std::packaged_task<return_type()>>(
            std::bind(std::forward<F>(f), std::forward<Args>(args)...)
        );
        
        std::future<return_type> result = task->get_future();
        
        {
            std::unique_lock<std::mutex> lock(queue_mutex);
            if (stop) {
                throw std::runtime_error("线程池已停止，无法添加任务");
            }
            tasks.emplace([task](){ (*task)(); });
        }
        
        condition.notify_one();
        return result;
    }
    
    ~ThreadPool() {
        {
            std::unique_lock<std::mutex> lock(queue_mutex);
            stop = true;
        }
        
        condition.notify_all();
        
        for (std::thread &worker : workers) {
            worker.join();
        }
    }
};

void thread_pool_example() {
    ThreadPool pool(4);  // 创建4个工作线程
    
    // 提交任务并获取future
    auto result1 = pool.enqueue([](int a, int b) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        return a + b;
    }, 10, 20);
    
    auto result2 = pool.enqueue([](int x) {
        std::this_thread::sleep_for(std::chrono::seconds(2));
        return x * x;
    }, 5);
    
    // 获取结果
    std::cout << "Result 1: " << result1.get() << std::endl;  // 输出30
    std::cout << "Result 2: " << result2.get() << std::endl;  // 输出25
}
```

## 7. 类型特质与元编程

### 7.1 类型特质

#### 类型特质机制

- **类型信息**：`std::is_integral`, `std::is_pointer`等
- **类型关系**：`std::is_same`, `std::is_base_of`等
- **类型修改**：`std::remove_reference`, `std::add_const`等
- **类型变换**：`std::decay`, `std::common_type`等

#### 类型特质应用

- **编译期条件**：根据类型特质选择代码路径
- **SFINAE**：替换失败不是错误，实现泛型代码分支
- **静态断言**：编译期验证类型属性

```cpp
// 类型特质示例
# include <type_traits>

// 类型检查
template<typename T>
void process_numeric(T value) {
    static_assert(std::is_arithmetic<T>::value, "需要数值类型");
    
    if constexpr (std::is_integral<T>::value) {
        std::cout << "处理整数: " << value << std::endl;
    } else if constexpr (std::is_floating_point<T>::value) {
        std::cout << "处理浮点数: " << value << std::endl;
    }
}

// 类型修改
template<typename T>
void process_reference(T&& value) {
    using ValueType = typename std::remove_reference<T>::type;
    
    static_assert(!std::is_pointer<ValueType>::value, "不接受指针");
    
    ValueType copy = value;  // 创建副本
    std::cout << "处理值: " << copy << std::endl;
}

// SFINAE应用
template<typename T>
typename std::enable_if<std::is_pod<T>::value, void>::type
serialize(const T& value) {
    std::cout << "POD类型序列化" << std::endl;
    // 二进制序列化...
}

template<typename T>
typename std::enable_if<!std::is_pod<T>::value, void>::type
serialize(const T& value) {
    std::cout << "非POD类型序列化" << std::endl;
    // 自定义序列化...
}
```

### 7.2 模板元编程

#### 编译期计算

- **递归模板实例化**：实现编译期循环
- **模板特化**：实现编译期条件分支
- **类型操作**：编译期类型运算与转换

#### 编译期算法

- **编译期值计算**：阶乘、斐波那契等
- **类型列表操作**：类型连接、过滤等
- **策略选择**：根据类型选择最优算法

```cpp
// 模板元编程示例
// 编译期阶乘计算
template<int N>
struct Factorial {
    static constexpr int value = N * Factorial<N-1>::value;
};

template<>
struct Factorial<0> {
    static constexpr int value = 1;
};

// 编译期斐波那契数列
template<int N>
struct Fibonacci {
    static constexpr int value = Fibonacci<N-1>::value + Fibonacci<N-2>::value;
};

template<>
struct Fibonacci<0> {
    static constexpr int value = 0;
};

template<>
struct Fibonacci<1> {
    static constexpr int value = 1;
};

// 类型列表
template<typename... Ts>
struct TypeList {};

// 类型列表长度
template<typename List>
struct Length;

template<typename... Ts>
struct Length<TypeList<Ts...>> {
    static constexpr size_t value = sizeof...(Ts);
};

// 类型列表前端插入
template<typename T, typename List>
struct PushFront;

template<typename T, typename... Ts>
struct PushFront<T, TypeList<Ts...>> {
    using type = TypeList<T, Ts...>;
};

// 类型列表连接
template<typename List1, typename List2>
struct Concat;

template<typename... Ts1, typename... Ts2>
struct Concat<TypeList<Ts1...>, TypeList<Ts2...>> {
    using type = TypeList<Ts1..., Ts2...>;
};

void template_metaprogramming_example() {
    std::cout << "5! = " << Factorial<5>::value << std::endl;  // 120
    std::cout << "Fibonacci(7) = " << Fibonacci<7>::value << std::endl;  // 13
    
    using MyTypes = TypeList<int, double, std::string>;
    std::cout << "Type list length: " << Length<MyTypes>::value << std::endl;  // 3
    
    using ExtendedTypes = PushFront<char, MyTypes>::type;
    std::cout << "Extended type list length: " << Length<ExtendedTypes>::value << std::endl;  // 4
}
```

### 7.3 标签分派与特化

#### 标签分派技术

- **优先级标签**：用于实现重载解析优先级
- **类型标签**：用类型标签选择重载
- **编译期if**：C++17的`if constexpr`简化条件分支

#### 特化技术

- **全特化**：为特定类型提供完全特化版本
- **偏特化**：为类型模式提供特化版本
- **特化选择**：编译器根据特化匹配规则选择最佳实现

```cpp
// 标签分派与特化示例
# include <algorithm>
# include <iterator>

// 标签类型
struct input_iterator_tag {};
struct forward_iterator_tag : input_iterator_tag {};
struct bidirectional_iterator_tag : forward_iterator_tag {};
struct random_access_iterator_tag : bidirectional_iterator_tag {};

// 特质类提取迭代器类型
template<typename Iterator>
struct iterator_traits {
    using iterator_category = typename Iterator::iterator_category;
};

// 针对指针的特化
template<typename T>
struct iterator_traits<T*> {
    using iterator_category = random_access_iterator_tag;
};

// 使用标签分派实现优化的distance函数
template<typename Iterator>
typename std::iterator_traits<Iterator>::difference_type
distance_impl(Iterator first, Iterator last, std::input_iterator_tag) {
    // 对输入迭代器的慢实现 - O(n)
    typename std::iterator_traits<Iterator>::difference_type n = 0;
    while (first != last) {
        ++first;
        ++n;
    }
    return n;
}

template<typename Iterator>
typename std::iterator_traits<Iterator>::difference_type
distance_impl(Iterator first, Iterator last, std::random_access_iterator_tag) {
    // 对随机访问迭代器的快实现 - O(1)
    return last - first;
}

template<typename Iterator>
typename std::iterator_traits<Iterator>::difference_type
distance(Iterator first, Iterator last) {
    // 根据迭代器类型分派到最合适的实现
    return distance_impl(
        first, last,
        typename std::iterator_traits<Iterator>::iterator_category()
    );
}

// 使用if constexpr简化条件分支
template<typename T>
auto get_value(T t) {
    if constexpr (std::is_pointer_v<T>) {
        return *t;  // T是指针类型
    } else if constexpr (std::is_array_v<T>) {
        return t[0];  // T是数组类型
    } else {
        return t;  // T是值类型
    }
}
```

## 8. 函数式编程特质

### 8.1 Lambda表达式

#### Lambda语法与特质

- **捕获列表**：`[capture]`，捕获外部变量
- **参数列表**：`(params)`，函数参数
- **返回类型**：`-> return_type`，可选的返回类型声明
- **函数体**：`{body}`，执行代码
- **变量捕获方式**：值捕获、借用捕获、隐式捕获

#### Lambda底层原理

- **闭包类型**：每个lambda表达式生成唯一的闭包类型
- **闭包对象**：捕获的变量作为闭包对象的成员
- **函数调用运算符**：实现lambda的执行逻辑

```cpp
// Lambda表达式示例
# include <algorithm>
# include <vector>
# include <functional>

void lambda_examples() {
    // 基本语法
    auto add = [](int a, int b) -> int { return a + b; };
    std::cout << "5 + 3 = " << add(5, 3) << std::endl;
    
    // 变量捕获
    int x = 10;
    auto add_x = [x](int a) { return a + x; };
    std::cout << "15 + x = " << add_x(15) << std::endl;
    
    // 借用捕获
    auto increment_x = [&x] { x++; };
    increment_x();
    std::cout << "x = " << x << std::endl;  // 输出11
    
    // 隐式捕获
    int y = 20;
    auto sum_vars = [=] { return x + y; };  // 隐式值捕获
    auto modify_vars = [&] { x += 5; y += 5; };  // 隐式借用捕获
    
    std::cout << "Sum: " << sum_vars() << std::endl;
    modify_vars();
    std::cout << "x = " << x << ", y = " << y << std::endl;
    
    // 泛型lambda（C++14）
    auto generic_add = [](auto a, auto b) { return a + b; };
    std::cout << "5 + 3 = " << generic_add(5, 3) << std::endl;
    std::cout << "3.5 + 2.5 = " << generic_add(3.5, 2.5) << std::endl;
    
    // 在算法中使用
    std::vector<int> nums = {1, 2, 3, 4, 5};
    std::transform(nums.begin(), nums.end(), nums.begin(),
                   [](int n) { return n * n; });
                   
    for (int n : nums) {
        std::cout << n << " ";  // 输出：1 4 9 16 25
    }
    std::cout << std::endl;
    
    // 可变lambda
    int counter = 0;
    auto increment = [counter]() mutable { return ++counter; };
    std::cout << increment() << std::endl;  // 1
    std::cout << increment() << std::endl;  // 2
    std::cout << "Original counter: " << counter << std::endl;  // 0（未修改）
}
```

### 8.2 高阶函数

#### 高阶函数概念

- **定义**：接受函数作为参数或返回函数的函数
- **函数组合**：将多个函数组合成一个新函数
- **柯里化**：将多参数函数转换为一系列单参数函数
- **部分应用**：固定一部分参数，返回接受剩余参数的函数

#### C++中的实现

- **函数指针**：传统的函数借用方式
- **函数对象**：重载函数调用运算符的类
- **std::function**：类型擦除的函数包装器
- **std::bind**：部分应用的实现

```cpp
// 高阶函数示例
# include <functional>

// 高阶函数：接受两个函数和一个值，返回它们组合的结果
template<typename F, typename G, typename T>
auto compose(F f, G g, T x) -> decltype(f(g(x))) {
    return f(g(x));
}

// 返回函数的函数
template<typename T>
std::function<T(T)> makeMultiplier(T factor) {
    return [factor](T value) { return value * factor; };
}

// 柯里化示例
template<typename A, typename B, typename C>
auto curry(std::function<C(A, B)> f) {
    return [f](A a) {
        return [f, a](B b) {
            return f(a, b);
        };
    };
}

void higher_order_function_examples() {
    // 组合函数
    auto square = [](int x) { return x * x; };
    auto negate = [](int x) { return -x; };
    
    int result = compose(negate, square, 5);
    std::cout << "negate(square(5)) = " << result << std::endl;  // -25
    
    // 使用makeMultiplier生成新函数
    auto double_func = makeMultiplier(2);
    auto triple_func = makeMultiplier(3);
    
    std::cout << "double(5) = " << double_func(5) << std::endl;  // 10
    std::cout << "triple(5) = " << triple_func(5) << std::endl;  // 15
    
    // 部分应用
    std::function<int(int, int)> add = [](int a, int b) { return a + b; };
    auto add5 = std::bind(add, 5, std::placeholders::_1);
    
    std::cout << "add5(10) = " << add5(10) << std::endl;  // 15
    
    // 柯里化
    auto curriedAdd = curry<int, int, int>(add);
    auto add7 = curriedAdd(7);
    
    std::cout << "add7(8) = " << add7(8) << std::endl;  // 15
}
```

### 8.3 范畴论视角的函子与单子

#### 函子概念

- **定义**：保持结构的映射，从一个范畴到另一个范畴
- **在C++中**：容器模板如`std::vector`，加上"映射"操作
- **映射操作**：将容器中的值通过函数变换

#### 单子模式

- **定义**：具有额外结构的函子，支持组合和扁平化
- **在C++中**：`std::optional`、`std::variant`、`std::future`等
- **操作**：bind（flatMap）、return（纯值封装）

```cpp
// 函子与单子示例
# include <vector>
# include <optional>
# include <algorithm>
# include <string>

// 函子实现：为容器提供映射操作
template<template<typename...> class Container, typename A, typename B, typename... Args>
Container<B, Args...> fmap(std::function<B(A)> f, const Container<A, Args...>& container) {
    Container<B, Args...> result;
    std::transform(container.begin(), container.end(), 
                   std::back_inserter(result), f);
    return result;
}

// 单子操作：optional的bind实现
template<typename A, typename B>
std::optional<B> mbind(const std::optional<A>& ma, std::function<std::optional<B>(A)> f) {
    if (ma.has_value()) {
        return f(*ma);
    } else {
        return std::nullopt;
    }
}

// 单子操作：optional的return实现
template<typename A>
std::optional<A> mreturn(A a) {
    return std::optional<A>(a);
}

void functor_monad_examples() {
    // 函子示例
    std::vector<int> numbers = {1, 2, 3, 4, 5};
    auto square = [](int x) { return x * x; };
    
    // 映射操作
    std::vector<int> squared = fmap<std::vector>(square, numbers);
    
    std::cout << "Squares: ";
    for (int n : squared) {
        std::cout << n << " ";  // 1 4 9 16 25
    }
    std::cout << std::endl;
    
    // 单子示例：optional
    std::function<std::optional<int>(int)> half = [](int x) -> std::optional<int> {
        if (x % 2 == 0) {
            return x / 2;
        } else {
            return std::nullopt;
        }
    };
    
    std::function<std::optional<std::string>(int)> toString = [](int x) -> std::optional<std::string> {
        if (x >= 0) {
            return std::to_string(x);
        } else {
            return std::nullopt;
        }
    };
    
    // 单子操作：链式调用
    auto result1 = mbind(mreturn(10), half);  // optional(5)
    auto result2 = mbind(mbind(mreturn(10), half), toString);  // optional("5")
    auto result3 = mbind(mbind(mreturn(9), half), toString);  // nullopt
    
    std::cout << "Result 1: " << (result1 ? std::to_string(*result1) : "nullopt") << std::endl;
    std::cout << "Result 2: " << (result2 ? *result2 : "nullopt") << std::endl;
    std::cout << "Result 3: " << (result3 ? *result3 : "nullopt") << std::endl;
}
```

## 9. 形式语义与验证

### 9.1 操作语义

#### 形式语义模型

- **大步语义**：描述整个程序执行结果
- **小步语义**：描述程序的每一步执行
- **指称语义**：将程序映射到数学模型
- **公理语义**：通过公理系统描述程序行为

#### C++语句语义

- **表达式**：计算值和产生副作用
- **声明**：引入名称和类型
- **语句**：影响控制流和执行顺序
- **未定义行为**：超出语言规范定义的执行

```cpp
// 操作语义示例：小步语义示意
/*
考虑表达式 (x + 1) * 2，其中 x = 5
小步语义执行步骤：
1. (5 + 1) * 2    -- 替换变量
2. 6 * 2          -- 计算加法
3. 12             -- 计算乘法
*/

// 约定俗成的语义表示
void operation_semantics_example() {
    int x = 0;
    // {x = 0}
    
    if (x == 0) {
        x = 1;
    } else {
        x = 2;
    }
    // {x = 1}
    
    for (int i = 0; i < 3; i++) {
        x *= 2;
    }
    // 循环不变量：每次迭代后，x = 初始值 * 2^i
    // {x = 8}
    
    std::cout << "Final x: " << x << std::endl;
}
```

### 9.2 类型安全与约束

#### 9.2.1 类型安全机制

- **静态类型检查**：编译时验证类型兼容性
- **动态类型检查**：运行时验证类型转换
- **类型约束**：限制泛型代码接受的类型

#### 9.2.2 形式化定义

- **类型安全性**：良好类型的程序不会进入非法状态
- **类型完备性**：类型系统能捕获所有类型错误
- **健全性**：良好类型的程序执行不会卡住

```cpp
// 类型安全与约束示例
# include <type_traits>
# include <concepts>  // C++20

// C++20之前的类型约束
template<typename T>
typename std::enable_if<std::is_arithmetic<T>::value, T>::type
safe_add(T a, T b) {
    return a + b;
}

// C++20：概念约束
template<typename T>
concept Numeric = std::is_arithmetic_v<T>;

template<Numeric T>
T constrained_add(T a, T b) {
    return a + b;
}

// 类型安全的容器
template<typename T, typename Enable = void>
class SafeContainer;

// 只允许可复制类型
template<typename T>
class SafeContainer<T, typename std::enable_if<std::is_copy_constructible<T>::value>::type> {
private:
    std::vector<T> data;
    
public:
    void add(const T& item) {
        data.push_back(item);
    }
    
    T get(size_t index) const {
        if (index < data.size()) {
            return data[index];
        }
        throw std::out_of_range("Index out of range");
    }
};

// 类型安全示例
struct NonCopyable {
    NonCopyable() = default;
    NonCopyable(const NonCopyable&) = delete;
    NonCopyable& operator=(const NonCopyable&) = delete;
};

void type_safety_examples() {
    // 静态类型检查
    int a = 5;
    // std::string s = a;  // 编译错误：类型不兼容
    
    // 动态类型检查
    try {
        std::vector<int> v = {1, 2, 3};
        // v.at(10);  // 抛出std::out_of_range异常
    } catch (const std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
    }
    
    // 类型约束
    auto result = safe_add(5, 10);
    // auto invalid = safe_add("hello", "world");  // 编译错误：非数值类型
    
    // 安全容器
    SafeContainer<int> intContainer;
    intContainer.add(42);
    
    // SafeContainer<NonCopyable> ncContainer;  // 编译错误：NonCopyable不可复制
}
```

### 9.3 程序验证

#### 9.3.1 验证技术

- **静态分析**：无需执行程序的分析技术
- **符号执行**：以符号形式执行程序
- **模型检验**：验证程序状态模型
- **霍尔逻辑**：通过前置条件和后置条件验证程序

#### 9.3.2 形式化证明

- **不变量**：程序执行过程中保持的条件
- **循环变体**：证明循环终止的度量
- **前置/后置条件**：验证函数行为

```cpp
// 程序验证示例
// 使用霍尔逻辑对二分查找进行形式化分析

/*
二分查找的霍尔三元组表示：

{前置条件: arr是已排序数组，0 ≤ left ≤ right < arr.length}
int binary_search(int arr[], int left, int right, int target)
{
    while (left <= right) {
        // 循环不变量: 如果target在数组中，它必在arr[left..right]范围内
        int mid = left + (right - left) / 2;
        
        if (arr[mid] == target) {
            return mid;
        }
        
        if (arr[mid] < target) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
        // 循环变体: right - left，每次迭代都会减小
    }
    
    return -1;
}
{后置条件: 返回-1表示target不在数组中，否则返回的索引i满足arr[i] = target}
*/

// 使用断言验证不变量
# include <cassert>

int verified_binary_search(int arr[], int size, int target) {
    // 前置条件检查
    assert(size >= 0);
    
    int left = 0;
    int right = size - 1;
    
    while (left <= right) {
        // 循环不变量：如果target在arr 中，它必在arr[left..right]范围内
        assert(left >= 0 && right < size);
        
        int mid = left + (right - left) / 2;
        assert(mid >= left && mid <= right);
        
        if (arr[mid] == target) {
            // 后置条件：arr[mid] = target
            return mid;
        }
        
        int old_range = right - left + 1;
        
        if (arr[mid] < target) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
        
        // 循环变体：范围大小减小
        int new_range = right - left + 1;
        assert(new_range < old_range);  // 确保终止
    }
    
    // 后置条件：target不在arr 中
    return -1;
}
```

## 10. 总结与前沿发展

### 10.1 C++类型系统总结

#### 关键特质

- **静态类型**：编译时类型检查
- **多范式**：支持过程式、面向对象、泛型和函数式编程
- **模板**：强大的编译期泛型和元编程能力
- **类型安全**：强类型系统保证程序正确性

#### 优缺点分析

- **优点**：性能、表达能力、类型安全
- **缺点**：复杂性、学习曲线、历史包袱
- **权衡**：灵活性与安全性、性能与抽象

### 10.2 前沿发展

#### 现代C++特质

- **C++20**：概念、协程、模块、范围
- **C++23**：静态反射、模式匹配、契约
- **未来方向**：元编程简化、更强类型安全

#### 与其他语言的对比

- **相对Rust**：所有权模型、内存安全
- **相对Haskell**：纯函数式、类型系统
- **相对TypeScript**：结构化类型、渐进式类型

```cpp
// C++20概念示例
# include <concepts>
# include <iostream>
# include <string>

// 定义概念
template<typename T>
concept Printable = requires(T x, std::ostream& os) {
    { os << x } -> std::same_as<std::ostream&>;
};

// 使用概念约束泛型函数
template<Printable T>
void print(const T& value) {
    std::cout << value << std::endl;
}

// C++20协程示例
# include <coroutine>
# include <future>

struct Task {
    struct promise_type {
        Task get_return_object() { return {}; }
        std::suspend_never initial_suspend() { return {}; }
        std::suspend_never final_suspend() noexcept { return {}; }
        void return_void() {}
        void unhandled_exception() {}
    };
};

Task example_coroutine() {
    std::cout << "Start coroutine" << std::endl;
    co_await std::suspend_always{};
    std::cout << "Resume coroutine" << std::endl;
    co_return;
}

// 未来：静态反射示例（概念性，非实际C++代码）
/*
template<reflectable T>
void describe_type() {
    std::cout << "Type name: " << T::name() << std::endl;
    std::cout << "Member variables:" << std::endl;
    
    for (const auto& member : T::members()) {
        std::cout << "  - " << member.type().name() << " " << member.name() << std::endl;
    }
    
    std::cout << "Member functions:" << std::endl;
    for (const auto& function : T::functions()) {
        std::cout << "  - " << function.signature() << std::endl;
    }
}
*/
```

### 10.3 实际应用与最佳实践

#### 工程实践

- **编程规范**：遵循现代C++指南
- **构建系统**：使用CMake等跨平台工具
- **测试框架**：Google Test, Catch2等
- **设计模式**：适合C++的模式应用

#### 性能优化

- **编译期优化**：模板元编程、常量求值
- **内存布局**：缓存友好设计、数据结构对齐
- **移动语义**：避免不必要复制
- **并发化**：利用并发库提高性能

```cpp
// 最佳实践示例：RAII + 智能指针 + 移动语义
class Resource {
private:
    std::string name;
    std::vector<int> data;
    
public:
    Resource(std::string n, size_t size)
        : name(std::move(n)), data(size) {
        std::cout << "Resource " << name << " constructed" << std::endl;
    }
    
    ~Resource() {
        std::cout << "Resource " << name << " destroyed" << std::endl;
    }
    
    // 使用移动语义避免不必要复制
    Resource(Resource&& other) noexcept
        : name(std::move(other.name)), data(std::move(other.data)) {
        std::cout << "Resource moved" << std::endl;
    }
    
    Resource& operator=(Resource&& other) noexcept {
        if (this != &other) {
            name = std::move(other.name);
            data = std::move(other.data);
            std::cout << "Resource move assigned" << std::endl;
        }
        return *this;
    }
    
    // 禁用复制
    Resource(const Resource&) = delete;
    Resource& operator=(const Resource&) = delete;
};

class ResourceManager {
private:
    std::vector<std::unique_ptr<Resource>> resources;
    
public:
    void addResource(std::string name, size_t size) {
        resources.push_back(std::make_unique<Resource>(std::move(name), size));
    }
    
    void removeResource(size_t index) {
        if (index < resources.size()) {
            resources.erase(resources.begin() + index);
        }
    }
};

// 现代C++：结构化绑定 + 范围for + auto
void modern_cpp_features() {
    std::map<std::string, int> scores = {
        {"Alice", 95},
        {"Bob", 87},
        {"Charlie", 92}
    };
    
    // 结构化绑定
    for (const auto& [name, score] : scores) {
        std::cout << name << ": " << score << std::endl;
    }
    
    // 使用std::optional处理可能不存在的值
    std::optional<int> findScore(const std::string& name) {
        auto it = scores.find(name);
        if (it != scores.end()) {
            return it->second;
        }
        return std::nullopt;
    }
    
    if (auto score = findScore("David"); score) {
        std::cout << "David's score: " << *score << std::endl;
    } else {
        std::cout << "David not found" << std::endl;
    }
}
```

通过这些详细分析，我们对C++编程语言的各个方面进行了深入探讨，从基础概念到高级特质，从经典用法到现代实践。
C++的强大和灵活性使其在系统编程、高性能计算、游戏开发等领域保持着重要地位，
同时其复杂性也要求开发者对其内部机制有深入理解。
掌握这些知识将有助于编写更高效、更安全、更易维护的C++代码。

## 11. C++20/23新特质深入分析

### 11.1 概念与约束

#### 概念机制

- **定义**：为模板参数指定要求的语言机制
- **目的**：改进模板错误信息、明确文档、启用重载约束
- **语法**：`template <concept T> class X`或`template <typename T> requires concept<T> class X`

#### 核心概念

- **标准概念**：`std::integral`、`std::same_as`、`std::constructible_from`等
- **概念组合**：使用逻辑运算符组合概念
- **约束表达式**：`requires`子句和`requires`表达式

```cpp
// 概念与约束示例
# include <concepts>
# include <type_traits>
# include <iostream>

// 定义自己的概念
template<typename T>
concept Hashable = requires(T a) {
    { std::hash<T>{}(a) } -> std::convertible_to<std::size_t>;
};

template<typename T>
concept Sortable = requires(T a, T b) {
    { a < b } -> std::convertible_to<bool>;
    { a > b } -> std::convertible_to<bool>;
    { a <= b } -> std::convertible_to<bool>;
    { a >= b } -> std::convertible_to<bool>;
    { a == b } -> std::convertible_to<bool>;
    { a != b } -> std::convertible_to<bool>;
};

// 约束模板
template<Hashable T>
void print_hash(const T& value) {
    std::cout << "Hash: " << std::hash<T>{}(value) << std::endl;
}

// 概念组合
template<typename T>
concept Arithmetic = std::integral<T> || std::floating_point<T>;

// 类型约束
template<Arithmetic T>
T add(T a, T b) {
    return a + b;
}

// 使用requires表达式
template<typename T>
requires requires(T x) { x + x; } // 外层requires是子句，内层是表达式
T double_it(T x) {
    return x + x;
}

// 使用约束自动推导指引
template<typename T>
class Container {
public:
    Container(std::initializer_list<T> init) {}
};

// 约束构造函数模板
template<Sortable T>
Container(std::initializer_list<T>) -> Container<T>;

int main() {
    print_hash(42);        // OK：int是Hashable
    print_hash("hello");   // OK：const char*是Hashable
    // print_hash(std::cin); // 错误：std::istream不是Hashable
    
    std::cout << add(5, 10) << std::endl;           // OK：int是Arithmetic
    std::cout << add(3.14, 2.71) << std::endl;      // OK：double是Arithmetic
    // std::cout << add("a", "b") << std::endl;     // 错误：std::string不是Arithmetic
    
    std::cout << double_it(7) << std::endl;         // OK：int支持加法
    std::cout << double_it(std::string("abc")) << std::endl; // OK：string支持加法
    
    Container c = {1, 2, 3}; // 自动推导为Container<int>
}
```

### 11.2 协程机制

#### 协程基础

- **定义**：可以暂停和恢复执行的函数
- **关键字**：`co_await`、`co_yield`、`co_return`
- **工作原理**：通过编译器生成的状态机实现

#### 协程组件

- **promise_type**：控制协程状态、结果和行为
- **协程句柄**：协程状态的非拥有借用
- **awaitable**：定义暂停点行为的对象

```cpp
// 协程示例
# include <coroutine>
# include <iostream>
# include <thread>
# include <chrono>
# include <functional>

// 简单的协程类型
struct SimpleTask {
    struct promise_type {
        SimpleTask get_return_object() {
            return SimpleTask{std::coroutine_handle<promise_type>::from_promise(*this)};
        }
        std::suspend_never initial_suspend() { return {}; }
        std::suspend_never final_suspend() noexcept { return {}; }
        void return_void() {}
        void unhandled_exception() { std::terminate(); }
    };
    
    std::coroutine_handle<promise_type> handle;
    
    SimpleTask(std::coroutine_handle<promise_type> h) : handle(h) {}
    ~SimpleTask() {
        if (handle) handle.destroy();
    }
};

// 可恢复的任务
struct ResumableTask {
    struct promise_type {
        ResumableTask get_return_object() {
            return ResumableTask{std::coroutine_handle<promise_type>::from_promise(*this)};
        }
        std::suspend_always initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        void return_void() {}
        void unhandled_exception() { std::terminate(); }
    };
    
    std::coroutine_handle<promise_type> handle;
    
    ResumableTask(std::coroutine_handle<promise_type> h) : handle(h) {}
    ~ResumableTask() {
        if (handle) handle.destroy();
    }
    
    bool resume() {
        if (!handle.done())
            handle.resume();
        return !handle.done();
    }
};

// 自定义awaitable
struct Sleeper {
    std::chrono::milliseconds duration;
    
    bool await_ready() const { return false; }
    
    void await_suspend(std::coroutine_handle<> h) {
        std::thread([h, this]() {
            std::this_thread::sleep_for(duration);
            h.resume();
        }).detach();
    }
    
    void await_resume() {}
};

// 生成器协程
template<typename T>
class Generator {
public:
    struct promise_type {
        T value;
        
        Generator<T> get_return_object() {
            return Generator{std::coroutine_handle<promise_type>::from_promise(*this)};
        }
        
        std::suspend_always initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        std::suspend_always yield_value(T val) {
            value = val;
            return {};
        }
        void return_void() {}
        void unhandled_exception() { std::terminate(); }
    };
    
    std::coroutine_handle<promise_type> handle;
    
    Generator(std::coroutine_handle<promise_type> h) : handle(h) {}
    ~Generator() { if (handle) handle.destroy(); }
    
    T next() {
        handle.resume();
        if (handle.done()) throw std::out_of_range("Generator is done");
        return handle.promise().value;
    }
    
    bool has_next() {
        return !handle.done();
    }
};

// 协程示例1：简单任务
SimpleTask simple_coroutine() {
    std::cout << "协程开始" << std::endl;
    co_await std::suspend_never{};
    std::cout << "协程继续" << std::endl;
    co_return;
}

// 协程示例2：可恢复任务
ResumableTask counter(int max) {
    for (int i = 0; i < max; ++i) {
        std::cout << "计数: " << i << std::endl;
        co_await std::suspend_always{};
    }
}

// 协程示例3：异步等待
SimpleTask async_wait() {
    std::cout << "开始等待..." << std::endl;
    co_await Sleeper{std::chrono::milliseconds(1000)};
    std::cout << "等待1秒后" << std::endl;
    co_await Sleeper{std::chrono::milliseconds(2000)};
    std::cout << "又等待2秒后" << std::endl;
}

// 协程示例4：生成器
Generator<int> fibonacci(int n) {
    if (n > 0) co_yield 0;
    if (n > 1) co_yield 1;
    
    int a = 0, b = 1;
    for (int i = 2; i < n; ++i) {
        int next = a + b;
        co_yield next;
        a = b;
        b = next;
    }
}

void coroutine_examples() {
    // 简单协程
    std::cout << "--- 简单协程 ---" << std::endl;
    auto task1 = simple_coroutine();
    
    // 可恢复协程
    std::cout << "\n--- 可恢复协程 ---" << std::endl;
    auto task2 = counter(5);
    while (task2.resume()) {
        std::cout << "  主线程继续执行" << std::endl;
    }
    
    // 异步等待
    std::cout << "\n--- 异步等待 ---" << std::endl;
    auto task3 = async_wait();
    std::cout << "主线程等待异步任务..." << std::endl;
    std::this_thread::sleep_for(std::chrono::milliseconds(4000));
    
    // 生成器
    std::cout << "\n--- 斐波那契生成器 ---" << std::endl;
    auto fib = fibonacci(10);
    while (fib.has_next()) {
        try {
            std::cout << fib.next() << " ";
        } catch (const std::out_of_range&) {
            break;
        }
    }
    std::cout << std::endl;
}
```

### 11.3 模块系统

#### 模块基础

- **定义**：编译单元的逻辑分组，替代传统头文件
- **目的**：加速编译、避免宏污染、改进封装
- **语法**：`import`导入模块，`export`导出声明

#### 模块组件

- **模块声明**：`module my_module;`
- **导出声明**：`export int func();`
- **导入声明**：`import my_module;`
- **分区**：通过模块分区组织代码

```cpp
// 模块示例

// 文件：math.ixx（模块接口单元）
module;  // 全局模块片段，用于include传统头文件

# include <cmath>

export module math;  // 声明math模块

// 导出函数
export double square(double x) {
    return x * x;
}

export double cube(double x) {
    return x * x * x;
}

// 内部函数（不导出）
double internal_helper(double x) {
    return std::sqrt(x);
}

// 导出命名空间内的内容
export namespace math_constants {
    constexpr double pi = 3.14159265358979323846;
    constexpr double e = 2.71828182845904523536;
}

// 文件：math_advanced.ixx（模块分区）
export module math:advanced;  // math模块的advanced分区

export double power(double base, int exponent) {
    double result = 1.0;
    for (int i = 0; i < exponent; ++i) {
        result *= base;
    }
    return result;
}

// 文件：main.cpp（使用模块）
import math;  // 导入math模块
// import math.advanced;  // C++23允许这种语法
import :advanced;  // 导入指定分区

# include <iostream>

int main() {
    double x = 3.0;
    
    std::cout << "Square of " << x << ": " << square(x) << std::endl;
    std::cout << "Cube of " << x << ": " << cube(x) << std::endl;
    std::cout << "Power of " << x << "^4: " << power(x, 4) << std::endl;
    
    // 使用导出的常量
    std::cout << "Pi: " << math_constants::pi << std::endl;
    std::cout << "e: " << math_constants::e << std::endl;
    
    // internal_helper(x);  // 错误：内部函数不可访问
}

// 构建命令示例（不同编译器可能有所不同）
// clang++ -std=c++20 -fmodules math.ixx math_advanced.ixx main.cpp -o modules_example
// 或
// g++ -std=c++20 -fmodules-ts math.ixx math_advanced.ixx main.cpp -o modules_example
```

### 11.4 范围与视图

#### 范围库

- **定义**：表示元素序列的抽象
- **目的**：简化序列算法，支持延迟计算和组合
- **组件**：范围适配器、范围工厂、视图

#### 主要特质

- **视图**：轻量级、非拥有元素的范围
- **适配器**：转换范围的操作
- **延迟求值**：仅在需要时才计算结果

```cpp
// 范围与视图示例
# include <ranges>
# include <vector>
# include <iostream>
# include <algorithm>
# include <string>

void ranges_views_examples() {
    std::vector<int> numbers = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    
    // 基本范围操作
    for (int n : numbers) {
        std::cout << n << " ";
    }
    std::cout << std::endl;
    
    // 过滤视图：只保留偶数
    auto even = numbers | std::views::filter([](int n) { return n % 2 == 0; });
    for (int n : even) {
        std::cout << n << " ";  // 输出：2 4 6 8 10
    }
    std::cout << std::endl;
    
    // 转换视图：平方所有元素
    auto squares = numbers | std::views::transform([](int n) { return n * n; });
    for (int n : squares) {
        std::cout << n << " ";  // 输出：1 4 9 16 25 36 49 64 81 100
    }
    std::cout << std::endl;
    
    // 组合视图：过滤后转换
    auto even_squares = numbers 
        | std::views::filter([](int n) { return n % 2 == 0; })
        | std::views::transform([](int n) { return n * n; });
    
    for (int n : even_squares) {
        std::cout << n << " ";  // 输出：4 16 36 64 100
    }
    std::cout << std::endl;
    
    // 取前N个元素
    auto first_three = numbers | std::views::take(3);
    for (int n : first_three) {
        std::cout << n << " ";  // 输出：1 2 3
    }
    std::cout << std::endl;
    
    // 跳过前N个元素
    auto skip_first_five = numbers | std::views::drop(5);
    for (int n : skip_first_five) {
        std::cout << n << " ";  // 输出：6 7 8 9 10
    }
    std::cout << std::endl;
    
    // 反向视图
    auto reversed = numbers | std::views::reverse;
    for (int n : reversed) {
        std::cout << n << " ";  // 输出：10 9 8 7 6 5 4 3 2 1
    }
    std::cout << std::endl;
    
    // 复杂组合：取偶数，平方，取前3个
    auto complex = numbers 
        | std::views::filter([](int n) { return n % 2 == 0; })
        | std::views::transform([](int n) { return n * n; })
        | std::views::take(3);
    
    for (int n : complex) {
        std::cout << n << " ";  // 输出：4 16 36
    }
    std::cout << std::endl;
    
    // 字符串视图
    std::string str = "Hello, Ranges!";
    auto chars = str | std::views::split(' ');
    for (auto word : chars) {
        for (char c : word) {
            std::cout << c;
        }
        std::cout << std::endl;
    }
    
    // 无限序列（惰性求值）
    auto infinite = std::views::iota(1)  // 从1开始的无限序列
        | std::views::transform([](int n) { return n * n; })
        | std::views::take(10);  // 只取前10个
    
    for (int n : infinite) {
        std::cout << n << " ";  // 输出：1 4 9 16 25 36 49 64 81 100
    }
    std::cout << std::endl;
}
```

### 11.5 格式库

#### 11.5.1 格式库基础

- **定义**：类型安全的格式化库，替代`printf`和`iostream`
- **核心**：`std::format`函数和相关类型
- **语法**：基于Python的格式字符串语法

#### 11.5.2 主要特质

- **类型安全**：编译时检查参数类型匹配
- **位置参数**：`{0}, {1}, ...`指定参数位置
- **命名参数**：通过上下文参数提供值
- **格式描述符**：控制输出格式

```cpp
// 格式库示例
# include <format>
# include <iostream>
# include <string>
# include <vector>

void format_examples() {
    // 基本格式化
    std::string message = std::format("Hello, {}!", "World");
    std::cout << message << std::endl;  // 输出：Hello, World!
    
    // 多参数格式化
    std::string result = std::format("The result is: {}", 42);
    std::cout << result << std::endl;  // 输出：The result is: 42
    
    // 参数索引
    std::string reordered = std::format("{1} comes before {0}", "World", "Hello");
    std::cout << reordered << std::endl;  // 输出：Hello comes before World
    
    // 参数重用
    std::string repeated = std::format("{0}, {0}, {0}!", "Hello");
    std::cout << repeated << std::endl;  // 输出：Hello, Hello, Hello!
    
    // 数值格式化
    // 十六进制格式
    std::string hex = std::format("Hex: {0:x}, uppercase: {0:X}", 255);
    std::cout << hex << std::endl;  // 输出：Hex: ff, uppercase: FF
    
    // 小数位数
    std::string precision = std::format("Pi: {:.3f}", 3.14159265359);
    std::cout << precision << std::endl;  // 输出：Pi: 3.142
    
    // 填充与对齐
    std::string padded = std::format("{:*^15}", "centered");
    std::cout << padded << std::endl;  // 输出：***centered****
    
    std::string left_aligned = std::format("{:<10}", "left");
    std::cout << left_aligned << std::endl;  // 输出：left      
    
    std::string right_aligned = std::format("{:>10}", "right");
    std::cout << right_aligned << std::endl;  // 输出：     right
    
    // 自定义类型格式化
    struct Point {
        double x, y;
    };
    
    // 为Point实现格式化支持
    template<>
    struct std::formatter<Point> {
        constexpr auto parse(std::format_parse_context& ctx) {
            return ctx.begin();
        }
        
        auto format(const Point& p, std::format_context& ctx) const {
            return std::format_to(ctx.out(), "({:.1f}, {:.1f})", p.x, p.y);
        }
    };
    
    Point p{3.5, 7.2};
    std::string point_str = std::format("Point: {}", p);
    std::cout << point_str << std::endl;  // 输出：Point: (3.5, 7.2)
    
    // 条件格式化
    bool condition = true;
    std::string conditional = std::format("Status: {}", condition ? "Active" : "Inactive");
    std::cout << conditional << std::endl;  // 输出：Status: Active
    
    // 容器格式化
    std::vector<int> vec = {1, 2, 3, 4, 5};
    std::string vec_str;
    vec_str += std::format("Vector: [");
    for (size_t i = 0; i < vec.size(); ++i) {
        if (i > 0) vec_str += ", ";
        vec_str += std::format("{}", vec[i]);
    }
    vec_str += "]";
    std::cout << vec_str << std::endl;  // 输出：Vector: [1, 2, 3, 4, 5]
}
```

## 12. 特定领域C++应用

### 12.1 嵌入式系统

#### 嵌入式C++特点

- **资源限制**：有限内存和处理能力
- **实时性要求**：确定性响应时间
- **无异常**：通常禁用RTTI和异常
- **裸机编程**：直接硬件访问

#### 嵌入式编程技术

- **静态内存分配**：避免动态内存
- **固定大小容器**：使用`std::array`而非`std::vector`
- **中断处理**：低级中断服务例程
- **位操作**：寄存器访问和位字段操作

```cpp
// 嵌入式系统C++示例
// 注意：此代码只是示意性的，实际嵌入式代码取决于特定硬件平台

// 硬件抽象层 - 寄存器定义
namespace hardware {
    // 设备寄存器地址（示例地址）
    constexpr uintptr_t GPIO_BASE = 0x40020000;
    constexpr uintptr_t GPIO_MODE = GPIO_BASE + 0x00;
    constexpr uintptr_t GPIO_OUTPUT = GPIO_BASE + 0x04;
    
    // 寄存器访问函数
    template<typename T = uint32_t>
    inline T read_reg(uintptr_t addr) {
        return *reinterpret_cast<volatile T*>(addr);
    }
    
    template<typename T = uint32_t>
    inline void write_reg(uintptr_t addr, T value) {
        *reinterpret_cast<volatile T*>(addr) = value;
    }
    
    // 位操作辅助函数
    inline void set_bit(uintptr_t addr, uint8_t bit) {
        write_reg(addr, read_reg(addr) | (1 << bit));
    }
    
    inline void clear_bit(uintptr_t addr, uint8_t bit) {
        write_reg(addr, read_reg(addr) & ~(1 << bit));
    }
    
    inline bool read_bit(uintptr_t addr, uint8_t bit) {
        return (read_reg(addr) & (1 << bit)) != 0;
    }
}

// 固定大小缓冲区
template<typename T, size_t Size>
class CircularBuffer {
private:
    std::array<T, Size> buffer;
    size_t head = 0;
    size_t tail = 0;
    bool full = false;
    
public:
    bool push(const T& item) {
        if (full) return false;
        
        buffer[head] = item;
        head = (head + 1) % Size;
        full = head == tail;
        return true;
    }
    
    bool pop(T& item) {
        if (empty()) return false;
        
        item = buffer[tail];
        tail = (tail + 1) % Size;
        full = false;
        return true;
    }
    
    bool empty() const {
        return !full && (head == tail);
    }
    
    bool is_full() const {
        return full;
    }
};

// LED控制器类
class LedController {
private:
    static constexpr uint8_t LED_PIN = 5;  // 示例引脚号
    
public:
    // 初始化LED引脚为输出模式
    void init() {
        // 设置GPIO引脚为输出模式
        uint32_t mode = hardware::read_reg(hardware::GPIO_MODE);
        mode &= ~(0x3 << (LED_PIN * 2));  // 清除旧模式
        mode |= (0x1 << (LED_PIN * 2));   // 设置为输出模式
        hardware::write_reg(hardware::GPIO_MODE, mode);
    }
    
    // 打开LED
    void on() {
        hardware::set_bit(hardware::GPIO_OUTPUT, LED_PIN);
    }
    
    // 关闭LED
    void off() {
        hardware::clear_bit(hardware::GPIO_OUTPUT, LED_PIN);
    }
    
    // 切换LED状态
    void toggle() {
        if (hardware::read_bit(hardware::GPIO_OUTPUT, LED_PIN)) {
            off();
        } else {
            on();
        }
    }
};

// 中断服务例程（示例）
extern "C" void ISR_TIMER0() {
    static LedController led;
    static bool initialized = false;
    
    if (!initialized) {
        led.init();
        initialized = true;
    }
    
    // 在定时器中断中切换LED状态
    led.toggle();
}

// 主循环函数
void embedded_main() {
    // 初始化硬件
    LedController led;
    led.init();
    
    // 创建固定大小的消息缓冲区
    CircularBuffer<uint8_t, 16> msgBuffer;
    
    // 主循环
    while (true) {
        // 处理消息
        uint8_t msg;
        if (msgBuffer.pop(msg)) {
            // 基于消息处理LED
            if (msg == 0x01) {
                led.on();
            } else if (msg == 0x02) {
                led.off();
            } else if (msg == 0x03) {
                led.toggle();
            }
        }
        
        // 低功耗模式等待中断
        // 平台相关的代码
    }
}
```

### 12.2 游戏开发

#### 游戏引擎设计

- **组件系统**：实体-组件-系统架构
- **资源管理**：材质、模型、音频等
- **高性能**：缓存友好数据布局
- **并发处理**：多线程任务系统

#### 游戏开发技术

- **碰撞检测**：空间分区、包围盒
- **物理引擎**：刚体动力学、约束解算
- **渲染管线**：3D图形API接口
- **脚本集成**：嵌入式脚本语言

```cpp
// 游戏开发C++示例
# include <vector>
# include <unordered_map>
# include <string>
# include <memory>
# include <algorithm>
# include <functional>

// 游戏实体-组件-系统架构

// 组件基类
class Component {
public:
    virtual ~Component() = default;
    virtual void update(float deltaTime) {}
};

// 具体组件：变换
class TransformComponent : public Component {
private:
    float x = 0, y = 0, z = 0;
    float rotationX = 0, rotationY = 0, rotationZ = 0;
    float scaleX = 1, scaleY = 1, scaleZ = 1;
    
public:
    void setPosition(float x, float y, float z) {
        this->x = x;
        this->y = y;
        this->z = z;
    }
    
    void setRotation(float x, float y, float z) {
        rotationX = x;
        rotationY = y;
        rotationZ = z;
    }
    
    void setScale(float x, float y, float z) {
        scaleX = x;
        scaleY = y;
        scaleZ = z;
    }
    
    // 获取位置、旋转、缩放的方法
    std::tuple<float, float, float> getPosition() const {
        return {x, y, z};
    }
    
    std::tuple<float, float, float> getRotation() const {
        return {rotationX, rotationY, rotationZ};
    }
    
    std::tuple<float, float, float> getScale() const {
        return {scaleX, scaleY, scaleZ};
    }
};

// 具体组件：渲染
class RenderComponent : public Component {
private:
    std::string meshPath;
    std::string texturePath;
    bool visible = true;
    
public:
    RenderComponent(const std::string& mesh, const std::string& texture)
        : meshPath(mesh), texturePath(texture) {}
    
    void setVisible(bool visible) {
        this->visible = visible;
    }
    
    bool isVisible() const {
        return visible;
    }
    
    const std::string& getMesh() const {
        return meshPath;
    }
    
    const std::string& getTexture() const {
        return texturePath;
    }
};

// 具体组件：物理
class PhysicsComponent : public Component {
private:
    float mass = 1.0f;
    float velocityX = 0, velocityY = 0, velocityZ = 0;
    bool hasGravity = true;
    
public:
    PhysicsComponent(float mass) : mass(mass) {}
    
    void setVelocity(float x, float y, float z) {
        velocityX = x;
        velocityY = y;
        velocityZ = z;
    }
    
    void setGravity(bool enabled) {
        hasGravity = enabled;
    }
    
    void update(float deltaTime) override {
        // 简单物理更新
        if (hasGravity) {
            velocityY -= 9.8f * deltaTime;
        }
        
        // 更新位置逻辑
    }
};

// 实体类
class Entity {
private:
    uint64_t id;
    std::string name;
    std::unordered_map<std::string, std::unique_ptr<Component>> components;
    
public:
    Entity(uint64_t id, const std::string& name) : id(id), name(name) {}
    
    template<typename T, typename... Args>
    T* addComponent(const std::string& key, Args&&... args) {
        auto component = std::make_unique<T>(std::forward<Args>(args)...);
        T* comp_ptr = component.get();
        components[key] = std::move(component);
        return comp_ptr;
    }
    
    Component* getComponent(const std::string& key) {
        auto it = components.find(key);
        return it != components.end() ? it->second.get() : nullptr;
    }
    
    template<typename T>
    T* getComponentAs(const std::string& key) {
        return dynamic_cast<T*>(getComponent(key));
    }
    
    void update(float deltaTime) {
        for (auto& [key, component] : components) {
            component->update(deltaTime);
        }
    }
    
    uint64_t getId() const { return id; }
    const std::string& getName() const { return name; }
};

// 系统基类
class System {
public:
    virtual ~System() = default;
    virtual void update(std::vector<Entity*>& entities, float deltaTime) = 0;
};

// 具体系统：渲染系统
class RenderSystem : public System {
public:
    void update(std::vector<Entity*>& entities, float deltaTime) override {
        for (auto entity : entities) {
            auto render = entity->getComponentAs<RenderComponent>("render");
            auto transform = entity->getComponentAs<TransformComponent>("transform");
            
            if (render && transform && render->isVisible()) {
                // 在实际引擎中，这里会调用图形API渲染实体
                auto [x, y, z] = transform->getPosition();
                std::cout << "Rendering " << entity->getName() 
                          << " at position (" << x << ", " << y << ", " << z << ")"
                          << " using mesh " << render->getMesh() 
                          << " and texture " << render->getTexture() << std::endl;
            }
        }
    }
};

// 具体系统：物理系统
class PhysicsSystem : public System {
public:
    void update(std::vector<Entity*>& entities, float deltaTime) override {
        for (auto entity : entities) {
            auto physics = entity->getComponentAs<PhysicsComponent>("physics");
            auto transform = entity->getComponentAs<TransformComponent>("transform");
            
            if (physics && transform) {
                // 更新物理组件
                physics->update(deltaTime);
                
                // 在实际引擎中，这里会处理碰撞检测、物理响应等
                std::cout << "Updating physics for " << entity->getName() << std::endl;
            }
        }
    }
};

// 游戏世界
class GameWorld {
private:
    std::vector<std::unique_ptr<Entity>> entities;
    std::vector<st

```cpp
// 游戏世界(续)
class GameWorld {
private:
    std::vector<std::unique_ptr<Entity>> entities;
    std::vector<std::unique_ptr<System>> systems;
    uint64_t nextEntityId = 0;
    
public:
    Entity* createEntity(const std::string& name) {
        auto entity = std::make_unique<Entity>(nextEntityId++, name);
        Entity* ptr = entity.get();
        entities.push_back(std::move(entity));
        return ptr;
    }
    
    void addSystem(std::unique_ptr<System> system) {
        systems.push_back(std::move(system));
    }
    
    void update(float deltaTime) {
        // 准备实体指针列表供系统使用
        std::vector<Entity*> entityPtrs;
        for (auto& entity : entities) {
            entityPtrs.push_back(entity.get());
        }
        
        // 更新所有系统
        for (auto& system : systems) {
            system->update(entityPtrs, deltaTime);
        }
    }
};

// 资源管理
class ResourceManager {
private:
    struct Resource {
        void* data;
        size_t refCount;
        
        Resource() : data(nullptr), refCount(0) {}
        ~Resource() { if (data) free(data); }
    };
    
    std::unordered_map<std::string, Resource> resources;
    
public:
    template<typename T>
    T* loadResource(const std::string& path) {
        auto it = resources.find(path);
        if (it != resources.end()) {
            it->second.refCount++;
            return static_cast<T*>(it->second.data);
        }
        
        // 实际应用中，这里会加载文件、创建纹理等
        T* resource = new T();
        resources[path].data = resource;
        resources[path].refCount = 1;
        
        std::cout << "Loaded resource: " << path << std::endl;
        return resource;
    }
    
    void releaseResource(const std::string& path) {
        auto it = resources.find(path);
        if (it != resources.end()) {
            if (--it->second.refCount == 0) {
                std::cout << "Unloaded resource: " << path << std::endl;
                resources.erase(it);
            }
        }
    }
    
    ~ResourceManager() {
        if (!resources.empty()) {
            std::cout << "Warning: " << resources.size() << " resources not properly released" << std::endl;
        }
    }
};

// 游戏示例代码
void game_development_example() {
    // 创建游戏世界
    GameWorld world;
    
    // 添加系统
    world.addSystem(std::make_unique<PhysicsSystem>());
    world.addSystem(std::make_unique<RenderSystem>());
    
    // 创建玩家实体
    Entity* player = world.createEntity("Player");
    
    // 添加组件
    auto transform = player->addComponent<TransformComponent>("transform");
    transform->setPosition(0, 0, 0);
    
    player->addComponent<RenderComponent>("render", "player.mesh", "player.texture");
    player->addComponent<PhysicsComponent>("physics", 70.0f);
    
    // 创建敌人实体
    Entity* enemy = world.createEntity("Enemy");
    auto enemyTransform = enemy->addComponent<TransformComponent>("transform");
    enemyTransform->setPosition(10, 0, 5);
    
    enemy->addComponent<RenderComponent>("render", "enemy.mesh", "enemy.texture");
    enemy->addComponent<PhysicsComponent>("physics", 50.0f);
    
    // 游戏主循环
    float deltaTime = 0.016f; // 约60FPS
    for (int frame = 0; frame < 10; ++frame) {
        std::cout << "\n--- Frame " << frame << " ---" << std::endl;
        
        // 更新游戏世界
        world.update(deltaTime);
        
        // 在实际游戏中，这里会处理输入、AI、音频等
    }
}
```

### 12.3 高性能计算

#### 高性能计算特点

- **性能优化**：SIMD指令、缓存友好设计
- **并发计算**：多线程、GPU计算
- **内存管理**：内存池、自定义分配器
- **算法优化**：数据布局、向量化

#### HPC技术

- **SIMD指令集**：SSE、AVX、NEON
- **缓存优化**：数据对齐、预取、减少分支
- **并发库**：OpenMP、MPI、TBB
- **GPU编程**：CUDA、OpenCL

```cpp
// 高性能计算C++示例
# include <iostream>
# include <vector>
# include <chrono>
# include <numeric>
# include <thread>
# include <future>
# include <cstring>

// 使用SIMD指令优化向量加法
# ifdef __SSE4_1__
# include <immintrin.h>

void vector_add_simd(const float* a, const float* b, float* result, size_t size) {
    // 确保数据对齐
    constexpr size_t VECTOR_SIZE = 4; // SSE使用128位寄存器，可以同时处理4个float
    
    // 处理可向量化部分
    size_t aligned_size = size - (size % VECTOR_SIZE);
    for (size_t i = 0; i < aligned_size; i += VECTOR_SIZE) {
        __m128 va = _mm_loadu_ps(a + i);
        __m128 vb = _mm_loadu_ps(b + i);
        __m128 vresult = _mm_add_ps(va, vb);
        _mm_storeu_ps(result + i, vresult);
    }
    
    // 处理剩余部分
    for (size_t i = aligned_size; i < size; ++i) {
        result[i] = a[i] + b[i];
    }
}
# else
void vector_add_simd(const float* a, const float* b, float* result, size_t size) {
    // 降级为标准实现
    for (size_t i = 0; i < size; ++i) {
        result[i] = a[i] + b[i];
    }
}
# endif

// 标准向量加法
void vector_add_standard(const float* a, const float* b, float* result, size_t size) {
    for (size_t i = 0; i < size; ++i) {
        result[i] = a[i] + b[i];
    }
}

// 多线程向量加法
void vector_add_parallel(const float* a, const float* b, float* result, size_t size, size_t num_threads) {
    std::vector<std::future<void>> futures;
    
    size_t chunk_size = size / num_threads;
    
    for (size_t t = 0; t < num_threads; ++t) {
        size_t start = t * chunk_size;
        size_t end = (t == num_threads - 1) ? size : (t + 1) * chunk_size;
        
        futures.push_back(std::async(std::launch::async, [=]() {
            for (size_t i = start; i < end; ++i) {
                result[i] = a[i] + b[i];
            }
        }));
    }
    
    // 等待所有线程完成
    for (auto& future : futures) {
        future.wait();
    }
}

// 缓存友好的矩阵乘法
void matrix_multiply_cache_friendly(const float* a, const float* b, float* result, size_t rows_a, size_t cols_a, size_t cols_b) {
    // 假设b的行数等于a的列数
    
    // 传统实现：C[i][j] += A[i][k] * B[k][j]
    // 将B转置可以提高缓存命中率
    std::vector<float> b_transposed(cols_a * cols_b);
    
    // 转置B
    for (size_t i = 0; i < cols_a; ++i) {
        for (size_t j = 0; j < cols_b; ++j) {
            b_transposed[j * cols_a + i] = b[i * cols_b + j];
        }
    }
    
    // 计算乘积
    for (size_t i = 0; i < rows_a; ++i) {
        for (size_t j = 0; j < cols_b; ++j) {
            float sum = 0.0f;
            
            // 使用转置后的B，提高缓存局部性
            for (size_t k = 0; k < cols_a; ++k) {
                sum += a[i * cols_a + k] * b_transposed[j * cols_a + k];
            }
            
            result[i * cols_b + j] = sum;
        }
    }
}

// 内存池实现
class MemoryPool {
private:
    void* pool;
    size_t pool_size;
    size_t used;
    
public:
    MemoryPool(size_t size) : pool_size(size), used(0) {
        pool = std::aligned_alloc(64, size); // 64字节对齐，适合AVX指令
    }
    
    ~MemoryPool() {
        free(pool);
    }
    
    void* allocate(size_t size, size_t alignment = 8) {
        // 对齐used指针
        size_t aligned_used = (used + alignment - 1) & ~(alignment - 1);
        
        if (aligned_used + size > pool_size) {
            return nullptr; // 内存不足
        }
        
        void* ptr = static_cast<char*>(pool) + aligned_used;
        used = aligned_used + size;
        return ptr;
    }
    
    void reset() {
        used = 0;
    }
};

// 高性能计算示例
void hpc_examples() {
    constexpr size_t VECTOR_SIZE = 10000000;
    constexpr size_t NUM_THREADS = 4;
    
    // 分配向量
    std::vector<float> a(VECTOR_SIZE), b(VECTOR_SIZE), result(VECTOR_SIZE);
    
    // 初始化
    for (size_t i = 0; i < VECTOR_SIZE; ++i) {
        a[i] = static_cast<float>(i);
        b[i] = static_cast<float>(VECTOR_SIZE - i);
    }
    
    // 时间测量
    auto time_function = [](const std::string& name, auto func) {
        auto start = std::chrono::high_resolution_clock::now();
        func();
        auto end = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> elapsed = end - start;
        std::cout << name << " took " << elapsed.count() << " ms" << std::endl;
    };
    
    // 标准向量加法
    time_function("Standard vector addition", [&]() {
        vector_add_standard(a.data(), b.data(), result.data(), VECTOR_SIZE);
    });
    
    // SIMD向量加法
    time_function("SIMD vector addition", [&]() {
        vector_add_simd(a.data(), b.data(), result.data(), VECTOR_SIZE);
    });
    
    // 多线程向量加法
    time_function("Parallel vector addition", [&]() {
        vector_add_parallel(a.data(), b.data(), result.data(), VECTOR_SIZE, NUM_THREADS);
    });
    
    // 矩阵乘法示例
    constexpr size_t MATRIX_SIZE = 500;
    std::vector<float> matrix_a(MATRIX_SIZE * MATRIX_SIZE);
    std::vector<float> matrix_b(MATRIX_SIZE * MATRIX_SIZE);
    std::vector<float> matrix_c(MATRIX_SIZE * MATRIX_SIZE);
    
    // 初始化矩阵
    for (size_t i = 0; i < MATRIX_SIZE * MATRIX_SIZE; ++i) {
        matrix_a[i] = static_cast<float>(i % 10);
        matrix_b[i] = static_cast<float>((i + 5) % 10);
    }
    
    // 缓存友好的矩阵乘法
    time_function("Cache-friendly matrix multiplication", [&]() {
        matrix_multiply_cache_friendly(matrix_a.data(), matrix_b.data(), matrix_c.data(), 
                                      MATRIX_SIZE, MATRIX_SIZE, MATRIX_SIZE);
    });
    
    // 内存池示例
    MemoryPool pool(1024 * 1024); // 1MB内存池
    
    float* pooled_vector = static_cast<float*>(pool.allocate(100 * sizeof(float), 32));
    if (pooled_vector) {
        for (size_t i = 0; i < 100; ++i) {
            pooled_vector[i] = static_cast<float>(i);
        }
        
        float sum = std::accumulate(pooled_vector, pooled_vector + 100, 0.0f);
        std::cout << "Sum of pooled vector: " << sum << std::endl;
    }
    
    pool.reset();
}
```

### 12.4 金融系统

#### 金融软件特质

- **低延迟**：交易系统的实时响应
- **高可用性**：容错和冗余设计
- **精确计算**：定点数和特殊浮点处理
- **风险管理**：模拟和分析

#### 金融编程技术

- **交易系统**：订单匹配、市场数据处理
- **风险模型**：蒙特卡洛模拟、期权定价
- **精确算术**：定点数、多精度库
- **时间序列**：历史数据分析与预测

```cpp
// 金融系统C++示例
# include <iostream>
# include <vector>
# include <queue>
# include <random>
# include <cmath>
# include <numeric>
# include <iomanip>
# include <unordered_map>

// 定点数类
class FixedPoint {
private:
    int64_t value;
    static constexpr int SCALE = 10000; // 四位小数精度
    
public:
    FixedPoint() : value(0) {}
    
    explicit FixedPoint(double d) : value(static_cast<int64_t>(d * SCALE)) {}
    
    FixedPoint(int64_t v) : value(v * SCALE) {}
    
    FixedPoint operator+(const FixedPoint& other) const {
        FixedPoint result;
        result.value = value + other.value;
        return result;
    }
    
    FixedPoint operator-(const FixedPoint& other) const {
        FixedPoint result;
        result.value = value - other.value;
        return result;
    }
    
    FixedPoint operator*(const FixedPoint& other) const {
        FixedPoint result;
        result.value = (value * other.value) / SCALE;
        return result;
    }
    
    FixedPoint operator/(const FixedPoint& other) const {
        FixedPoint result;
        result.value = (value * SCALE) / other.value;
        return result;
    }
    
    bool operator<(const FixedPoint& other) const {
        return value < other.value;
    }
    
    bool operator>(const FixedPoint& other) const {
        return value > other.value;
    }
    
    bool operator==(const FixedPoint& other) const {
        return value == other.value;
    }
    
    double toDouble() const {
        return static_cast<double>(value) / SCALE;
    }
    
    std::string toString() const {
        std::stringstream ss;
        ss << std::fixed << std::setprecision(4) << toDouble();
        return ss.str();
    }
};

// 市场数据类型
struct MarketData {
    std::string symbol;
    FixedPoint bid;
    FixedPoint ask;
    uint64_t timestamp;
};

// 订单类型
enum class OrderSide { BUY, SELL };

struct Order {
    uint64_t orderId;
    std::string symbol;
    OrderSide side;
    FixedPoint price;
    int quantity;
    uint64_t timestamp;
    std::string traderId;
    
    // 比较运算符，用于订单队列排序
    bool operator<(const Order& other) const {
        if (side == OrderSide::BUY) {
            // 买单按价格降序（高价优先）
            return price < other.price;
        } else {
            // 卖单按价格升序（低价优先）
            return price > other.price;
        }
    }
};

// 成交记录
struct Trade {
    uint64_t tradeId;
    uint64_t buyOrderId;
    uint64_t sellOrderId;
    std::string symbol;
    FixedPoint price;
    int quantity;
    uint64_t timestamp;
};

// 订单簿
class OrderBook {
private:
    std::string symbol;
    std::priority_queue<Order> buyOrders;
    std::priority_queue<Order> sellOrders;
    std::vector<Trade> trades;
    uint64_t nextTradeId = 1;
    
public:
    OrderBook(const std::string& sym) : symbol(sym) {}
    
    // 添加订单
    void addOrder(const Order& order) {
        if (order.symbol != symbol) {
            throw std::invalid_argument("Order symbol doesn't match order book");
        }
        
        if (order.side == OrderSide::BUY) {
            buyOrders.push(order);
        } else {
            sellOrders.push(order);
        }
        
        // 尝试撮合订单
        matchOrders();
    }
    
    // 撮合订单
    void matchOrders() {
        while (!buyOrders.empty() && !sellOrders.empty()) {
            Order buyOrder = buyOrders.top();
            Order sellOrder = sellOrders.top();
            
            // 如果最高买价小于最低卖价，无法撮合
            if (buyOrder.price < sellOrder.price) {
                break;
            }
            
            // 移除顶部订单
            buyOrders.pop();
            sellOrders.pop();
            
            // 确定成交量
            int tradeQuantity = std::min(buyOrder.quantity, sellOrder.quantity);
            
            // 创建成交记录
            Trade trade{
                nextTradeId++,
                buyOrder.orderId,
                sellOrder.orderId,
                symbol,
                sellOrder.price,  // 通常以卖价成交
                tradeQuantity,
                getCurrentTimestamp()
            };
            
            trades.push_back(trade);
            
            std::cout << "Trade executed: " << tradeQuantity 
                      << " of " << symbol 
                      << " at " << sellOrder.price.toString() 
                      << std::endl;
            
            // 处理部分成交
            buyOrder.quantity -= tradeQuantity;
            sellOrder.quantity -= tradeQuantity;
            
            // 如果订单还有剩余，重新放回队列
            if (buyOrder.quantity > 0) {
                buyOrders.push(buyOrder);
            }
            
            if (sellOrder.quantity > 0) {
                sellOrders.push(sellOrder);
            }
        }
    }
    
    // 获取当前最优买卖价
    std::pair<FixedPoint, FixedPoint> getBestPrices() const {
        FixedPoint bestBid(0.0);
        FixedPoint bestAsk(1000000.0);  // 设一个很大的初始值
        
        if (!buyOrders.empty()) {
            bestBid = buyOrders.top().price;
        }
        
        if (!sellOrders.empty()) {
            bestAsk = sellOrders.top().price;
        }
        
        return {bestBid, bestAsk};
    }
    
    // 获取成交历史
    const std::vector<Trade>& getTradeHistory() const {
        return trades;
    }
    
private:
    uint64_t getCurrentTimestamp() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::system_clock::now().time_since_epoch()
        ).count();
    }
};

// 蒙特卡洛期权定价
class OptionPricer {
private:
    std::mt19937_64 rng;
    
public:
    OptionPricer() : rng(std::random_device{}()) {}
    
    // 欧式看涨期权蒙特卡洛定价
    double priceEuropeanCall(double spot, double strike, double volatility, 
                            double riskFreeRate, double timeToMaturity, 
                            int numSimulations) {
        std::normal_distribution<double> normalDist(0.0, 1.0);
        
        double dt = timeToMaturity;
        double drift = (riskFreeRate - 0.5 * volatility * volatility) * dt;
        double diffusion = volatility * std::sqrt(dt);
        
        double sumPayoffs = 0.0;
        
        for (int i = 0; i < numSimulations; ++i) {
            double z = normalDist(rng);
            double stockPrice = spot * std::exp(drift + diffusion * z);
            double payoff = std::max(stockPrice - strike, 0.0);
            sumPayoffs += payoff;
        }
        
        double mean = sumPayoffs / numSimulations;
        double price = mean * std::exp(-riskFreeRate * timeToMaturity);
        
        return price;
    }
    
    // 欧式看跌期权蒙特卡洛定价
    double priceEuropeanPut(double spot, double strike, double volatility, 
                           double riskFreeRate, double timeToMaturity, 
                           int numSimulations) {
        std::normal_distribution<double> normalDist(0.0, 1.0);
        
        double dt = timeToMaturity;
        double drift = (riskFreeRate - 0.5 * volatility * volatility) * dt;
        double diffusion = volatility * std::sqrt(dt);
        
        double sumPayoffs = 0.0;
        
        for (int i = 0; i < numSimulations; ++i) {
            double z = normalDist(rng);
            double stockPrice = spot * std::exp(drift + diffusion * z);
            double payoff = std::max(strike - stockPrice, 0.0);
            sumPayoffs += payoff;
        }
        
        double mean = sumPayoffs / numSimulations;
        double price = mean * std::exp(-riskFreeRate * timeToMaturity);
        
        return price;
    }
};

// 投资组合风险分析
class PortfolioAnalyzer {
private:
    struct Position {
        std::string symbol;
        int quantity;
        double entryPrice;
    };
    
    std::vector<Position> positions;
    std::unordered_map<std::string, double> currentPrices;
    
public:
    void addPosition(const std::string& symbol, int quantity, double entryPrice) {
        positions.push_back({symbol, quantity, entryPrice});
        currentPrices[symbol] = entryPrice;  // 初始化当前价格为买入价格
    }
    
    void updatePrice(const std::string& symbol, double price) {
        currentPrices[symbol] = price;
    }
    
    // 计算投资组合总价值
    double calculatePortfolioValue() const {
        double totalValue = 0.0;
        
        for (const auto& position : positions) {
            auto it = currentPrices.find(position.symbol);
            if (it != currentPrices.end()) {
                totalValue += position.quantity * it->second;
            }
        }
        
        return totalValue;
    }
    
    // 计算投资组合收益
    double calculatePortfolioReturn() const {
        double currentValue = calculatePortfolioValue();
        double initialValue = 0.0;
        
        for (const auto& position : positions) {
            initialValue += position.quantity * position.entryPrice;
        }
        
        if (initialValue == 0.0) {
            return 0.0;
        }
        
        return (currentValue - initialValue) / initialValue * 100.0;
    }
    
    // 计算投资组合风险（简单标准差）
    double calculatePortfolioRisk(int numSimulations, double volatility) {
        std::mt19937_64 rng(std::random_device{}());
        std::normal_distribution<double> normalDist(0.0, 1.0);
        
        double currentValue = calculatePortfolioValue();
        std::vector<double> simulatedReturns(numSimulations);
        
        for (int i = 0; i < numSimulations; ++i) {
            double simulatedValue = 0.0;
            
            for (const auto& position : positions) {
                auto it = currentPrices.find(position.symbol);
                if (it != currentPrices.end()) {
                    double currentPrice = it->second;
                    double z = normalDist(rng);
                    double simulatedPrice = currentPrice * (1.0 + volatility * z);
                    simulatedValue += position.quantity * simulatedPrice;
                }
            }
            
            double simulatedReturn = (simulatedValue - currentValue) / currentValue;
            simulatedReturns[i] = simulatedReturn;
        }
        
        // 计算标准差
        double mean = std::accumulate(simulatedReturns.begin(), simulatedReturns.end(), 0.0) / numSimulations;
        
        double variance = 0.0;
        for (double ret : simulatedReturns) {
            variance += (ret - mean) * (ret - mean);
        }
        variance /= numSimulations;
        
        return std::sqrt(variance);
    }
    
    // 计算风险价值(Value at Risk)
    double calculateVaR(double confidenceLevel, int numSimulations, double volatility) {
        std::mt19937_64 rng(std::random_device{}());
        std::normal_distribution<double> normalDist(0.0, 1.0);
        
        double currentValue = calculatePortfolioValue();
        std::vector<double> simulatedLosses(numSimulations);
        
        for (int i = 0; i < numSimulations; ++i) {
            double simulatedValue = 0.0;
            
            for (const auto& position : positions) {
                auto it = currentPrices.find(position.symbol);
                if (it != currentPrices.end()) {
                    double currentPrice = it->second;
                    double z = normalDist(rng);
                    double simulatedPrice = currentPrice * (1.0 + volatility * z);
                    simulatedValue += position.quantity * simulatedPrice;
                }
            }
            
            simulatedLosses[i] = currentValue - simulatedValue;
        }
        
        // 按损失排序
        std::sort(simulatedLosses.begin(), simulatedLosses.end());
        
        // 计算指定置信度的VaR
        int index = static_cast<int>(numSimulations * confidenceLevel);
        return simulatedLosses[index];
    }
};

// 金融系统示例
void financial_system_examples() {
    // 订单簿示例
    OrderBook book("AAPL");
    
    // 添加一些订单
    uint64_t timestamp = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::system_clock::now().time_since_epoch()
    ).count();
    
    // 买单
    book.addOrder({1, "AAPL", OrderSide::BUY, FixedPoint(150.50), 100, timestamp, "trader1"});
    book.addOrder({2, "AAPL", OrderSide::BUY, FixedPoint(151.00), 50, timestamp, "trader2"});
    
    // 卖单
    book.addOrder({3, "AAPL", OrderSide::SELL, FixedPoint(152.00), 75, timestamp, "trader3"});
    book.addOrder({4, "AAPL", OrderSide::SELL, FixedPoint(151.00), 60, timestamp, "trader4"});
    
    // 查看最优价格
    auto [bestBid, bestAsk] = book.getBestPrices();
    std::cout << "Best bid: " << bestBid.toString() << ", Best ask: " << bestAsk.toString() << std::endl;
    
    // 期权定价示例
    OptionPricer pricer;
    
    double spot = 100.0;
    double strike = 100.0;
    double volatility = 0.2;
    double riskFreeRate = 0.05;
    double timeToMaturity = 1.0;
    int numSimulations = 100000;
    
    double callPrice = pricer.priceEuropeanCall(
        spot, strike, volatility, riskFreeRate, timeToMaturity, numSimulations
    );
    
    double putPrice = pricer.priceEuropeanPut(
        spot, strike, volatility, riskFreeRate, timeToMaturity, numSimulations
    );
    
    std::cout << "European Call Option Price: " << callPrice << std::endl;
    std::cout << "European Put Option Price: " << putPrice << std::endl;
    
    // 投资组合分析示例
    PortfolioAnalyzer portfolio;
    
    portfolio.addPosition("AAPL", 100, 150.0);
    portfolio.addPosition("GOOGL", 50, 2500.0);
    portfolio.addPosition("MSFT", 200, 210.0);
    
    // 更新当前价格
    portfolio.updatePrice("AAPL", 155.0);
    portfolio.updatePrice("GOOGL", 2550.0);
    portfolio.updatePrice("MSFT", 215.0);
    
    double portfolioValue = portfolio.calculatePortfolioValue();
    double portfolioReturn = portfolio.calculatePortfolioReturn();
    
    std::cout << "Portfolio Value: $" << portfolioValue << std::endl;
    std::cout << "Portfolio Return: " << portfolioReturn << "%" << std::endl;
    
    // 风险分析
    double portfolioRisk = portfolio.calculatePortfolioRisk(10000, 0.02);
    double var95 = portfolio.calculateVaR(0.95, 10000, 0.02);
    
    std::cout << "Portfolio Risk (Volatility): " << portfolioRisk * 100 << "%" << std::endl;
    std::cout << "Value at Risk (95% confidence): $" << var95 << std::endl;
}
```

## 13. C++系统级编程

### 13.1 与操作系统交互

#### 系统接口封装

- **文件系统操作**：路径管理、文件读写
- **进程管理**：创建、终止、通信
- **系统信息**：环境变量、主机名、系统配置
- **跨平台抽象**：统一API封装不同平台

```cpp
// 操作系统交互示例
# include <iostream>
# include <string>
# include <vector>
# include <cstdlib>
# include <filesystem>
# include <fstream>
# include <mutex>
# include <thread>

# ifdef _WIN32
# include <windows.h>
# else
# include <unistd.h>
# include <sys/types.h>
# include <sys/wait.h>
# endif

// 跨平台系统交互类
class SystemInteraction {
public:
    // 获取环境变量
    static std::string getEnvironmentVariable(const std::string& name) {
        const char* value = std::getenv(name.c_str());
        return value ? value : "";
    }
    
    // 设置环境变量
    static bool setEnvironmentVariable(const std::string& name, const std::string& value) {
    #ifdef _WIN32
        return _putenv_s(name.c_str(), value.c_str()) == 0;
    #else
        return setenv(name.c_str(), value.c_str(), 1) == 0;
    #endif
    }
    
    // 获取当前工作目录
    static std::string getCurrentDirectory() {
        return std::filesystem::current_path().string();
    }
    
    // 改变当前工作目录
    static bool changeDirectory(const std::string& path) {
        try {
            std::filesystem::current_path(path);
            return true;
        } catch (const std::filesystem::filesystem_error&) {
            return false;
        }
    }
    
    // 获取主机名
    static std::string getHostName() {
        char hostname[256];
    #ifdef _WIN32
        DWORD size = sizeof(hostname);
        if (GetComputerNameA(hostname, &size)) {
            return hostname;
        }
    #else
        if (gethostname(hostname, sizeof(hostname)) == 0) {
            return hostname;
        }
    #endif
        return "unknown";
    }
    
    // 执行系统命令
    static int executeCommand(const std::string& command) {
        return std::system(command.c_str());
    }
    
    // 获取当前进程ID
    static int getProcessId() {
    #ifdef _WIN32
        return static_cast<int>(GetCurrentProcessId());
    #else
        return static_cast<int>(getpid());
    #endif
    }
    
    // 睡眠（毫秒）
    static void sleep(unsigned int milliseconds) {
    #ifdef _WIN32
        Sleep(milliseconds);
    #else
        usleep(milliseconds * 1000);
    #endif
    }
};

// 文件系统封装类
class FileSystem {
public:
    // 检查文件是否存在
    static bool fileExists(const std::string& path) {
        return std::filesystem::exists(path);
    }
    
    // 创建目录
    static bool createDirectory(const std::string& path) {
        try {
            return std::filesystem::create_directories(path);
        } catch (const std::filesystem::filesystem_error&) {
            return false;
        }
    }
    
    // 删除文件
    static bool removeFile(const std::string& path) {
        try {
            return std::filesystem::remove(path);
        } catch (const std::filesystem::filesystem_error&) {
            return false;
        }
    }
    
    // 获取文件大小
    static std::uintmax_t getFileSize(const std::string& path) {
        try {
            return std::filesystem::file_size(path);
        } catch (const std::filesystem::filesystem_error&) {
            return 0;
        }
    }
    
    // 列出目录内容
    static std::vector<std::string> listDirectory(const std::string& path) {
        std::vector<std::string> entries;
        
        try {
            for (const auto& entry : std::filesystem::directory_iterator(path)) {
                entries.push_back(entry.path().filename().string());
            }
        } catch (const std::filesystem::filesystem_error&) {
            // 处理错误
        }
        
        return entries;
    }
    
    // 复制文件
    static bool copyFile(const std::string& source, const std::string& destination) {
        try {
            std::filesystem::copy_file(
                source, destination, 
                std::filesystem::copy_options::overwrite_existing
            );
            return true;
        } catch (const std::filesystem::filesystem_error&) {
            return false;
        }
    }
    
    // 移动文件
    static bool moveFile(const std::string& source, const std::string& destination) {
        try {
            std::filesystem::rename(source, destination);
            return true;
        } catch (const std::filesystem::filesystem_error&) {
            return false;
        }
    }
};

// 进程管理类
class ProcessManager {
public:
    // 创建新进程（基本实现）
    static int createProcess(const

```cpp
    // 创建新进程（基本实现）
    static int createProcess(const std::string& command) {
    #ifdef _WIN32
        STARTUPINFO si;
        PROCESS_INFORMATION pi;
        
        ZeroMemory(&si, sizeof(si));
        si.cb = sizeof(si);
        ZeroMemory(&pi, sizeof(pi));
        
        // 创建进程
        if (!CreateProcess(
                nullptr,               // 应用程序名称
                const_cast<char*>(command.c_str()), // 命令行
                nullptr,               // 进程安全属性
                nullptr,               // 线程安全属性
                FALSE,                 // 不继承句柄
                0,                     // 创建标志
                nullptr,               // 环境块
                nullptr,               // 当前目录
                &si,                   // 启动信息
                &pi                    // 进程信息
            )) {
            return -1;
        }
        
        // 等待进程结束
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // 获取退出码
        DWORD exitCode;
        GetExitCodeProcess(pi.hProcess, &exitCode);
        
        // 关闭句柄
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        
        return static_cast<int>(exitCode);
    #else
        pid_t pid = fork();
        
        if (pid < 0) {
            // 创建进程失败
            return -1;
        } else if (pid == 0) {
            // 子进程
            execl("/bin/sh", "sh", "-c", command.c_str(), nullptr);
            exit(1); // 如果execl失败
        } else {
            // 父进程
            int status;
            waitpid(pid, &status, 0);
            
            if (WIFEXITED(status)) {
                return WEXITSTATUS(status);
            }
            
            return -1;
        }
    #endif
    }
    
    // 检查进程是否运行
    static bool isProcessRunning(int pid) {
    #ifdef _WIN32
        HANDLE process = OpenProcess(PROCESS_QUERY_INFORMATION, FALSE, pid);
        if (!process) {
            return false;
        }
        
        DWORD exitCode;
        bool isRunning = (GetExitCodeProcess(process, &exitCode) && exitCode == STILL_ACTIVE);
        CloseHandle(process);
        return isRunning;
    #else
        return kill(pid, 0) == 0;
    #endif
    }
    
    // 终止进程
    static bool terminateProcess(int pid) {
    #ifdef _WIN32
        HANDLE process = OpenProcess(PROCESS_TERMINATE, FALSE, pid);
        if (!process) {
            return false;
        }
        
        bool result = TerminateProcess(process, 1) != 0;
        CloseHandle(process);
        return result;
    #else
        return kill(pid, SIGTERM) == 0;
    #endif
    }
};

// 系统交互示例
void system_interaction_examples() {
    // 环境变量
    std::cout << "PATH: " << SystemInteraction::getEnvironmentVariable("PATH") << std::endl;
    
    SystemInteraction::setEnvironmentVariable("MY_VARIABLE", "test_value");
    std::cout << "MY_VARIABLE: " << SystemInteraction::getEnvironmentVariable("MY_VARIABLE") << std::endl;
    
    // 工作目录
    std::cout << "Current directory: " << SystemInteraction::getCurrentDirectory() << std::endl;
    
    // 主机名
    std::cout << "Hostname: " << SystemInteraction::getHostName() << std::endl;
    
    // 进程ID
    std::cout << "Process ID: " << SystemInteraction::getProcessId() << std::endl;
    
    // 文件系统操作
    std::string testDir = "test_dir";
    std::string testFile = testDir + "/test.txt";
    
    // 创建目录
    if (FileSystem::createDirectory(testDir)) {
        std::cout << "Created directory: " << testDir << std::endl;
        
        // 创建文件
        {
            std::ofstream file(testFile);
            file << "Hello, world!" << std::endl;
        }
        
        // 检查文件
        if (FileSystem::fileExists(testFile)) {
            std::cout << "File exists: " << testFile << std::endl;
            std::cout << "File size: " << FileSystem::getFileSize(testFile) << " bytes" << std::endl;
        }
        
        // 列出目录内容
        std::cout << "Directory contents:" << std::endl;
        for (const auto& entry : FileSystem::listDirectory(testDir)) {
            std::cout << "  " << entry << std::endl;
        }
        
        // 删除文件
        if (FileSystem::removeFile(testFile)) {
            std::cout << "Removed file: " << testFile << std::endl;
        }
    }
    
    // 执行命令
    std::cout << "Executing command: date" << std::endl;
    int exitCode = SystemInteraction::executeCommand("date");
    std::cout << "Exit code: " << exitCode << std::endl;
    
    // 进程操作
    std::cout << "Creating process..." << std::endl;
# ifdef _WIN32
    int cmdPid = ProcessManager::createProcess("ping -n 3 127.0.0.1");
# else
    int cmdPid = ProcessManager::createProcess("ping -c 3 127.0.0.1");
# endif
    std::cout << "Process completed with exit code: " << cmdPid << std::endl;
}
```

### 13.2 内存映射

#### 内存映射文件

- **定义**：将文件内容映射到进程的地址空间
- **优势**：提高I/O性能、简化大文件处理
- **共享内存**：进程间通信的高效方式
- **持久化**：将内存内容直接保存到磁盘

```cpp
// 内存映射示例
# include <iostream>
# include <fstream>
# include <string>
# include <system_error>
# include <cstring>
# include <fcntl.h>

# ifdef _WIN32
# include <windows.h>
# else
# include <sys/mman.h>
# include <sys/stat.h>
# include <unistd.h>
# endif

// 跨平台内存映射类
class MemoryMappedFile {
private:
# ifdef _WIN32
    HANDLE fileHandle = INVALID_HANDLE_VALUE;
    HANDLE mappingHandle = nullptr;
# else
    int fileDescriptor = -1;
# endif
    void* mappedData = nullptr;
    size_t mappedSize = 0;
    bool readOnly = true;
    
public:
    MemoryMappedFile() = default;
    ~MemoryMappedFile() {
        close();
    }
    
    // 打开并映射文件
    bool open(const std::string& filename, bool readOnly = true, size_t size = 0) {
        this->readOnly = readOnly;
        
# ifdef _WIN32
        // 打开文件
        fileHandle = CreateFile(
            filename.c_str(),
            readOnly ? GENERIC_READ : (GENERIC_READ | GENERIC_WRITE),
            FILE_SHARE_READ,
            nullptr,
            readOnly ? OPEN_EXISTING : OPEN_ALWAYS,
            FILE_ATTRIBUTE_NORMAL,
            nullptr
        );
        
        if (fileHandle == INVALID_HANDLE_VALUE) {
            return false;
        }
        
        // 获取文件大小
        LARGE_INTEGER fileSize;
        if (!GetFileSizeEx(fileHandle, &fileSize)) {
            CloseHandle(fileHandle);
            fileHandle = INVALID_HANDLE_VALUE;
            return false;
        }
        
        // 如果是只读，使用文件的实际大小
        if (readOnly) {
            mappedSize = static_cast<size_t>(fileSize.QuadPart);
        } else {
            // 如果是写入模式且指定了大小，使用指定大小
            mappedSize = size > 0 ? size : static_cast<size_t>(fileSize.QuadPart);
            
            // 设置文件大小
            if (mappedSize > static_cast<size_t>(fileSize.QuadPart)) {
                LARGE_INTEGER newSize;
                newSize.QuadPart = mappedSize;
                if (!SetFilePointerEx(fileHandle, newSize, nullptr, FILE_BEGIN) ||
                    !SetEndOfFile(fileHandle)) {
                    CloseHandle(fileHandle);
                    fileHandle = INVALID_HANDLE_VALUE;
                    return false;
                }
            }
        }
        
        // 创建文件映射
        mappingHandle = CreateFileMapping(
            fileHandle,
            nullptr,
            readOnly ? PAGE_READONLY : PAGE_READWRITE,
            0, 0,
            nullptr
        );
        
        if (!mappingHandle) {
            CloseHandle(fileHandle);
            fileHandle = INVALID_HANDLE_VALUE;
            return false;
        }
        
        // 映射视图
        mappedData = MapViewOfFile(
            mappingHandle,
            readOnly ? FILE_MAP_READ : FILE_MAP_ALL_ACCESS,
            0, 0,
            mappedSize
        );
        
        if (!mappedData) {
            CloseHandle(mappingHandle);
            CloseHandle(fileHandle);
            mappingHandle = nullptr;
            fileHandle = INVALID_HANDLE_VALUE;
            return false;
        }
# else
        // 打开文件
        fileDescriptor = ::open(
            filename.c_str(),
            readOnly ? O_RDONLY : (O_RDWR | O_CREAT),
            S_IRUSR | S_IWUSR
        );
        
        if (fileDescriptor == -1) {
            return false;
        }
        
        // 获取文件大小
        struct stat fileStat;
        if (fstat(fileDescriptor, &fileStat) == -1) {
            ::close(fileDescriptor);
            fileDescriptor = -1;
            return false;
        }
        
        // 如果是只读，使用文件的实际大小
        if (readOnly) {
            mappedSize = static_cast<size_t>(fileStat.st_size);
        } else {
            // 如果是写入模式且指定了大小，使用指定大小
            mappedSize = size > 0 ? size : static_cast<size_t>(fileStat.st_size);
            
            // 设置文件大小
            if (mappedSize > static_cast<size_t>(fileStat.st_size)) {
                if (ftruncate(fileDescriptor, mappedSize) == -1) {
                    ::close(fileDescriptor);
                    fileDescriptor = -1;
                    return false;
                }
            }
        }
        
        // 映射文件
        int protection = readOnly ? PROT_READ : (PROT_READ | PROT_WRITE);
        mappedData = mmap(
            nullptr,
            mappedSize,
            protection,
            MAP_SHARED,
            fileDescriptor,
            0
        );
        
        if (mappedData == MAP_FAILED) {
            ::close(fileDescriptor);
            fileDescriptor = -1;
            mappedData = nullptr;
            return false;
        }
# endif
        
        return true;
    }
    
    // 关闭映射
    void close() {
# ifdef _WIN32
        if (mappedData) {
            UnmapViewOfFile(mappedData);
            mappedData = nullptr;
        }
        
        if (mappingHandle) {
            CloseHandle(mappingHandle);
            mappingHandle = nullptr;
        }
        
        if (fileHandle != INVALID_HANDLE_VALUE) {
            CloseHandle(fileHandle);
            fileHandle = INVALID_HANDLE_VALUE;
        }
# else
        if (mappedData) {
            munmap(mappedData, mappedSize);
            mappedData = nullptr;
        }
        
        if (fileDescriptor != -1) {
            ::close(fileDescriptor);
            fileDescriptor = -1;
        }
# endif
        mappedSize = 0;
    }
    
    // 刷新映射到磁盘
    bool flush() {
        if (!mappedData) {
            return false;
        }
        
# ifdef _WIN32
        return FlushViewOfFile(mappedData, mappedSize) != 0;
# else
        return msync(mappedData, mappedSize, MS_SYNC) == 0;
# endif
    }
    
    // 获取映射数据指针
    void* data() const {
        return mappedData;
    }
    
    // 获取映射大小
    size_t size() const {
        return mappedSize;
    }
    
    // 是否有效
    bool isValid() const {
        return mappedData != nullptr;
    }
    
    // 禁止拷贝
    MemoryMappedFile(const MemoryMappedFile&) = delete;
    MemoryMappedFile& operator=(const MemoryMappedFile&) = delete;
    
    // 允许移动
    MemoryMappedFile(MemoryMappedFile&& other) noexcept
        : mappedData(other.mappedData), mappedSize(other.mappedSize), readOnly(other.readOnly) {
# ifdef _WIN32
        fileHandle = other.fileHandle;
        mappingHandle = other.mappingHandle;
        other.fileHandle = INVALID_HANDLE_VALUE;
        other.mappingHandle = nullptr;
# else
        fileDescriptor = other.fileDescriptor;
        other.fileDescriptor = -1;
# endif
        other.mappedData = nullptr;
        other.mappedSize = 0;
    }
    
    MemoryMappedFile& operator=(MemoryMappedFile&& other) noexcept {
        if (this != &other) {
            close();
            
            mappedData = other.mappedData;
            mappedSize = other.mappedSize;
            readOnly = other.readOnly;
            
# ifdef _WIN32
            fileHandle = other.fileHandle;
            mappingHandle = other.mappingHandle;
            other.fileHandle = INVALID_HANDLE_VALUE;
            other.mappingHandle = nullptr;
# else
            fileDescriptor = other.fileDescriptor;
            other.fileDescriptor = -1;
# endif
            other.mappedData = nullptr;
            other.mappedSize = 0;
        }
        return *this;
    }
};

// 使用内存映射文件的示例
void memory_mapped_file_example() {
    // 创建测试文件
    {
        std::ofstream testFile("test_mmap.dat", std::ios::binary);
        const char* testData = "Hello, Memory Mapped World!";
        testFile.write(testData, strlen(testData));
    }
    
    // 读取模式
    {
        MemoryMappedFile mmapFile;
        
        if (mmapFile.open("test_mmap.dat", true)) {
            const char* data = static_cast<const char*>(mmapFile.data());
            size_t size = mmapFile.size();
            
            std::cout << "Memory mapped file size: " << size << " bytes" << std::endl;
            std::cout << "Content: " << std::string(data, size) << std::endl;
        } else {
            std::cerr << "Failed to open memory mapped file in read mode" << std::endl;
        }
    }
    
    // 写入模式
    {
        MemoryMappedFile mmapFile;
        
        if (mmapFile.open("test_mmap.dat", false, 100)) {
            char* data = static_cast<char*>(mmapFile.data());
            
            // 修改内容
            strcpy(data + 7, "Modified");
            
            // 刷新到磁盘
            mmapFile.flush();
            
            std::cout << "File content modified using memory mapping" << std::endl;
        } else {
            std::cerr << "Failed to open memory mapped file in write mode" << std::endl;
        }
    }
    
    // 再次读取验证修改
    {
        MemoryMappedFile mmapFile;
        
        if (mmapFile.open("test_mmap.dat", true)) {
            const char* data = static_cast<const char*>(mmapFile.data());
            size_t size = mmapFile.size();
            
            std::cout << "Updated content: " << std::string(data, size) << std::endl;
        }
    }
    
    // 大文件示例
    {
        constexpr size_t largeFileSize = 100 * 1024 * 1024; // 100 MB
        
        std::cout << "Creating large file... ";
        
        MemoryMappedFile mmapFile;
        
        if (mmapFile.open("large_file.dat", false, largeFileSize)) {
            char* data = static_cast<char*>(mmapFile.data());
            
            // 在文件的开始、中间和结尾写入标记
            strcpy(data, "START");
            strcpy(data + largeFileSize / 2, "MIDDLE");
            strcpy(data + largeFileSize - 6, "END");
            
            mmapFile.flush();
            mmapFile.close();
            
            std::cout << "Done" << std::endl;
            
            // 验证内容
            mmapFile.open("large_file.dat", true);
            
            const char* readData = static_cast<const char*>(mmapFile.data());
            
            std::cout << "Verifying large file:" << std::endl;
            std::cout << "Start: " << std::string(readData, 5) << std::endl;
            std::cout << "Middle: " << std::string(readData + largeFileSize / 2, 6) << std::endl;
            std::cout << "End: " << std::string(readData + largeFileSize - 3, 3) << std::endl;
        } else {
            std::cerr << "Failed to create large file" << std::endl;
        }
    }
    
    // 清理文件
    remove("test_mmap.dat");
    remove("large_file.dat");
}
```

### 13.3 系统调用封装

#### 系统调用接口

- **文件描述符**：低级I/O操作
- **套接字API**：网络通信
- **信号处理**：捕获和响应系统信号
- **IPC机制**：进程间通信

```cpp
// 系统调用封装示例
# include <iostream>
# include <string>
# include <vector>
# include <stdexcept>
# include <system_error>
# include <functional>

# ifdef _WIN32
# include <winsock2.h>
# include <ws2tcpip.h>
# pragma comment(lib, "ws2_32.lib")
# else
# include <sys/socket.h>
# include <netinet/in.h>
# include <arpa/inet.h>
# include <unistd.h>
# include <signal.h>
# include <fcntl.h>
# endif

// 跨平台初始化
class SystemCallInitializer {
private:
    static bool initialized;
    
public:
    static bool initialize() {
        if (initialized) return true;
        
# ifdef _WIN32
        WSADATA wsaData;
        int result = WSAStartup(MAKEWORD(2, 2), &wsaData);
        if (result != 0) {
            std::cerr << "WSAStartup failed: " << result << std::endl;
            return false;
        }
# endif
        
        initialized = true;
        return true;
    }
    
    static void cleanup() {
        if (!initialized) return;
        
# ifdef _WIN32
        WSACleanup();
# endif
        
        initialized = false;
    }
    
    // 确保初始化只运行一次的单例模式
    static SystemCallInitializer& instance() {
        static SystemCallInitializer instance;
        return instance;
    }
    
    SystemCallInitializer() {
        initialize();
    }
    
    ~SystemCallInitializer() {
        cleanup();
    }
};

bool SystemCallInitializer::initialized = false;

// 低级套接字封装
class Socket {
private:
# ifdef _WIN32
    SOCKET handle = INVALID_SOCKET;
# else
    int handle = -1;
# endif
    bool blocking = true;
    
public:
    Socket() {
        SystemCallInitializer::initialize();
    }
    
    explicit Socket(int type, int protocol = 0) {
        SystemCallInitializer::initialize();
        
        handle = socket(AF_INET, type, protocol);
        
# ifdef _WIN32
        if (handle == INVALID_SOCKET) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to create socket");
        }
# else
        if (handle == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to create socket");
        }
# endif
    }
    
    ~Socket() {
        close();
    }
    
    // 关闭套接字
    void close() {
# ifdef _WIN32
        if (handle != INVALID_SOCKET) {
            closesocket(handle);
            handle = INVALID_SOCKET;
        }
# else
        if (handle != -1) {
            ::close(handle);
            handle = -1;
        }
# endif
    }
    
    // 绑定到地址
    void bind(const std::string& ip, uint16_t port) {
        sockaddr_in addr{};
        addr.sin_family = AF_INET;
        addr.sin_port = htons(port);
        
# ifdef _WIN32
        inet_pton(AF_INET, ip.c_str(), &addr.sin_addr);
# else
        addr.sin_addr.s_addr = inet_addr(ip.c_str());
# endif
        
        int result = ::bind(handle, reinterpret_cast<sockaddr*>(&addr), sizeof(addr));
        
# ifdef _WIN32
        if (result == SOCKET_ERROR) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to bind socket");
        }
# else
        if (result == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to bind socket");
        }
# endif
    }
    
    // 监听连接
    void listen(int backlog = 5) {
        int result = ::listen(handle, backlog);
        
# ifdef _WIN32
        if (result == SOCKET_ERROR) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to listen on socket");
        }
# else
        if (result == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to listen on socket");
        }
# endif
    }
    
    // 接受连接
    Socket accept() {
        Socket clientSocket;
        sockaddr_in clientAddr{};
        socklen_t addrLen = sizeof(clientAddr);
        
# ifdef _WIN32
        clientSocket.handle = ::accept(handle, reinterpret_cast<sockaddr*>(&clientAddr), &addrLen);
        
        if (clientSocket.handle == INVALID_SOCKET) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to accept connection");
        }
# else
        clientSocket.handle = ::accept(handle, reinterpret_cast<sockaddr*>(&clientAddr), &addrLen);
        
        if (clientSocket.handle == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to accept connection");
        }
# endif
        
        return clientSocket;
    }
    
    // 连接到服务器
    void connect(const std::string& ip, uint16_t port) {
        sockaddr_in serverAddr{};
        serverAddr.sin_family = AF_INET;
        serverAddr.sin_port = htons(port);
        
# ifdef _WIN32
        inet_pton(AF_INET, ip.c_str(), &serverAddr.sin_addr);
# else
        serverAddr.sin_addr.s_addr = inet_addr(ip.c_str());
# endif
        
        int result = ::connect(handle, reinterpret_cast<sockaddr*>(&serverAddr), sizeof(serverAddr));
        
# ifdef _WIN32
        if (result == SOCKET_ERROR) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to connect to server");
        }
# else
        if (result == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to connect to server");
        }
# endif
    }
    
    // 发送数据
    int send(const void* data, size_t length, int flags = 0) {
# ifdef _WIN32
        int result = ::send(handle, static_cast<const char*>(data), static_cast<int>(length), flags);
        
        if (result == SOCKET_ERROR) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to send data");
        }
# else
        int result = ::send(handle, static_cast<const char*>(data), length, flags);
        
        if (result == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to send data");
        }
# endif
        
        return result;
    }
    
    // 接收数据
    int receive(void* buffer, size_t length, int flags = 0) {
# ifdef _WIN32
        int result = ::recv(handle, static_cast<char*>(buffer), static_cast<int>(length), flags);
        
        if (result == SOCKET_ERROR) {
            int error = WSAGetLastError();
            if (error == WSAEWOULDBLOCK) {
                return 0; // 非阻塞模式下无数据可读
            }
            throw std::system_error(error, std::system_category(),
                                   "Failed to receive data");
        }
# else
        int result = ::recv(handle, static_cast<char*>(buffer), length, flags);
        
        if (result == -1) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                return 0; // 非阻塞模式下无数据可读
            }
            throw std::system_error(errno, std::system_category(),
                                   "Failed to receive data");
        }
# endif
        
        return result;
    }
    
    // 设置为非阻塞模式
    void setBlocking(bool blocking) {
        this->blocking = blocking;
        
# ifdef _WIN32
        u_long mode = blocking ? 0 : 1;
        if (ioctlsocket(handle, FIONBIO, &mode) == SOCKET_ERROR) {
            throw std::system_error(WSAGetLastError(), std::system_category(),
                                   "Failed to set socket blocking mode");
        }
# else
        int flags = fcntl(handle, F_GETFL, 0);
        if (flags == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to get socket flags");
        }
        
        if (blocking) {
            flags &= ~O_NONBLOCK;
        } else {
            flags |= O_NONBLOCK;
        }
        
        if (fcntl(handle, F_SETFL, flags) == -1) {
            throw std::system_error(errno, std::system_category(),
                                   "Failed to set socket flags");
        }
# endif
    }
    
    // 是否有效
    bool isValid() const {
# ifdef _WIN32
        return handle != INVALID_SOCKET;
# else
        return handle != -1;
# endif
    }
    
    // 获取原始句柄
# ifdef _WIN32
    SOCKET getHandle() const {
# else
    int getHandle() const {
# endif
        return handle;
    }
    
    // 禁止拷贝
    Socket(const Socket&) = delete;
    Socket& operator=(const Socket&) = delete;
    
    // 允许移动
    Socket(Socket&& other) noexcept : handle(other.handle), blocking(other.blocking) {
# ifdef _WIN32
        other.handle = INVALID_SOCKET;
# else
        other.handle = -1;
# endif
    }
    
    Socket& operator=(Socket&& other) noexcept {
        if (this != &other) {
            close();
            handle = other.handle;
            blocking = other.blocking;
# ifdef _WIN32
            other.handle = INVALID_SOCKET;
# else
            other.handle = -1;
# endif
        }
        return *this;
    }
};

// 信号处理封装
# ifndef _WIN32
class SignalHandler {
private:
    static std::unordered_map<int, std::function<void(int)>> handlers;
    
    static void signalHandler(int signal) {
        auto it = handlers.find(signal);
        if (it != handlers.end()) {
            it->second(signal);
        }
    }
    
public:
    // 注册信号处理函数
    static void registerHandler(int signal, const std::function<void(int)>& handler) {
        handlers[signal] = handler;
        struct sigaction sa;
        sa.sa_handler = signalHandler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sigaction(signal, &sa, nullptr);
    }
    
    // 忽略信号
    static void ignoreSignal(int signal) {
        struct sigaction sa;
        sa.sa_handler = SIG_IGN;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sigaction(signal, &sa, nullptr);
    }
    
    // 恢复默认处理
    static void resetToDefault(int signal) {
        handlers.erase(signal);
        struct sigaction sa;
        sa.sa_handler = SIG_DFL;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sigaction(signal, &sa, nullptr);
    }
};

std::unordered_map<int, std::function<void(int)>> SignalHandler::handlers;
# endif

// 系统调用示例
void system_call_examples() {
    // 确保系统初始化
    SystemCallInitializer::initialize();
    
    // TCP Echo Server示例
    try {
        // 创建TCP套接字
        Socket serverSocket(SOCK_STREAM);
        
        std::cout << "Created TCP socket" << std::endl;
        
        // 绑定到本地地址
        serverSocket.bind("127.0.0.1", 8080);
        std::cout << "Bound to 127.0.0.1:8080" << std::endl;
        
        // 监听连接
        serverSocket.listen(5);
        std::cout << "Listening for connections..." << std::endl;
        
        // 非阻塞模式
        serverSocket.setBlocking(false);
        
        // 简单的服务器循环
        int iterationsLeft = 100; // 限制循环次数，避免无限循环
        while (iterationsLeft-- > 0) {
            try {
                // 尝试接受连接
                Socket clientSocket = serverSocket.accept();
                
                std::cout << "Accepted client connection" << std::endl;
                
                // 接收数据
                char buffer[1024] = {0};
                int bytesRead = clientSocket.receive(buffer, sizeof(buffer));
                
                if (bytesRead > 0) {
                    std::cout << "Received: " << buffer << std::endl;
                    
                    // 回显数据
                    clientSocket.send(buffer, bytesRead);
                    std::cout << "Echoed data back to client" << std::endl;
                }
                
                // 关闭客户端连接
                clientSocket.close();
                
                // 收到连接就退出示例循环
                break;
            } catch (const std::system_error& e) {
# ifdef _WIN32
                if (e.code().value() == WSAEWOULDBLOCK) {
# else
                if (e.code().value() == EAGAIN || e.code().value() == EWOULDBLOCK) {
# endif
                    // 非阻塞模式下暂无连接，继续循环
                    std::this_thread::sleep_for(std::chrono::milliseconds(100));
                    continue;
                } else {
                    // 其他错误
                    std::cerr << "Socket error: " << e.what() << std::endl;
                    break;
                }
            }
        }
    } catch (const std::exception& e) {
        std::cerr << "Exception: " << e.what() << std::endl;
    }
    
    // 信号处理示例
# ifndef _WIN32
    std::cout << "\nSignal handling example (UNIX only)" << std::endl;
    
    // 注册SIGINT处理程序
    SignalHandler::registerHandler(SIGINT, [](int signal) {
        std::cout << "Received SIGINT signal (" << signal << ")" << std::endl;
    });
    
    std::cout << "Registered SIGINT handler. Try pressing Ctrl+C..." << std::endl;
    std::this_thread::sleep_for(std::chrono::seconds(3));
    
    // 恢复默认处理
    SignalHandler::resetToDefault(SIGINT);
    std::cout << "Reset SIGINT to default handler" << std::endl;
# endif
    
    // 清理
    SystemCallInitializer::cleanup();
}
```

### 13.4 进程与线程管理

#### 进程管理

- **创建与终止**：启动新进程、获取退出状态
- **进程通信**：管道、共享内存、消息队列
- **进程同步**：信号量、互斥量

#### 线程管理

- **线程创建**：创建新线程、设置属性
- **线程同步**：互斥锁、条件变量、原子操作
- **线程池**：管理工作线程集合

```cpp
// 进程与线程管理示例
# include <iostream>
# include <string>
# include <vector>
# include <thread>
# include <mutex>
# include <condition_variable>
# include <queue>
# include <functional>
# include <future>
# include <chrono>

# ifdef _WIN32
# include <windows.h>
# include <process.h>
# else
# include <unistd.h>
# include <sys/types.h>
# include <sys/wait.h>
# endif

// 进程管理类
class ProcessManager {
public:
    // 创建进程并等待完成
    static int executeProcess(const std::string& command) {
# ifdef _WIN32
        STARTUPINFO si;
        PROCESS_INFORMATION pi;
        
        ZeroMemory(&si, sizeof(si));
        si.cb = sizeof(si);
        ZeroMemory(&pi, sizeof(pi));
        
        // 创建进程
        if (!CreateProcess(
                nullptr,               // 应用程序名称
                const_cast<char*>(command.c_str()), // 命令行
                nullptr,               // 进程安全属性
                nullptr,               // 线程安全属性
                FALSE,                 // 不继承句柄
                0,                     // 创建标志
                nullptr,               // 环境块
                nullptr,               // 当前目录
                &si,                   // 启动信息
                &pi                    // 进程信息
            )) {
            return -1;
        }
        
        // 等待进程结束
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // 获取退出码
        DWORD exitCode;
        GetExitCodeProcess(pi.hProcess, &exitCode);
        
        // 关闭句柄
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        
        return static_cast<int>(exitCode);
# else
        int status;
        pid_t pid = fork();
        
        if (pid < 0) {
            // 创建进程失败
            return -1;
        } else if (pid == 0) {
            // 子进程
            execl("/bin/sh", "sh", "-c", command.c_str(), nullptr);
            exit(1); // 如果execl失败
        } else {
            // 父进程
            waitpid(pid, &status, 0);
            
            if (WIFEXITED(status)) {
                return WEXITSTATUS(status);
            }
            
            return

```cpp
            return -1;
        }
# endif
    }
    
    // 创建进程不等待完成
    static bool startProcess(const std::string& command) {
# ifdef _WIN32
        STARTUPINFO si;
        PROCESS_INFORMATION pi;
        
        ZeroMemory(&si, sizeof(si));
        si.cb = sizeof(si);
        ZeroMemory(&pi, sizeof(pi));
        
        // 创建进程
        if (!CreateProcess(
                nullptr,               // 应用程序名称
                const_cast<char*>(command.c_str()), // 命令行
                nullptr,               // 进程安全属性
                nullptr,               // 线程安全属性
                FALSE,                 // 不继承句柄
                0,                     // 创建标志
                nullptr,               // 环境块
                nullptr,               // 当前目录
                &si,                   // 启动信息
                &pi                    // 进程信息
            )) {
            return false;
        }
        
        // 关闭句柄，不等待进程
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        
        return true;
# else
        pid_t pid = fork();
        
        if (pid < 0) {
            // 创建进程失败
            return false;
        } else if (pid == 0) {
            // 子进程
            execl("/bin/sh", "sh", "-c", command.c_str(), nullptr);
            exit(1); // 如果execl失败
        }
        
        // 父进程继续，不等待子进程
        return true;
# endif
    }
    
    // 管道通信示例
    static std::string captureProcessOutput(const std::string& command) {
        std::string result;
        
# ifdef _WIN32
        // 创建管道
        HANDLE hReadPipe, hWritePipe;
        SECURITY_ATTRIBUTES saAttr;
        
        saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
        saAttr.bInheritHandle = TRUE;
        saAttr.lpSecurityDescriptor = nullptr;
        
        if (!CreatePipe(&hReadPipe, &hWritePipe, &saAttr, 0)) {
            return "";
        }
        
        // 设置子进程输出重定向
        STARTUPINFO si;
        PROCESS_INFORMATION pi;
        
        ZeroMemory(&si, sizeof(si));
        si.cb = sizeof(si);
        si.hStdOutput = hWritePipe;
        si.hStdError = hWritePipe;
        si.dwFlags |= STARTF_USESTDHANDLES;
        
        ZeroMemory(&pi, sizeof(pi));
        
        // 创建进程
        if (!CreateProcess(
                nullptr,                // 应用程序名称
                const_cast<char*>(command.c_str()), // 命令行
                nullptr,                // 进程安全属性
                nullptr,                // 线程安全属性
                TRUE,                   // 继承句柄
                0,                      // 创建标志
                nullptr,                // 环境块
                nullptr,                // 当前目录
                &si,                    // 启动信息
                &pi                     // 进程信息
            )) {
            CloseHandle(hReadPipe);
            CloseHandle(hWritePipe);
            return "";
        }
        
        // 关闭不需要的写入端
        CloseHandle(hWritePipe);
        
        // 读取输出
        char buffer[4096];
        DWORD bytesRead;
        
        while (ReadFile(hReadPipe, buffer, sizeof(buffer) - 1, &bytesRead, nullptr) && bytesRead != 0) {
            buffer[bytesRead] = '\0';
            result += buffer;
        }
        
        // 等待进程结束
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // 清理
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        CloseHandle(hReadPipe);
# else
        // 创建管道
        int pipefd[2];
        if (pipe(pipefd) == -1) {
            return "";
        }
        
        pid_t pid = fork();
        
        if (pid < 0) {
            // 创建进程失败
            close(pipefd[0]);
            close(pipefd[1]);
            return "";
        } else if (pid == 0) {
            // 子进程
            close(pipefd[0]); // 关闭读取端
            
            // 重定向标准输出到管道
            dup2(pipefd[1], STDOUT_FILENO);
            dup2(pipefd[1], STDERR_FILENO);
            close(pipefd[1]);
            
            execl("/bin/sh", "sh", "-c", command.c_str(), nullptr);
            exit(1); // 如果execl失败
        }
        
        // 父进程
        close(pipefd[1]); // 关闭写入端
        
        // 读取子进程输出
        char buffer[4096];
        ssize_t bytes_read;
        
        while ((bytes_read = read(pipefd[0], buffer, sizeof(buffer) - 1)) > 0) {
            buffer[bytes_read] = '\0';
            result += buffer;
        }
        
        // 关闭读取端
        close(pipefd[0]);
        
        // 等待子进程结束
        int status;
        waitpid(pid, &status, 0);
# endif
        
        return result;
    }
};

// 线程池类
class ThreadPool {
private:
    std::vector<std::thread> workers;
    std::queue<std::function<void()>> tasks;
    std::mutex queue_mutex;
    std::condition_variable condition;
    bool stop;
    
public:
    // 构造函数
    ThreadPool(size_t numThreads) : stop(false) {
        for (size_t i = 0; i < numThreads; ++i) {
            workers.emplace_back([this] {
                while (true) {
                    std::function<void()> task;
                    
                    {
                        std::unique_lock<std::mutex> lock(queue_mutex);
                        
                        // 等待直到有任务或需要停止
                        condition.wait(lock, [this] {
                            return stop || !tasks.empty();
                        });
                        
                        // 如果线程池停止且没有任务，退出线程
                        if (stop && tasks.empty()) {
                            return;
                        }
                        
                        // 获取任务
                        task = std::move(tasks.front());
                        tasks.pop();
                    }
                    
                    // 执行任务
                    task();
                }
            });
        }
    }
    
    // 提交任务到线程池
    template<class F, class... Args>
    auto enqueue(F&& f, Args&&... args) -> std::future<typename std::result_of<F(Args...)>::type> {
        using return_type = typename std::result_of<F(Args...)>::type;
        
        // 创建一个可共享的打包任务
        auto task = std::make_shared<std::packaged_task<return_type()>>(
            std::bind(std::forward<F>(f), std::forward<Args>(args)...)
        );
        
        // 获取任务的future
        std::future<return_type> result = task->get_future();
        
        {
            std::unique_lock<std::mutex> lock(queue_mutex);
            
            // 如果线程池已停止，不能添加任务
            if (stop) {
                throw std::runtime_error("Cannot enqueue on stopped ThreadPool");
            }
            
            // 添加任务到队列
            tasks.emplace([task]() { (*task)(); });
        }
        
        // 通知一个等待中的线程
        condition.notify_one();
        
        return result;
    }
    
    // 析构函数
    ~ThreadPool() {
        {
            std::unique_lock<std::mutex> lock(queue_mutex);
            stop = true;
        }
        
        // 通知所有线程
        condition.notify_all();
        
        // 等待所有线程完成
        for (std::thread& worker : workers) {
            if (worker.joinable()) {
                worker.join();
            }
        }
    }
};

// 线程安全队列
template<typename T>
class ThreadSafeQueue {
private:
    std::queue<T> queue;
    mutable std::mutex mutex;
    std::condition_variable cv;
    
public:
    // 添加元素
    void push(T value) {
        {
            std::lock_guard<std::mutex> lock(mutex);
            queue.push(std::move(value));
        }
        cv.notify_one();
    }
    
    // 获取元素（阻塞）
    T pop() {
        std::unique_lock<std::mutex> lock(mutex);
        cv.wait(lock, [this] { return !queue.empty(); });
        
        T value = std::move(queue.front());
        queue.pop();
        return value;
    }
    
    // 尝试获取元素（非阻塞）
    bool tryPop(T& value) {
        std::lock_guard<std::mutex> lock(mutex);
        if (queue.empty()) {
            return false;
        }
        
        value = std::move(queue.front());
        queue.pop();
        return true;
    }
    
    // 等待并获取元素（有超时）
    bool waitAndPop(T& value, const std::chrono::milliseconds& timeout) {
        std::unique_lock<std::mutex> lock(mutex);
        
        if (!cv.wait_for(lock, timeout, [this] { return !queue.empty(); })) {
            return false;
        }
        
        value = std::move(queue.front());
        queue.pop();
        return true;
    }
    
    // 判断是否为空
    bool empty() const {
        std::lock_guard<std::mutex> lock(mutex);
        return queue.empty();
    }
    
    // 获取大小
    size_t size() const {
        std::lock_guard<std::mutex> lock(mutex);
        return queue.size();
    }
};

// 进程与线程管理示例
void process_thread_management_examples() {
    // 进程执行示例
    std::cout << "=== Process Management ===" << std::endl;
    
# ifdef _WIN32
    std::string listCommand = "dir";
    std::string echoCommand = "echo Hello from subprocess";
# else
    std::string listCommand = "ls -la";
    std::string echoCommand = "echo Hello from subprocess";
# endif
    
    // 执行进程并等待
    std::cout << "Executing command: " << listCommand << std::endl;
    int exitCode = ProcessManager::executeProcess(listCommand);
    std::cout << "Process exit code: " << exitCode << std::endl;
    
    // 捕获进程输出
    std::cout << "\nCapturing process output:" << std::endl;
    std::string output = ProcessManager::captureProcessOutput(echoCommand);
    std::cout << "Output: " << output << std::endl;
    
    // 启动进程不等待
    std::cout << "\nStarting process without waiting..." << std::endl;
    bool success = ProcessManager::startProcess(echoCommand);
    std::cout << "Process started: " << (success ? "yes" : "no") << std::endl;
    
    // 线程池示例
    std::cout << "\n=== Thread Pool ===" << std::endl;
    
    {
        // 创建线程池
        ThreadPool pool(4);
        
        // 提交一些任务
        std::vector<std::future<int>> results;
        
        std::cout << "Submitting tasks to thread pool..." << std::endl;
        
        for (int i = 0; i < 8; ++i) {
            results.emplace_back(
                pool.enqueue([i] {
                    std::cout << "Task " << i << " running on thread " << std::this_thread::get_id() << std::endl;
                    std::this_thread::sleep_for(std::chrono::milliseconds(100 * i));
                    return i * i;
                })
            );
        }
        
        // 获取结果
        std::cout << "\nResults:" << std::endl;
        for (size_t i = 0; i < results.size(); ++i) {
            std::cout << "Task " << i << " result: " << results[i].get() << std::endl;
        }
    } // 线程池在这里析构，等待所有任务完成
    
    // 线程安全队列示例
    std::cout << "\n=== Thread Safe Queue ===" << std::endl;
    
    ThreadSafeQueue<std::string> messageQueue;
    
    // 生产者线程
    std::thread producer([&messageQueue] {
        for (int i = 0; i < 5; ++i) {
            std::string message = "Message " + std::to_string(i);
            std::cout << "Producer: Adding " << message << std::endl;
            messageQueue.push(message);
            std::this_thread::sleep_for(std::chrono::milliseconds(300));
        }
    });
    
    // 消费者线程
    std::thread consumer([&messageQueue] {
        for (int i = 0; i < 5; ++i) {
            std::string message;
            
            // 等待消息
            if (messageQueue.waitAndPop(message, std::chrono::milliseconds(1000))) {
                std::cout << "Consumer: Received " << message << std::endl;
            } else {
                std::cout << "Consumer: Timeout waiting for message" << std::endl;
            }
        }
    });
    
    // 等待线程完成
    producer.join();
    consumer.join();
}
```

## 14. 高级设计模式与实践

### 14.1 现代C++设计模式

#### 经典设计模式的C++实现

- **创建型模式**：工厂、单例、构建器、原型
- **结构型模式**：适配器、桥接、组合、装饰器
- **行为型模式**：命令、迭代器、观察者、策略

#### 现代C++特质优化

- **移动语义**：提高资源传递效率
- **智能指针**：安全管理对象生命周期
- **Lambda**：简化函数对象创建

```cpp
// 现代C++设计模式示例
# include <iostream>
# include <string>
# include <memory>
# include <vector>
# include <unordered_map>
# include <functional>
# include <algorithm>

// 工厂模式
class Product {
public:
    virtual ~Product() = default;
    virtual std::string operation() const = 0;
};

class ConcreteProductA : public Product {
public:
    std::string operation() const override {
        return "Result of ConcreteProductA";
    }
};

class ConcreteProductB : public Product {
public:
    std::string operation() const override {
        return "Result of ConcreteProductB";
    }
};

class Factory {
public:
    virtual ~Factory() = default;
    virtual std::unique_ptr<Product> createProduct() const = 0;
};

class ConcreteFactoryA : public Factory {
public:
    std::unique_ptr<Product> createProduct() const override {
        return std::make_unique<ConcreteProductA>();
    }
};

class ConcreteFactoryB : public Factory {
public:
    std::unique_ptr<Product> createProduct() const override {
        return std::make_unique<ConcreteProductB>();
    }
};

// 单例模式（线程安全，C++11）
class Singleton {
private:
    Singleton() = default;
    
public:
    // 禁止拷贝和移动
    Singleton(const Singleton&) = delete;
    Singleton& operator=(const Singleton&) = delete;
    Singleton(Singleton&&) = delete;
    Singleton& operator=(Singleton&&) = delete;
    
    // 获取实例
    static Singleton& getInstance() {
        static Singleton instance;
        return instance;
    }
    
    void someBusinessLogic() {
        // 单例的业务逻辑
        std::cout << "Singleton business logic called" << std::endl;
    }
};

// 观察者模式（使用std::function和智能指针）
class Subject;

class Observer {
public:
    virtual ~Observer() = default;
    virtual void update(Subject& subject) = 0;
};

class Subject {
private:
    std::vector<std::shared_ptr<Observer>> observers;
    int state = 0;
    
public:
    void attach(std::shared_ptr<Observer> observer) {
        observers.push_back(observer);
    }
    
    void detach(std::shared_ptr<Observer> observer) {
        observers.erase(
            std::remove_if(observers.begin(), observers.end(),
                [&observer](const std::shared_ptr<Observer>& o) {
                    return o == observer;
                }),
            observers.end()
        );
    }
    
    void setState(int state) {
        this->state = state;
        notify();
    }
    
    int getState() const {
        return state;
    }
    
    void notify() {
        for (const auto& observer : observers) {
            observer->update(*this);
        }
    }
};

class ConcreteObserverA : public Observer {
private:
    std::string name;
    
public:
    explicit ConcreteObserverA(std::string name) : name(std::move(name)) {}
    
    void update(Subject& subject) override {
        std::cout << name << " observed state change to " << subject.getState() << std::endl;
    }
};

// 命令模式（使用std::function）
class Command {
public:
    virtual ~Command() = default;
    virtual void execute() = 0;
};

class SimpleCommand : public Command {
private:
    std::function<void()> action;
    
public:
    explicit SimpleCommand(std::function<void()> action)
        : action(std::move(action)) {}
    
    void execute() override {
        action();
    }
};

class ComplexCommand : public Command {
private:
    std::function<void()> begin_action;
    std::function<void()> end_action;
    
public:
    ComplexCommand(std::function<void()> begin, std::function<void()> end)
        : begin_action(std::move(begin)), end_action(std::move(end)) {}
    
    void execute() override {
        begin_action();
        end_action();
    }
};

class Invoker {
private:
    Command* on_start = nullptr;
    Command* on_finish = nullptr;
    
public:
    void setOnStart(Command* command) {
        on_start = command;
    }
    
    void setOnFinish(Command* command) {
        on_finish = command;
    }
    
    void doSomething() {
        std::cout << "Invoker: Does anybody want something done before I begin?" << std::endl;
        if (on_start) {
            on_start->execute();
        }
        
        std::cout << "Invoker: ...doing something really important..." << std::endl;
        
        std::cout << "Invoker: Does anybody want something done after I finish?" << std::endl;
        if (on_finish) {
            on_finish->execute();
        }
    }
};

// 装饰器模式
class Component {
public:
    virtual ~Component() = default;
    virtual std::string operation() const = 0;
};

class ConcreteComponent : public Component {
public:
    std::string operation() const override {
        return "ConcreteComponent";
    }
};

class Decorator : public Component {
protected:
    std::unique_ptr<Component> component;
    
public:
    explicit Decorator(std::unique_ptr<Component> component)
        : component(std::move(component)) {}
    
    std::string operation() const override {
        return component->operation();
    }
};

class ConcreteDecoratorA : public Decorator {
public:
    explicit ConcreteDecoratorA(std::unique_ptr<Component> component)
        : Decorator(std::move(component)) {}
    
    std::string operation() const override {
        return "ConcreteDecoratorA(" + Decorator::operation() + ")";
    }
};

class ConcreteDecoratorB : public Decorator {
public:
    explicit ConcreteDecoratorB(std::unique_ptr<Component> component)
        : Decorator(std::move(component)) {}
    
    std::string operation() const override {
        return "ConcreteDecoratorB(" + Decorator::operation() + ")";
    }
};

// 设计模式示例
void design_patterns_examples() {
    // 工厂模式
    std::cout << "=== Factory Pattern ===" << std::endl;
    
    std::unique_ptr<Factory> factoryA = std::make_unique<ConcreteFactoryA>();
    std::unique_ptr<Product> productA = factoryA->createProduct();
    std::cout << productA->operation() << std::endl;
    
    std::unique_ptr<Factory> factoryB = std::make_unique<ConcreteFactoryB>();
    std::unique_ptr<Product> productB = factoryB->createProduct();
    std::cout << productB->operation() << std::endl;
    
    // 单例模式
    std::cout << "\n=== Singleton Pattern ===" << std::endl;
    
    Singleton& singleton = Singleton::getInstance();
    singleton.someBusinessLogic();
    
    // 观察者模式
    std::cout << "\n=== Observer Pattern ===" << std::endl;
    
    Subject subject;
    
    auto observerA = std::make_shared<ConcreteObserverA>("Observer A");
    auto observerB = std::make_shared<ConcreteObserverA>("Observer B");
    
    subject.attach(observerA);
    subject.attach(observerB);
    
    subject.setState(123);
    
    subject.detach(observerB);
    
    subject.setState(456);
    
    // 命令模式
    std::cout << "\n=== Command Pattern ===" << std::endl;
    
    SimpleCommand simpleCommand([]() {
        std::cout << "Simple command executed" << std::endl;
    });
    
    ComplexCommand complexCommand(
        []() { std::cout << "Complex command: begin action" << std::endl; },
        []() { std::cout << "Complex command: end action" << std::endl; }
    );
    
    Invoker invoker;
    invoker.setOnStart(&simpleCommand);
    invoker.setOnFinish(&complexCommand);
    
    invoker.doSomething();
    
    // 装饰器模式
    std::cout << "\n=== Decorator Pattern ===" << std::endl;
    
    std::unique_ptr<Component> simple = std::make_unique<ConcreteComponent>();
    std::cout << "Client: " << simple->operation() << std::endl;
    
    std::unique_ptr<Component> decorator1 = 
        std::make_unique<ConcreteDecoratorA>(std::move(simple));
    std::cout << "Client: " << decorator1->operation() << std::endl;
    
    std::unique_ptr<Component> decorator2 = 
        std::make_unique<ConcreteDecoratorB>(std::move(decorator1));
    std::cout << "Client: " << decorator2->operation() << std::endl;
}
```

### 14.2 C++中的函数式模式

#### 函数式编程概念

- **不可变性**：避免状态修改
- **纯函数**：无副作用的函数
- **高阶函数**：函数作为参数和返回值
- **函数组合**：构建复杂函数

#### C++实现

- **std::function**：函数包装器
- **Lambda表达式**：匿名函数
- **std::bind**：部分应用
- **值语义**：复制而非修改

```cpp
// C++函数式编程模式示例
# include <iostream>
# include <vector>
# include <string>
# include <functional>
# include <algorithm>
# include <numeric>
# include <optional>

// 函数式编程工具函数
namespace functional {
    // 组合两个函数：(f ∘ g)(x) = f(g(x))
    template<typename F, typename G>
    auto compose(F&& f, G&& g) {
        return [f = std::forward<F>(f), g = std::forward<G>(g)](auto&&... args) {
            return f(g(std::forward<decltype(args)>(args)...));
        };
    }
    
    // 柯里化：将接受多个参数的函数转换为接受一个参数的函数链
    template<typename Func, typename Arg>
    auto curry(Func&& f, Arg&& arg) {
        return [f = std::forward<Func>(f), arg = std::forward<Arg>(arg)](auto&&... args) {
            return f(arg, std::forward<decltype(args)>(args)...);
        };
    }
    
    // 部分应用：固定函数的一些参数
    template<typename Func, typename... Args>
    auto partial(Func&& f, Args&&... args) {
        return [f = std::forward<Func>(f), args = std::make_tuple(std::forward<Args>(args)...)]
               (auto&&... remainingArgs) {
            return std::apply(
                [&](auto&&... capturedArgs) {
                    return f(std::forward<decltype(capturedArgs)>(capturedArgs)...,
                             std::forward<decltype(remainingArgs)>(remainingArgs)...);
                },
                args
            );
        };
    }
    
    // 管道操作符：x | f = f(x)
    template<typename T, typename F>
    auto operator|(T&& value, F&& f) -> decltype(f(std::forward<T>(value))) {
        return f(std::forward<T>(value));
    }
    
    // Maybe (Optional) Monad
    template<typename T, typename F>
    auto bind(const std::optional<T>& opt, F&& f) -> decltype(f(std::declval<T>())) {
        if (opt) {
            return f(*opt);
        }
        return {};
    }
}

// 函数式风格的数据处理示例
void functional_programming_examples() {
    using namespace functional;
    
    std::cout << "=== C++ Functional Programming ===" << std::endl;
    
    // 高阶函数示例
    std::vector<int> numbers = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    
    // 使用纯函数进行转换
    auto square = [](int x) { return x * x; };
    auto isEven = [](int x) { return x % 2 == 0; };
    auto toString = [](int x) { return std::to_string(x); };
    
    // 函数组合
    auto squareAndToString = compose(toString, square);
    
    std::cout << "Composed function: " << squareAndToString(5) << std::endl;
    
    // 柯里化和部分应用
    auto add = [](int a, int b) { return a + b; };
    auto add5 = curry(add, 5);
    
    std::cout << "Curried function (add5): " << add5(10) << std::endl;
    
    auto multiply = [](int a, int b, int c) { return a * b * c; };
    auto multiplyBy2And3 = partial(multiply, 2, 3);
    
    std::cout << "Partial application: " << multiplyBy2And3(4) << std::endl;
    
    // 管道操作
    int result = 5 | square | add5;
    std::cout << "Pipeline (5 | square | add5): " << result << std::endl;
    
    // 数据处理示例
    std::cout << "\nData processing example:" << std::endl;
    
    auto transformNumbers = [&]() {
        std::vector<std::string> result;
        
        for (const auto& num : numbers) {
            if (num % 2 == 0) {
                result.push_back(std::to_string(num * num));
            }
        }
        
        return result;
    };
    
    auto functionalTransform = [&]() {
        std::vector<int> evenNumbers;
        std::copy_if(numbers.begin(), numbers.end(), std::back_inserter(evenNumbers), isEven);
        
        std::vector<int> squaredNumbers;
        std::transform(evenNumbers.begin(), evenNumbers.end(), std::back_inserter(squaredNumbers), square);
        
        std::vector<std::string> result;
        std::transform(squaredNumbers.begin(), squaredNumbers.end(), std::back_inserter(result), toString);
        
        return result;
    };
    
    auto modernTransform = [&]() {
        return numbers 
               | [](const auto& nums) { // 过滤偶数
                   std::vector<int> result;
                   std::copy_if(nums.begin(), nums.end(), std::back_inserter(result), isEven);
                   return result;
               }
               | [](const auto& nums) { // 对每个数平方
                   std::vector<int> result;
                   std::transform(nums.begin(), nums.end(), std::back_inserter(result), square);
                   return result;
               }
               | [](const auto& nums) { // 转换为字符串
                   std::vector<std::string> result;
                   std::transform(nums.begin(), nums.end(), std::back_inserter(result), toString);
                   return result;
               };
    };
    
    auto results = modernTransform();
    
    std::cout << "Even squared numbers: ";
    for (const auto& str : results) {
        std::cout << str << " ";
    }
    std::cout << std::endl;
    
    // Maybe (Optional) Monad示例
    std::cout << "\nOptional monad example:" << std::endl;
    
    auto safeDivide = [](int a, int b) -> std::optional<int> {
        if (b == 0) return std::nullopt;
        return a / b;
    };
    
    auto safeSqrt = [](int x) -> std::optional<double> {
        if (x < 0) return std::nullopt;
        return std::sqrt(x);
    };
    
    // 使用monadic绑定进行链式操作
    auto computeResult = [&](int a, int b) {
        return bind(safeDivide(a, b), [](int div_result) {
            return safeSqrt(div_result);
        });
    };
    
    auto goodResult = computeResult(16, 4);  // 16/4 = 4, sqrt(4) = 2
    auto badResult1 = computeResult(16, 0);  // 除以零
    auto badResult2 = computeResult(-4, 4);  // 尝试对负数求平方根
    
    std::cout << "16/4 then sqrt: " 
              << (goodResult ? std::to_string(*goodResult) : "Error") << std::endl;
    
    std::cout << "16/0 then sqrt: " 
              << (badResult1 ? std::to_string(*badResult1) : "Error") << std::endl;
    
    std::cout << "-4/4 then sqrt: " 
              << (badResult2 ? std::to_string(*badResult2) : "Error") << std::endl;
}
```

### 14.3 元编程设计模式

#### 模板元编程技术

- **编译期计算**：常量表达式、模板递归
- **类型操作**：类型特质、SFINAE
- **静态多态**：CRTP、Concepts

#### 元编程模式

- **类型列表**：编译期类型容器
- **类型级别状态机**：编译期状态转换
- **表达式模板**：优化数值计算

```cpp
// 元编程设计模式示例
# include <iostream>
# include <type_traits>
# include <string>
# include <tuple>
# include <utility>

// 编译期计算
template<int N>
struct Factorial {
    static constexpr int value = N * Factorial<N-1>::value;
};

template<>
struct Factorial<0> {
    static constexpr int value = 1;
};

// CRTP（奇异递归模板模式）
template<typename Derived>
class Base {
public:
    void interface() {
        // 调用派生类的实现
        static_cast<Derived*>(this)->implementation();
    }
    
    // 提供默认实现
    void implementation() {
        std::cout << "Default implementation in Base" << std::endl;
    }
};

class Derived1 : public Base<Derived1> {
public:
    void implementation() {
        std::cout << "Implementation in Derived1" << std::endl;
    }
};

class Derived2 : public Base<Derived2> {
    // 使用基类的默认实现
};

// 类型列表
template<typename... Ts>
struct TypeList {};

// 获取类型列表的长度
template<typename List>
struct Length;

template<typename... Ts>
struct Length<TypeList<Ts...>> {
    static constexpr size_t value = sizeof...(Ts);
};

// 获取类型列表中的第N个元素
template<size_t N, typename List>
struct TypeAt;

template<size_t N, typename T, typename... Ts>
struct TypeAt<N, TypeList<T, Ts...>> : TypeAt<N-1, TypeList<Ts...>> {};

template<typename T, typename... Ts>
struct TypeAt<0, TypeList<T, Ts...>> {
    using type = T;
};

// 添加元素到类型列表前面
template<typename T, typename List>
struct PushFront;

template<typename T, typename... Ts>
struct PushFront<T, TypeList<Ts...>> {
    using type = TypeList<T, Ts...>;
};

// 表达式模板
template<typename T>
class Vector {
private:
    std::vector<T> data;
    
public:
    explicit Vector(size_t size) : data(size) {}
    
    Vector(std::initializer_list<T> init) : data(init) {}
    
    size_t size() const { return data.size(); }
    
    T& operator[](size_t index) { return data[index]; }
    const T& operator[](size_t index) const { return data[index]; }
    
    // 支持表达式模板的加法
    template<typename Expr>
    Vector& operator+=(const Expr& expr) {
        for (size_t i = 0; i < size(); ++i) {
            data[i] += expr[i];
        }
        return *this;
    }
    
    // 普通加法
    Vector& operator+=(const Vector& other) {
        for (size_t i = 0; i < size(); ++i) {
            data[i] += other[i];
        }
        return *this;
    }
};

// 矢量加法表达式
template<typename LhsExpr, typename RhsExpr>
class VectorAddExpr {
private:
    const LhsExpr& lhs;
    const RhsExpr& rhs;
    
public:
    VectorAddExpr(const LhsExpr& lhs, const RhsExpr& rhs)
        : lhs(lhs), rhs(rhs) {}
    
    auto operator[](size_t index) const {
        return lhs[index] + rhs[index];
    }
    
    size_t size() const { return lhs.size(); }
};

// 操作符重载
template<typename LhsExpr, typename RhsExpr>
VectorAddExpr<LhsExpr, RhsExpr> operator+(const LhsExpr& lhs, const RhsExpr& rhs) {
    return VectorAddExpr<LhsExpr, RhsExpr>(lhs, rhs);
}

// 编译期状态机
// 简单示例：编译期的有限状态机，用于解析简单语法
enum class State { Start, Parsing, End, Error };

template<State S>
struct StateMachine;

template<>
struct StateMachine<State::Start> {
    template<char C>
    using

```cpp
    template<char C>
    using Transition = std::conditional_t<
        C == '{',
        StateMachine<State::Parsing>,
        StateMachine<State::Error>
    >;
};

template<>
struct StateMachine<State::Parsing> {
    template<char C>
    using Transition = std::conditional_t<
        C == '}',
        StateMachine<State::End>,
        StateMachine<State::Parsing>
    >;
};

template<>
struct StateMachine<State::End> {
    template<char C>
    using Transition = StateMachine<State::Error>;
};

template<>
struct StateMachine<State::Error> {
    template<char C>
    using Transition = StateMachine<State::Error>;
};

// 编译期字符串解析器
template<typename SM, typename Str, size_t Pos = 0>
struct Parser;

template<typename SM, size_t Pos>
struct Parser<SM, std::integer_sequence<char>, Pos> {
    using Result = SM;
};

template<typename SM, char C, char... Cs, size_t Pos>
struct Parser<SM, std::integer_sequence<char, C, Cs...>, Pos> {
    using NextState = typename SM::template Transition<C>;
    using Result = typename Parser<
        NextState, 
        std::integer_sequence<char, Cs...>, 
        Pos + 1
    >::Result;
};

// 元编程设计模式示例
void metaprogramming_examples() {
    std::cout << "=== Metaprogramming Design Patterns ===" << std::endl;
    
    // 编译期计算示例
    constexpr int fact5 = Factorial<5>::value;
    std::cout << "Factorial of 5 (compile-time): " << fact5 << std::endl;
    
    // CRTP示例
    std::cout << "\nCRTP Example:" << std::endl;
    
    Derived1 d1;
    d1.interface();  // 调用Derived1的实现
    
    Derived2 d2;
    d2.interface();  // 使用Base的默认实现
    
    // 类型列表示例
    std::cout << "\nType List Example:" << std::endl;
    
    using MyTypes = TypeList<int, double, std::string, float>;
    
    std::cout << "Length of type list: " << Length<MyTypes>::value << std::endl;
    
    using SecondType = typename TypeAt<1, MyTypes>::type;
    std::cout << "Second type is double: " 
              << std::is_same<SecondType, double>::value << std::endl;
    
    using ExtendedList = typename PushFront<char, MyTypes>::type;
    std::cout << "Extended list length: " << Length<ExtendedList>::value << std::endl;
    
    // 表达式模板示例
    std::cout << "\nExpression Templates Example:" << std::endl;
    
    Vector<double> v1 = {1.0, 2.0, 3.0, 4.0};
    Vector<double> v2 = {5.0, 6.0, 7.0, 8.0};
    Vector<double> v3 = {9.0, 10.0, 11.0, 12.0};
    Vector<double> result(4);
    
    // 不使用表达式模板：每个加法都创建一个临时向量
    // result = v1 + v2 + v3;
    
    // 使用表达式模板：避免创建临时向量
    result += v1 + v2 + v3;
    
    std::cout << "Result vector: ";
    for (size_t i = 0; i < result.size(); ++i) {
        std::cout << result[i] << " ";
    }
    std::cout << std::endl;
    
    // 编译期状态机示例
    std::cout << "\nCompile-time State Machine Example:" << std::endl;
    
    using ValidInput = std::integer_sequence<char, '{', 'a', 'b', 'c', '}'>;
    using InvalidInput = std::integer_sequence<char, '{', 'a', 'b', 'c'>;
    
    using ValidResult = Parser<StateMachine<State::Start>, ValidInput>::Result;
    using InvalidResult = Parser<StateMachine<State::Start>, InvalidInput>::Result;
    
    std::cout << "Valid input parsing ends in State::End: "
              << std::is_same<ValidResult, StateMachine<State::End>>::value << std::endl;
    
    std::cout << "Invalid input parsing ends in State::Error: "
              << std::is_same<InvalidResult, StateMachine<State::Error>>::value << std::endl;
}
```

### 14.4 性能优化模式

#### 性能关键模式

- **内存布局优化**：缓存友好设计
- **数据局部性**：提高缓存命中率
- **零拷贝技术**：减少数据复制
- **惰性计算**：延迟计算直到必要

#### 常见优化实践

- **内存池**：自定义内存分配
- **对象池**：重用对象减少分配
- **预分配**：避免动态内存分配
- **移动语义**：避免不必要的拷贝

```cpp
// 性能优化模式示例
# include <iostream>
# include <vector>
# include <chrono>
# include <memory>
# include <array>
# include <random>
# include <string>
# include <algorithm>
# include <new>

// 计时辅助类
class Timer {
private:
    std::chrono::high_resolution_clock::time_point start_time;
    std::string name;
    
public:
    explicit Timer(std::string name = "Operation")
        : start_time(std::chrono::high_resolution_clock::now()), name(std::move(name)) {}
    
    ~Timer() {
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
            end_time - start_time).count();
        std::cout << name << " took " << duration << " us" << std::endl;
    }
};

// 内存池分配器
template<typename T, size_t BlockSize = 4096>
class PoolAllocator {
private:
    struct Block {
        char data[BlockSize];
        Block* next;
    };
    
    struct Chunk {
        Chunk* next;
    };
    
    Block* current_block = nullptr;
    Chunk* free_chunk = nullptr;
    size_t chunks_per_block;
    
public:
    using value_type = T;
    
    PoolAllocator() : chunks_per_block(BlockSize / sizeof(T)) {
        if (sizeof(T) < sizeof(Chunk)) {
            chunks_per_block = BlockSize / sizeof(Chunk);
        }
    }
    
    ~PoolAllocator() {
        Block* block = current_block;
        while (block) {
            Block* next = block->next;
            delete block;
            block = next;
        }
    }
    
    T* allocate(size_t n = 1) {
        if (n > 1) {
            // 如果需要分配多个对象，回退到标准分配器
            return static_cast<T*>(::operator new(n * sizeof(T)));
        }
        
        if (free_chunk) {
            T* result = reinterpret_cast<T*>(free_chunk);
            free_chunk = free_chunk->next;
            return result;
        }
        
        if (!current_block || chunks_per_block == 0) {
            // 分配新块
            Block* new_block = new Block;
            new_block->next = current_block;
            current_block = new_block;
            
            // 初始化块中的所有chunk
            char* chunk_start = current_block->data;
            free_chunk = reinterpret_cast<Chunk*>(chunk_start);
            
            for (size_t i = 0; i < chunks_per_block - 1; ++i) {
                reinterpret_cast<Chunk*>(chunk_start)->next = 
                    reinterpret_cast<Chunk*>(chunk_start + sizeof(T));
                chunk_start += sizeof(T);
            }
            
            reinterpret_cast<Chunk*>(chunk_start)->next = nullptr;
        }
        
        T* result = reinterpret_cast<T*>(free_chunk);
        free_chunk = free_chunk->next;
        return result;
    }
    
    void deallocate(T* p, size_t n = 1) {
        if (n > 1) {
            // 如果分配了多个对象，回退到标准释放
            ::operator delete(p);
            return;
        }
        
        // 将对象添加回空闲列表
        Chunk* chunk = reinterpret_cast<Chunk*>(p);
        chunk->next = free_chunk;
        free_chunk = chunk;
    }
    
    template<typename... Args>
    void construct(T* p, Args&&... args) {
        new(p) T(std::forward<Args>(args)...);
    }
    
    void destroy(T* p) {
        p->~T();
    }
};

// 对象池模式
template<typename T>
class ObjectPool {
private:
    std::vector<std::unique_ptr<T>> pool;
    std::vector<T*> free_objects;
    
public:
    explicit ObjectPool(size_t initial_size = 10) {
        for (size_t i = 0; i < initial_size; ++i) {
            add_object();
        }
    }
    
    T* acquire() {
        if (free_objects.empty()) {
            add_object();
        }
        
        T* object = free_objects.back();
        free_objects.pop_back();
        return object;
    }
    
    void release(T* object) {
        free_objects.push_back(object);
    }
    
private:
    void add_object() {
        pool.push_back(std::make_unique<T>());
        free_objects.push_back(pool.back().get());
    }
};

// 数据布局优化：使用结构体数组
struct ParticleAoS {  // Array of Structures
    float x, y, z;    // 位置
    float vx, vy, vz; // 速度
    float r, g, b;    // 颜色
    float size;       // 大小
};

// 使用数组的结构体
struct ParticlesSoA {  // Structure of Arrays
    std::vector<float> x, y, z;    // 位置数组
    std::vector<float> vx, vy, vz; // 速度数组
    std::vector<float> r, g, b;    // 颜色数组
    std::vector<float> size;       // 大小数组
    
    void resize(size_t n) {
        x.resize(n); y.resize(n); z.resize(n);
        vx.resize(n); vy.resize(n); vz.resize(n);
        r.resize(n); g.resize(n); b.resize(n);
        size.resize(n);
    }
};

// 惰性求值示例
template<typename T>
class LazyValue {
private:
    std::function<T()> compute_func;
    mutable bool computed = false;
    mutable T value;
    
public:
    explicit LazyValue(std::function<T()> func)
        : compute_func(std::move(func)) {}
    
    const T& get() const {
        if (!computed) {
            value = compute_func();
            computed = true;
        }
        return value;
    }
    
    void reset() {
        computed = false;
    }
};

// 性能优化模式示例
void performance_optimization_examples() {
    std::cout << "=== Performance Optimization Patterns ===" << std::endl;
    
    // 内存池分配器示例
    std::cout << "\nMemory Pool Example:" << std::endl;
    
    constexpr int N = 100000;
    
    {
        Timer timer("Standard allocation");
        std::vector<int*> pointers;
        for (int i = 0; i < N; ++i) {
            pointers.push_back(new int(i));
        }
        
        for (auto ptr : pointers) {
            delete ptr;
        }
    }
    
    {
        Timer timer("Pool allocation");
        PoolAllocator<int> pool;
        std::vector<int*> pointers;
        
        for (int i = 0; i < N; ++i) {
            int* p = pool.allocate();
            pool.construct(p, i);
            pointers.push_back(p);
        }
        
        for (auto ptr : pointers) {
            pool.destroy(ptr);
            pool.deallocate(ptr);
        }
    }
    
    // 对象池示例
    std::cout << "\nObject Pool Example:" << std::endl;
    
    class ExpensiveObject {
    public:
        ExpensiveObject() {
            // 模拟昂贵的构造
            data.resize(1000);
            std::fill(data.begin(), data.end(), 0);
        }
        
        void reset() {
            // 重置对象状态而不是销毁重建
            std::fill(data.begin(), data.end(), 0);
        }
        
    private:
        std::vector<int> data;
    };
    
    {
        Timer timer("Without object pool");
        for (int i = 0; i < 1000; ++i) {
            auto obj = std::make_unique<ExpensiveObject>();
            // 使用对象...
        }
    }
    
    {
        Timer timer("With object pool");
        ObjectPool<ExpensiveObject> pool(10);
        
        for (int i = 0; i < 1000; ++i) {
            auto* obj = pool.acquire();
            // 使用对象...
            obj->reset();  // 重置状态
            pool.release(obj);
        }
    }
    
    // 数据布局优化示例
    std::cout << "\nData Layout Optimization Example:" << std::endl;
    
    constexpr int NUM_PARTICLES = 100000;
    
    // 生成随机数
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
    
    // 初始化数据
    std::vector<ParticleAoS> particles_aos(NUM_PARTICLES);
    ParticlesSoA particles_soa;
    particles_soa.resize(NUM_PARTICLES);
    
    for (int i = 0; i < NUM_PARTICLES; ++i) {
        // AoS初始化
        particles_aos[i].x = dist(gen);
        particles_aos[i].y = dist(gen);
        particles_aos[i].z = dist(gen);
        particles_aos[i].vx = dist(gen);
        particles_aos[i].vy = dist(gen);
        particles_aos[i].vz = dist(gen);
        particles_aos[i].r = dist(gen);
        particles_aos[i].g = dist(gen);
        particles_aos[i].b = dist(gen);
        particles_aos[i].size = dist(gen);
        
        // SoA初始化
        particles_soa.x[i] = particles_aos[i].x;
        particles_soa.y[i] = particles_aos[i].y;
        particles_soa.z[i] = particles_aos[i].z;
        particles_soa.vx[i] = particles_aos[i].vx;
        particles_soa.vy[i] = particles_aos[i].vy;
        particles_soa.vz[i] = particles_aos[i].vz;
        particles_soa.r[i] = particles_aos[i].r;
        particles_soa.g[i] = particles_aos[i].g;
        particles_soa.b[i] = particles_aos[i].b;
        particles_soa.size[i] = particles_aos[i].size;
    }
    
    // 测试AoS性能
    {
        Timer timer("AoS particle update");
        for (int i = 0; i < NUM_PARTICLES; ++i) {
            // 只更新位置
            particles_aos[i].x += particles_aos[i].vx * 0.1f;
            particles_aos[i].y += particles_aos[i].vy * 0.1f;
            particles_aos[i].z += particles_aos[i].vz * 0.1f;
        }
    }
    
    // 测试SoA性能
    {
        Timer timer("SoA particle update");
        for (int i = 0; i < NUM_PARTICLES; ++i) {
            // 只更新位置
            particles_soa.x[i] += particles_soa.vx[i] * 0.1f;
            particles_soa.y[i] += particles_soa.vy[i] * 0.1f;
            particles_soa.z[i] += particles_soa.vz[i] * 0.1f;
        }
    }
    
    // 惰性求值示例
    std::cout << "\nLazy Evaluation Example:" << std::endl;
    
    auto expensive_computation = []() {
        std::cout << "Performing expensive computation..." << std::endl;
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
        return 42;
    };
    
    LazyValue<int> lazy_value(expensive_computation);
    
    std::cout << "Lazy value created, but not computed yet" << std::endl;
    
    // 第一次获取值时会计算
    std::cout << "First access: " << lazy_value.get() << std::endl;
    
    // 后续获取直接返回缓存值
    std::cout << "Second access: " << lazy_value.get() << std::endl;
    
    // 重置后再次访问将重新计算
    lazy_value.reset();
    std::cout << "After reset, accessing again: " << lazy_value.get() << std::endl;
}

// 主函数
int main() {
    // 设计模式示例
    design_patterns_examples();
    
    // 函数式编程模式示例
    functional_programming_examples();
    
    // 元编程设计模式示例
    metaprogramming_examples();
    
    // 性能优化模式示例
    performance_optimization_examples();
    
    return 0;
}
```

## C++编程语言分析总结

通过深入研究和剖析C++编程语言的各个方面，我们全面了解了这门强大且多范式的语言。
从基础概念如变量、类型和控制流，到高级特质如元编程、并发和性能优化，我们系统地探索了C++的丰富特质和设计思想。

C++的优势在于其灵活性、性能和对底层系统的控制能力，
这使它在系统编程、游戏开发、高性能计算和金融系统等领域保持着不可替代的地位。
而近年来的标准更新（C++17/20/23）进一步增强了语言的表达能力和易用性，同时保持了向后兼容性。

同时，C++的复杂性和历史包袱也是不容忽视的。
多种范式的支持、复杂的模板机制、丰富的语言特质和细微的语义规则使得彻底掌握C++成为一项具有挑战性的工作。
这也提醒我们在开发过程中应重视代码简洁性、可读性和可维护性。

无论如何，C++作为一门成熟而强大的编程语言，仍将在计算机软件开发中占据重要位置，
特别是在对性能和资源控制要求较高的应用领域。
深入理解C++的类型系统、内存模型、执行模型和设计模式，将有助于我们编写更高效、更安全、更优雅的代码。
