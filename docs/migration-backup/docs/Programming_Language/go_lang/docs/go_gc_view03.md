# 编程语言 GC 体系分析

## 目录

- [编程语言 GC 体系分析](#编程语言-gc-体系分析)
  - [目录](#目录)
  - [1. 引言：什么是垃圾回收？](#1-引言什么是垃圾回收)
  - [2. 常见的 GC 算法模型](#2-常见的-gc-算法模型)
    - [2.1. 引用计数 (Reference Counting)](#21-引用计数-reference-counting)
    - [2.2. 标记-清除 (Mark-Sweep)](#22-标记-清除-mark-sweep)
    - [2.3. 标记-整理 (Mark-Compact)](#23-标记-整理-mark-compact)
    - [2.4. 复制算法 (Copying GC / Semi-space)](#24-复制算法-copying-gc--semi-space)
    - [2.5. 分代收集 (Generational GC)](#25-分代收集-generational-gc)
    - [2.6. 并发与增量 GC (Concurrent \& Incremental GC)](#26-并发与增量-gc-concurrent--incremental-gc)
  - [3. 语言构件与 GC 分析](#3-语言构件与-gc-分析)
    - [3.1. 变量与作用域](#31-变量与作用域)
    - [3.2. 类型系统](#32-类型系统)
    - [3.3. 控制流](#33-控制流)
  - [4. 变量类型与 GC 的关联性](#4-变量类型与-gc-的关联性)
  - [5. 形式化分析](#5-形式化分析)
    - [5.1. 核心概念](#51-核心概念)
    - [5.2. 基本定义 (以 Mark-Sweep 为例)](#52-基本定义-以-mark-sweep-为例)
    - [5.3. 逻辑推理与权衡](#53-逻辑推理与权衡)
    - [5.4. 综合分析](#54-综合分析)
  - [6. 代码示例](#6-代码示例)
    - [6.1. Go](#61-go)
    - [6.2. Python](#62-python)
    - [6.3. JavaScript / TypeScript](#63-javascript--typescript)
  - [7. 编程语言的生命周期管理](#7-编程语言的生命周期管理)
  - [8. 总结](#8-总结)
  - [9. 思维导图 (Text)](#9-思维导图-text)

---

## 1. 引言：什么是垃圾回收？

垃圾回收（Garbage Collection, GC）是一种自动内存管理机制。在支持 GC 的语言中，程序员无需手动分配和释放内存（像 C/C++ 中的 `malloc`/`free` 或 `new`/`delete`）。运行时环境（Runtime）或虚拟机（VM）会自动检测哪些内存对象不再被程序使用（成为“垃圾”），并回收它们占用的空间，以供后续分配使用。GC 的主要目标是简化内存管理、减少内存泄漏和悬挂指针等错误。

## 2. 常见的 GC 算法模型

不同的编程语言和运行时环境采用了不同的 GC 策略，通常是几种基础算法的组合与优化。

### 2.1. 引用计数 (Reference Counting)

- **模型**: 为每个对象维护一个引用计数器。当有一个新的引用指向该对象时，计数器加 1；当一个引用离开作用域或被重新赋值时，计数器减 1。当计数器变为 0 时，表示该对象不再被任何引用指向，可以立即回收。
- **优点**:
  - 内存回收及时，对象不再被引用时可以立即回收，避免了长时间的 GC 停顿（Pause）。
  - 实现相对简单。
- **缺点**:
  - **循环引用**: 如果两个或多个对象相互引用，即使它们对外部来说已经不可达，它们的引用计数也不会是 0，导致内存泄漏。需要额外的机制（如循环引用检测器）来处理。
  - **计数器维护开销**: 引用赋值是高频操作，频繁更新计数器会带来性能开销。
  - **原子操作**: 在并发环境中，更新计数器需要原子操作，进一步增加开销。
- **应用**: Python (CPython 主要使用，并辅以分代回收和循环引用检测), Swift, PHP (Zend Engine)。

### 2.2. 标记-清除 (Mark-Sweep)

- **模型**: 这是基于可达性（Reachability）分析的算法。
    1. **标记 (Mark) 阶段**: 从一组根对象（Roots，如全局变量、栈上的引用）开始，遍历所有可达的对象，并进行标记。
    2. **清除 (Sweep) 阶段**: 遍历整个堆内存，将所有未被标记的对象视为垃圾，回收它们占用的空间。
- **优点**:
  - 可以解决引用计数的循环引用问题。
- **缺点**:
  - **STW (Stop-The-World)**: 在标记和清除阶段，通常需要暂停应用程序（Mutator）的执行，导致明显的停顿，影响响应性。
  - **内存碎片**: 清除后会产生大量不连续的内存碎片，可能导致后续大对象分配失败。
- **应用**: 这是许多现代 GC 算法的基础。早期的 Lisp 系统使用。

### 2.3. 标记-整理 (Mark-Compact)

- **模型**: 是标记-清除的改进，旨在解决内存碎片问题。
    1. **标记 (Mark) 阶段**: 同标记-清除。
    2. **整理 (Compact) 阶段**: 将所有存活的对象移动到内存的一端，使它们连续排列。然后更新指向这些对象的引用。最后，回收掉另一端的所有空闲内存。
- **优点**:
  - 解决了内存碎片问题，提高了内存分配效率。
  - 解决了循环引用问题。
- **缺点**:
  - **STW**: 仍然需要 Stop-The-World。
  - **移动开销**: 移动对象和更新引用的成本较高。
- **应用**: Java HotSpot VM 的老年代 GC (Parallel Old GC, Serial Old GC) 中有使用。

### 2.4. 复制算法 (Copying GC / Semi-space)

- **模型**: 将堆内存分为两个大小相等的空间：From 空间和 To 空间。同一时间只有一个空间处于活动状态（用于分配）。
    1. **分配**: 新对象总是在当前活动空间（比如 From 空间）分配。
    2. **回收**: 当 From 空间满了之后，触发 GC。从根对象开始遍历，将所有可达的（存活的）对象复制到 To 空间。
    3. **切换**: 复制完成后，From 空间剩下的都是垃圾，可以整体清空。然后交换 From 和 To 空间的角色。
- **优点**:
  - **无内存碎片**: 每次回收后，存活对象都紧凑地排列在新的活动空间。
  - **分配速度快**: 只需移动指针即可分配内存。
  - 实现相对简单。
- **缺点**:
  - **内存利用率低**: 需要双倍的内存空间，实际只能使用一半。
  - **复制开销**: 如果存活对象很多，复制开销会很大。
- **应用**: 常用于新生代 GC (如 Java HotSpot VM 的 Eden 区和 Survivor 区, V8 的新生代)。因为新生代对象通常“朝生夕死”，存活率低，复制开销小。

### 2.5. 分代收集 (Generational GC)

- **模型**: 基于一个重要的观察：“大部分对象存活时间很短（弱分代假说），而很少一部分对象会存活很长时间（强分代假说）”。
  - 将堆内存划分为不同的“代”（Generation），通常是新生代（Young Generation）和老年代（Old Generation）。
  - 新创建的对象首先分配在新生代。
  - 新生代 GC 频率较高，但因为存活对象少，回收速度快，通常使用复制算法。
  - 经过多次新生代 GC 仍然存活的对象会被“晋升”（Promote）到老年代。
  - 老年代 GC 频率较低，但每次耗时可能较长，通常使用标记-清除或标记-整理算法。
  - 需要处理跨代引用问题（老年代对象引用新生代对象），通常使用“卡表”（Card Table）等技术记录。
- **优点**:
  - 针对不同代的特点使用不同算法，提高了整体 GC 效率。
  - 显著减少了 Full GC（回收整个堆）的频率和停顿时间。
- **缺点**:
  - 实现更复杂。
  - 跨代引用处理有额外开销。
- **应用**: 非常普遍，Java HotSpot VM, .NET CLR, V8 (JavaScript), Python (结合引用计数) 等都在使用。

### 2.6. 并发与增量 GC (Concurrent & Incremental GC)

- **目标**: 减少或消除 STW 停顿时间，提高应用程序的响应性。
- **并发 GC (Concurrent GC)**: 允许 GC 线程与应用程序线程（Mutator）并发执行。标记、清除等阶段可以部分或全部与用户程序并行。这需要复杂的同步机制（如写屏障 Write Barrier）来处理并发执行期间对象引用关系的变化。例如 Go 的 GC，Java 的 CMS (Concurrent Mark Sweep) 和 G1 (Garbage-First)。
- **增量 GC (Incremental GC)**: 将较长的 GC 周期（如标记阶段）分解成多个小的步骤，交错地在应用程序线程的执行间隙中运行。虽然总的 GC 时间可能增加，但单次停顿时间变短。例如 V8 的 Orinoco GC 使用增量标记。
- **优点**: 显著降低了 STW 停顿时间，对实时性要求高的应用（如图形界面、服务器）非常重要。
- **缺点**:
  - 实现非常复杂。
  - 可能引入额外的运行时开销（如写屏障）。
  - 并发 GC 可能无法完全消除 STW（例如 G1 仍有短暂 STW）。
  - 可能产生“浮动垃圾”（Floating Garbage），即在并发标记期间产生的垃圾需要等到下一次 GC 才能回收。
- **应用**: Go, Java (CMS, G1, ZGC, Shenandoah), V8。

## 3. 语言构件与 GC 分析

编程语言的基本构件（变量、类型、控制流）与 GC 机制紧密相关。

### 3.1. 变量与作用域

- **变量**: 变量是存储值的命名内存位置。在支持 GC 的语言中，变量通常存储两种东西：
  - **值类型 (Value Types)**: 如基本数据类型（int, float, bool 等）或结构体（struct）。它们的值通常直接存储在变量所在的内存区域（栈或对象内部）。
  - **引用类型 (Reference Types)**: 如对象、数组、闭包等。变量存储的是指向堆（Heap）上实际数据的内存地址（引用或指针）。
- **作用域 (Scope)**: 变量的可访问性范围（如函数局部作用域、全局作用域）。
  - **栈分配**: 局部变量通常在函数调用时在栈（Stack）上分配。当函数返回时，其栈帧被销毁，这些局部变量（及其可能包含的值类型数据）也随之消失。如果局部变量持有对堆对象的引用，那么这个引用会消失。
  - **堆分配**: 对象等引用类型通常在堆上分配。它们的生命周期与创建它们的作用域无关，而是由是否存在指向它们的引用决定。
- **GC 的关联**: GC 主要关注堆上分配的对象。当一个堆对象的最后一个引用（可能来自栈上的局部变量、全局变量或其他堆对象）消失时（例如，局部变量离开作用域，全局变量被重新赋值，对象内部的引用被修改），该对象就成为潜在的垃圾。GC 通过可达性分析（从根集合出发）来确定哪些堆对象是存活的。

### 3.2. 类型系统

- **静态类型 vs 动态类型**:
  - **静态类型语言 (如 Go, Java, C#)**: 在编译时就知道每个变量的类型。GC 可以利用这些类型信息来确定对象的大小、内部结构（哪些字段是引用，哪些是值），从而更高效地遍历对象图和管理内存。
  - **动态类型语言 (如 Python, JavaScript, Ruby)**: 变量类型在运行时确定。GC 需要在运行时检查对象的类型信息（通常通过对象头部的元数据）来了解其结构和大小。这可能增加 GC 的复杂度和开销。
- **值类型 vs 引用类型**:
  - **值类型**: 通常在栈上分配（如果是局部变量）或嵌入在包含它们的对象内部。它们不直接由 GC 管理其生命周期（除了它们所在的栈帧或对象的生命周期）。
  - **引用类型**: 在堆上分配，由 GC 负责管理其生命周期。变量或字段存储的是指向堆内存的引用。
- **GC 的关联**: 类型系统告知了 GC 内存中数据的布局方式。GC 需要知道一个内存块代表什么类型的对象，对象有多大，以及对象内部哪些部分是指向其他对象的引用，以便进行可达性分析。

### 3.3. 控制流

- **函数调用**: 创建新的栈帧，分配局部变量。函数返回时栈帧销毁。这直接影响栈上引用的生命周期。
- **循环和条件**: 控制代码的执行路径，从而影响对象在何时被创建、使用以及何时可能变得不再被引用。
- **闭包 (Closures)**: 闭包可以捕获其定义时所在作用域的变量。如果闭包本身存活时间较长（例如被存储在全局变量或传递到其他地方），它会使其捕获的变量（包括对堆对象的引用）持续存活，即使定义它们的原作用域已经结束。这是潜在内存泄漏的一个常见来源，GC 需要能正确处理闭包持有的引用。
- **并发/异步操作**: 在多线程或异步模型（如 `async/await`）中，对象的生命周期管理变得更复杂。一个对象可能被多个线程或异步任务引用，GC 必须能安全、正确地处理这些并发访问和引用变化。并发 GC 算法在这种场景下尤为重要。
- **GC 的关联**: 控制流决定了程序在运行时如何以及何时访问和修改对象引用。GC 必须在程序执行的任何时刻都能准确判断对象的可达性，即使在复杂的控制流（如异常处理、并发）下也是如此。

## 4. 变量类型与 GC 的关联性

变量类型和 GC 的关联主要体现在内存分配位置和生命周期管理方式上：

1. **分配位置**:
    - **值类型 (Primitives, Structs in some languages)**: 通常在栈上分配（如果是局部变量）或直接嵌入在包含它们的对象中（如果是对象成员）。栈内存管理简单，通过栈指针移动即可分配和释放，不由 GC 直接管理。
    - **引用类型 (Objects, Arrays, Closures)**: 总是在堆上分配。堆内存的管理更为复杂，需要 GC 来回收不再使用的空间。
2. **生命周期**:
    - **值类型**: 生命周期通常与其所在的作用域（栈帧）或包含它的对象绑定。
    - **引用类型**: 生命周期由其可达性决定，即是否存在至少一个有效的引用指向它。GC 的核心任务就是跟踪这种可达性。
3. **GC 扫描**:
    - GC 从根集合（栈、全局变量等）开始扫描。当扫描到一个引用时，它会跟随这个引用去访问堆上的对象。
    - 对于静态类型语言，GC 可以精确知道对象内部哪些字段是引用，需要继续扫描，哪些是值类型数据，无需扫描。
    - 对于动态类型语言，GC 需要依赖对象的元信息来判断字段是指向其他对象（需要扫描）还是包含基本数据。
4. **优化**:
    - **逃逸分析 (Escape Analysis)**: 现代编译器和 JIT 会进行逃逸分析。如果能确定一个对象（通常是引用类型）的作用域完全局限在一个函数内，并且不会被外部引用（即“不逃逸”），编译器可能会将其优化为在栈上分配，从而避免了堆分配和 GC 的开销。Go 语言在这方面做了很多优化。

总之，类型系统为 GC 提供了关于内存布局和引用关系的关键信息，决定了哪些数据需要 GC 管理，以及 GC 如何有效地扫描和回收内存。

## 5. 形式化分析

### 5.1. 核心概念

- **Mutator**: 指应用程序本身，它执行计算任务，创建和修改对象，改变对象间的引用关系。
- **Collector**: 指垃圾回收器，负责查找和回收 Mutator 不再使用的内存。
- **Heap**: 堆内存区域，用于动态分配对象。是 GC 工作的主要场所。
- **Stack**: 栈内存区域，用于存储函数调用的上下文（栈帧），包括局部变量和函数参数。栈上的引用是 GC 的重要根节点。
- **Roots**: 根集合，是 GC 开始扫描的起点。通常包括：
  - 全局变量
  - 当前线程栈上的所有局部变量和参数
  - CPU 寄存器中的引用
  - JNI 或其他本地接口中的引用
- **Object Graph**: 由堆中的对象以及它们之间的引用关系构成的有向图。节点是对象，边是引用。
- **Reachability**: 可达性。一个对象是可达的，如果从根集合出发，沿着引用链（图的边）可以访问到该对象。
- **Live Object**: 存活对象，指可达的对象。Mutator 可能会在未来访问它们。
- **Garbage**: 垃圾对象，指不可达的对象。Mutator 永远无法再访问它们，它们占用的内存可以被回收。

### 5.2. 基本定义 (以 Mark-Sweep 为例)

设 \( H \) 为堆内存中的所有对象的集合。
设 \( R \subseteq H \) 为根集合直接引用的对象的集合。
设 \( \text{ref}(o) \) 为对象 \( o \in H \) 内部包含的指向其他堆对象的引用集合。

**可达性定义**:
对象集合 \( \text{Reachable} \) 是满足以下条件的最小集合：

1. \( R \subseteq \text{Reachable} \) (根直接引用的对象是可达的)
2. 如果 \( o \in \text{Reachable} \) 且 \( o' \in \text{ref}(o) \)，则 \( o' \in \text{Reachable} \) (被可达对象引用的对象也是可达的)

**垃圾定义**:
垃圾对象集合 \( \text{Garbage} = H \setminus \text{Reachable} \)。

**Mark-Sweep 过程**:

1. **Mark**: 计算 \( \text{Reachable} \) 集合。通常通过图遍历算法（如深度优先 DFS 或广度优先 BFS）实现，从 \( R \) 出发，标记所有访问到的节点。
    \[ \text{Marked} = \text{traverse}(R) \]
    理论上 \( \text{Marked} = \text{Reachable} \)。
2. **Sweep**: 遍历整个堆 \( H \)，回收所有未被标记的对象。
    \[ \text{for } o \in H \text{ do} \]
    \[ \quad \text{if } o \notin \text{Marked} \text{ then} \]
    \[ \quad \quad \text{reclaim_memory}(o) \]
    \[ \quad \text{else} \]
    \[ \quad \quad \text{unmark}(o) \quad \text{// 为下次 GC 做准备} \]

### 5.3. 逻辑推理与权衡

**GC 正确性**:

- **安全性 (Safety)**: GC 绝不能回收存活的对象 (No live object should be collected)。形式化表示为：被回收的对象集合必须是 \( \text{Garbage} \) 的子集。 \( \forall o \in H, \text{if } o \text{ is reclaimed, then } o \notin \text{Reachable} \)。这是 GC 最基本的要求。
- **活性 (Liveness)**: GC 最终必须回收所有垃圾对象 (All garbage objects should eventually be collected)。形式化表示为：\( \forall o \in \text{Garbage}, o \text{ will eventually be reclaimed} \)。这保证了内存不会无限泄漏。

**性能权衡 (Trade-offs)**:

- **吞吐量 (Throughput)**: 应用线程执行时间占总时间的比例。高吞吐量意味着 GC 开销小。STW 时间长会降低吞吐量。
- **延迟 (Latency)**: GC 导致的应用程序最大停顿时间。低延迟对交互式应用和实时系统至关重要。并发/增量 GC 主要目标是降低延迟。
- **内存开销 (Memory Overhead)**: GC 自身需要的数据结构（如卡表、记忆集、引用计数器）以及算法策略（如复制算法需要双倍空间）所占用的额外内存。
- **暂停一致性 (Pause Consistency)**: 每次 GC 停顿时间是否稳定可预测。
- **实现复杂度**: 不同 GC 算法的实现难度差异很大。

没有完美的 GC 算法能在所有方面都做到最优。选择哪种 GC 策略取决于应用的具体需求和运行环境的特点。例如：

- 服务器后台应用可能更看重吞吐量。
- GUI 应用或游戏可能更看重低延迟。
- 嵌入式系统可能对内存开销非常敏感。

### 5.4. 综合分析

GC 是一个复杂的系统工程，涉及算法、数据结构、编译器优化、操作系统交互等多个方面。现代 GC 系统的发展趋势是：

- **更低的延迟**: 通过并发、增量、并行技术减少 STW。
- **更高的效率**: 结合多种算法（如分代收集）取长补短。
- **自适应**: 根据应用程序的运行状况动态调整 GC 策略和参数。
- **与编译器/运行时更紧密的集成**: 利用逃逸分析、类型信息等进行优化。

语言设计者在选择 GC 策略时，会考虑语言的目标场景、性能要求、实现复杂度等因素。例如，Go 语言设计之初就强调低延迟和高并发，因此采用了并发标记-清除（三色标记法）的 GC。Python 则因为历史原因和 C 扩展的兼容性，选择了引用计数为主、分代回收和循环检测为辅的策略。JavaScript 引擎（如 V8）通常采用高效的分代 GC（新生代用复制，老年代用并发/增量标记-整理）来应对 Web 应用中对象生命周期差异大的特点。

## 6. 代码示例

以下示例仅用于说明概念，具体 GC 行为由各语言的运行时决定，通常对开发者透明。

### 6.1. Go

Go 语言使用并发的标记-清除 GC。开发者通常不需要关心 GC，但可以通过 `runtime` 包观察或手动触发。

```go
package main

import (
 "fmt"
 "runtime"
 "time"
)

type Data struct {
 value int
 arr   [1024 * 10]byte // 占用一些内存
}

func createGarbage() {
 // 函数执行完毕后，d 的引用消失，指向的 Data 对象成为垃圾
 d := &Data{value: 1}
 fmt.Printf("Local object created: %p\n", d)
}

func main() {
 var stats runtime.MemStats

 // 创建大量垃圾
 for i := 0; i < 10000; i++ {
  createGarbage()
 }

 runtime.ReadMemStats(&stats)
 fmt.Printf("Before manual GC - Alloc: %d MiB, NumGC: %d\n", stats.Alloc/1024/1024, stats.NumGC)

 // 手动触发 GC (通常不需要)
 fmt.Println("Running manual GC...")
 runtime.GC()
 fmt.Println("Manual GC finished.")

 runtime.ReadMemStats(&stats)
 fmt.Printf("After manual GC - Alloc: %d MiB, NumGC: %d\n", stats.Alloc/1024/1024, stats.NumGC)

 // 让程序运行一段时间，观察自动 GC
 fmt.Println("Waiting for potential automatic GC...")
 time.Sleep(5 * time.Second)

 runtime.ReadMemStats(&stats)
 fmt.Printf("After waiting - Alloc: %d MiB, NumGC: %d\n", stats.Alloc/1024/1024, stats.NumGC)
}
```

### 6.2. Python

Python (CPython) 主要使用引用计数，辅以分代 GC 和循环引用检测。

```python
import sys
import gc

# 引用计数示例
a = []  # 创建一个列表对象，引用计数为 1
print(f"Initial ref count of []: {sys.getrefcount(a) - 1}") # getrefcount 本身会增加一次引用

b = a   # 新引用指向对象，计数器 +1
print(f"Ref count after b = a: {sys.getrefcount(a) - 1}")

c = a   # 再加一个引用，计数器 +1
print(f"Ref count after c = a: {sys.getrefcount(a) - 1}")

del c   # 删除一个引用，计数器 -1
print(f"Ref count after del c: {sys.getrefcount(a) - 1}")

del b   # 再删除一个引用，计数器 -1
print(f"Ref count after del b: {sys.getrefcount(a) - 1}")

# 当 a 也被删除或重新赋值时，计数器变为 0，对象被回收
print("-" * 20)

# 循环引用示例
class Node:
    def __init__(self, name):
        self.name = name
        self.neighbor = None
        print(f"Node {self.name} created")

    def __del__(self):
        # 这个方法在对象被回收时调用
        # 注意：如果存在循环引用且没被 GC 处理，这个可能不会被调用
        print(f"Node {self.name} destroyed")

# 创建循环引用
n1 = Node("A")
n2 = Node("B")
n1.neighbor = n2
n2.neighbor = n1

print(f"Ref count n1: {sys.getrefcount(n1) - 1}") # n1, n2.neighbor
print(f"Ref count n2: {sys.getrefcount(n2) - 1}") # n2, n1.neighbor

# 删除外部引用
del n1
del n2

# 此时 n1 和 n2 互相引用，引用计数不为 0，但它们已不可达
# 引用计数无法回收它们

# 手动触发分代 GC (包含循环引用检测)
print("Running manual GC for cycle detection...")
collected_count = gc.collect() # 返回回收的对象数量
print(f"Objects collected by GC: {collected_count}")

# 如果循环引用被打破，__del__ 会被调用 (取决于具体实现和时机)

print("-" * 20)
# 查看 GC 状态
print(f"GC enabled: {gc.isenabled()}")
print(f"GC thresholds: {gc.get_threshold()}") # (gen0, gen1, gen2) 触发回收的阈值
print(f"GC counts: {gc.get_count()}")       # 当前各代对象数量
```

### 6.3. JavaScript / TypeScript

JavaScript (以及编译成 JS 的 TypeScript) 的 GC 由 JS 引擎（如 V8, SpiderMonkey）实现，
通常是分代 GC (新生代用复制，老年代用并发标记整理)。
开发者无法直接控制或观察 GC，只能理解其原理以避免内存泄漏。

```typescript
// TypeScript (编译后行为同 JavaScript)

function createObjects() {
    let obj1: any = { name: "Object 1" };
    let obj2: any = { name: "Object 2" };

    // 创建一个闭包，它引用了 obj1
    let closure = () => {
        console.log(obj1.name); // 闭包捕获了 obj1
    };

    obj1 = null; // 移除了 obj1 的直接引用
    obj2 = null; // 移除了 obj2 的直接引用，obj2 现在是垃圾

    // obj1 仍然被 closure 引用，所以不是垃圾
    // 当 closure 不再可达时（例如，如果 closure 是局部变量且函数返回），obj1 才可能成为垃圾

    // 如果 closure 被全局变量或其他长期存活的对象引用，obj1 也将长期存活
    // (window as any).myClosure = closure; // 示例：挂到全局对象上，导致 obj1 无法回收

    console.log("Objects created and references potentially removed.");
    // 在这里，obj2 肯定是垃圾了
    // obj1 的命运取决于 closure 是否还存活

    // 模拟 closure 被使用
    // closure();
}

createObjects();

// JS 引擎会在合适的时机自动运行 GC
console.log("Function finished. GC might run later.");

// 另一个潜在泄漏：DOM 引用
// let element = document.getElementById('myElement');
// let data = { largeData: new Array(1000000).fill('*') };
// // 如果 element 和 data 互相引用，并且 element 从 DOM 中移除但 JS 引用仍在，可能导致泄漏
// (element as any).myData = data;
// data.domElement = element;
// // ... later remove element from DOM ...
// // element = null; // 需要断开 JS 引用
// // data = null;
```

开发者主要需要关注的是避免无意中保持对不再需要的对象的引用，例如：

- 未解除的事件监听器。
- 存储在全局变量或长期存活对象中的临时数据。
- 闭包意外捕获了大的对象。
- DOM 节点被移除后，JavaScript 代码中仍然持有其引用。

## 7. 编程语言的生命周期管理

对于采用 GC 的语言，对象的生命周期管理可以概括为以下阶段：

1. **分配 (Allocation)**: 当程序需要新的对象时（如 `new`, `{}` , `[]`），运行时从堆内存中分配一块空间。分配策略因 GC 算法而异（如在 Eden 区顺序分配，或在空闲列表中查找）。
2. **使用 (Usage)**: 程序通过变量（引用）访问和操作对象（Mutator 工作）。对象的状态可能改变，对象间的引用关系也可能改变。
3. **不可达 (Becoming Unreachable)**: 当没有任何活动的引用链（从根集合出发）能够到达某个对象时，该对象就变成不可达状态。这通常发生在最后一个指向它的引用消失时（离开作用域、被覆盖、对象本身被回收等）。
4. **检测 (Detection)**: GC 运行时（Collector）启动，通过其算法（引用计数、标记、复制等）来检测哪些对象是不可达的（即垃圾）。
5. **回收 (Reclamation/Collection)**: GC 回收不可达对象占用的内存空间，使其可以被重新分配。回收方式包括直接标记为空闲（Mark-Sweep）、移动存活对象整理内存（Mark-Compact）、或直接清空整个区域（Copying）。
6. **终结 (Finalization - 可选)**: 某些语言提供终结器（Finalizer，如 C# 的 `Finalize` 方法，Java 的 `finalize()` - 已不推荐使用）或析构函数（如 Python 的 `__del__`）。这些方法在对象被 GC 回收*之前*（或大约那个时候）可能被调用，用于释放对象占用的非内存资源（如文件句柄、网络连接）。但终结器的执行时机和顺序通常不确定，且可能带来复杂性，不应用于常规内存管理。

与手动内存管理（如 C/C++）相比，GC 极大地简化了程序员的工作，但也引入了 GC 自身的开销和可能的不可预测性（如 STW 停顿）。理解 GC 的基本原理有助于编写更高效、更健壮的程序。

## 8. 总结

垃圾回收是现代编程语言中一项关键的自动内存管理技术。它通过各种算法模型（引用计数、标记清除/整理、复制、分代、并发/增量）自动管理堆内存中对象的生命周期，核心在于区分存活对象和垃圾对象，并回收垃圾对象占用的空间。语言的变量、类型系统和控制流都与 GC 如何识别和管理对象引用密切相关。不同的 GC 算法在吞吐量、延迟、内存开销和实现复杂度之间存在不同的权衡。选择和优化 GC 策略是语言运行时设计的核心挑战之一，旨在平衡性能、响应性和开发效率。

## 9. 思维导图 (Text)

```text
垃圾回收 (GC) 体系分析
│
├── 1. 定义与目标
│   ├── 自动内存管理
│   ├── 回收不可达对象 (Garbage)
│   └── 简化开发、减少错误 (内存泄漏、悬挂指针)
│
├── 2. GC 算法模型
│   ├── 引用计数 (Reference Counting)
│   │   ├── 机制: 维护计数器，为 0 时回收
│   │   ├── 优点: 回收及时
│   │   └── 缺点: 循环引用问题、计数开销、并发原子性
│   ├── 标记-清除 (Mark-Sweep)
│   │   ├── 机制: 标记可达对象 -> 清除未标记对象
│   │   ├── 优点: 解决循环引用
│   │   └── 缺点: STW (Stop-The-World)、内存碎片
│   ├── 标记-整理 (Mark-Compact)
│   │   ├── 机制: 标记 -> 移动存活对象 -> 清除边界外
│   │   ├── 优点: 解决碎片问题
│   │   └── 缺点: STW、移动开销
│   ├── 复制算法 (Copying GC)
│   │   ├── 机制: From/To 空间切换，复制存活对象
│   │   ├── 优点: 无碎片、分配快
│   │   └── 缺点: 内存利用率低 (一半)、复制开销
│   ├── 分代收集 (Generational GC)
│   │   ├── 机制: 基于分代假说 (新生代/老年代)，不同代用不同算法
│   │   ├── 优点: 高效，减少 Full GC
│   │   └── 缺点: 实现复杂，跨代引用处理 (Card Table)
│   └── 并发与增量 GC (Concurrent & Incremental)
│       ├── 目标: 减少/消除 STW 停顿
│       ├── 机制: GC 与应用并发/交错执行
│       ├── 技术: 三色标记法、写屏障 (Write Barrier)
│       └── 缺点: 复杂、额外开销、浮动垃圾
│
├── 3. 语言构件与 GC
│   ├── 变量与作用域
│   │   ├── 值类型 (栈/内嵌) vs 引用类型 (堆)
│   │   └── 作用域决定栈上引用生命周期，堆对象由可达性决定
│   ├── 类型系统
│   │   ├── 静态类型: 提供对象结构信息给 GC
│   │   └── 动态类型: GC 需运行时检查元信息
│   └── 控制流
│       ├── 函数调用、循环、条件 -> 影响引用创建与销毁
│       ├── 闭包 -> 延长捕获变量生命周期
│       └── 并发/异步 -> 增加 GC 复杂度
│
├── 4. 变量类型与 GC 关联
│   ├── 分配位置 (栈 vs 堆)
│   ├── 生命周期管理 (作用域绑定 vs 可达性)
│   ├── GC 扫描依赖类型信息 (识别引用)
│   └── 优化: 逃逸分析 (栈上分配)
│
├── 5. 形式化分析
│   ├── 核心概念: Mutator, Collector, Heap, Stack, Roots, Object Graph, Reachability, Live, Garbage
│   ├── 基本定义: 可达性计算，垃圾识别
│   ├── 正确性: 安全性 (不收活的), 活性 (收尽垃圾)
│   └── 性能权衡: 吞吐量, 延迟, 内存开销, 暂停一致性, 复杂度
│
├── 6. 代码示例 (Go, Python, JS/TS)
│   ├── Go: 并发 Mark-Sweep，runtime.GC()
│   ├── Python: 引用计数 + 分代 + 循环检测，sys.getrefcount(), gc.collect()
│   └── JS/TS: 引擎实现 (V8: 分代)，开发者透明，关注避免泄漏 (闭包, DOM 引用)
│
└── 7. 生命周期管理
    ├── 分配 -> 使用 -> 不可达 -> 检测 -> 回收 -> (终结)
    └── 对比手动管理 (malloc/free)
```
