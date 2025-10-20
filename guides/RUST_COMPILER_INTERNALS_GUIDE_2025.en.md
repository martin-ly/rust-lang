# 🔧 Rust Compiler Internals Complete Guide (2025 Edition)

> **Version**: v2.0  
> **Created**: 2025-10-20  
> **Applicable rustc version**: 1.90+  
> **Difficulty**: 🔴 Advanced to Expert

---

## 📋 Table of Contents

- [🔧 Rust Compiler Internals Complete Guide (2025 Edition)](#-rust-compiler-internals-complete-guide-2025-edition)
  - [📋 Table of Contents](#-table-of-contents)
  - [Introduction](#introduction)
  - [1. Compiler Overall Architecture](#1-compiler-overall-architecture)
    - [1.1 Macro Architecture Diagram](#11-macro-architecture-diagram)
    - [1.2 Core Data Structures](#12-core-data-structures)
    - [1.3 Compilation Timeline](#13-compilation-timeline)
  - [2. Frontend: From Source to HIR](#2-frontend-from-source-to-hir)
    - [2.1 Lexical Analysis (Lexing)](#21-lexical-analysis-lexing)
      - [Implementation Location](#implementation-location)
      - [Token Types](#token-types)
    - [2.2 Syntax Analysis (Parsing)](#22-syntax-analysis-parsing)
      - [2.2.1 Implementation Location](#221-implementation-location)
  - [5. MIR: Mid-level IR Explained](#5-mir-mid-level-ir-explained)
    - [5.1 MIR Overview](#51-mir-overview)
    - [5.2 MIR Structure](#52-mir-structure)
      - [MIR Components](#mir-components)
    - [5.3 MIR Examples](#53-mir-examples)
      - [Simple Function](#simple-function)
    - [5.4 Viewing MIR](#54-viewing-mir)
      - [Command-line Flags](#command-line-flags)
  - [10. Practice: Exploring Compiler Internals](#10-practice-exploring-compiler-internals)
    - [10.1 Viewing Compiler Output](#101-viewing-compiler-output)
    - [10.2 Viewing MIR](#102-viewing-mir)
    - [10.3 Viewing LLVM IR](#103-viewing-llvm-ir)
    - [10.4 Viewing Assembly](#104-viewing-assembly)
  - [Appendix](#appendix)
    - [A. Common rustc Flags](#a-common-rustc-flags)
    - [B. Compiler Components Index](#b-compiler-components-index)
    - [C. Learning Resources](#c-learning-resources)
    - [D. Exercises](#d-exercises)
      - [Beginner Exercises](#beginner-exercises)
      - [Intermediate Exercises](#intermediate-exercises)
      - [Advanced Exercises](#advanced-exercises)

---

## Introduction

The Rust compiler (rustc) is a highly complex engineering system responsible for transforming Rust source code into efficient machine code. This guide provides an in-depth analysis of rustc's internal mechanisms, helping you understand:

- 🏗️ **Compiler Architecture**: Multi-stage compilation pipeline
- 🔍 **Static Analysis**: Type checking, borrow checking
- 🎯 **Intermediate Representations**: AST → HIR → MIR → LLVM IR
- ⚡ **Optimization Strategies**: Dead code elimination, inlining, loop optimization
- 🔧 **Code Generation**: LLVM integration, ABI conventions

**Why Study Compiler Internals?**

1. 💡 **Understand Error Messages**: Know what the compiler is checking
2. 🚀 **Performance Optimization**: Understand how the compiler optimizes code
3. 🛠️ **Tool Development**: Develop linters, macros, IDE plugins
4. 📚 **Deep Rust Understanding**: Understand language features at the implementation level
5. 🔬 **Compiler Contribution**: Contribute to rustc

---

## 1. Compiler Overall Architecture

### 1.1 Macro Architecture Diagram

```text
┌────────────────────────────────────────────────────────────────┐
│                    Rust Compiler Architecture                   │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  Source Code (.rs)                                             │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Lexer         │  Token Stream                             │
│  │                │  ---→  [fn, main, (, ), {, ...}          │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Parser        │  Abstract Syntax Tree (AST)               │
│  │                │  ---→  Fn(main) { Block {...} }          │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Macro Expand  │  Expanded AST                             │
│  │                │  ---→  Expanded syntax tree               │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  HIR Lowering  │  High-level IR (HIR)                      │
│  │                │  ---→  Desugared representation           │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Type Check    │  Add type information                     │
│  │                │  ---→  Type-annotated HIR                │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Borrow Check  │  Verify ownership rules                   │
│  │                │  ---→  Safety verification               │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  MIR Build     │  Mid-level IR (MIR)                       │
│  │                │  ---→  CFG-based representation           │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  MIR Optimize  │  Optimized MIR                            │
│  │                │  ---→  Const prop, inlining, etc.        │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  Codegen       │  LLVM IR                                  │
│  │                │  ---→  LLVM intermediate representation   │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                           │
│  │  LLVM Backend  │  Machine Code                             │
│  │                │  ---→  Target platform executable         │
│  └────────────────┘                                           │
│      ↓                                                         │
│  Executable / Library                                          │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### 1.2 Core Data Structures

```rust
// rustc_driver/src/lib.rs (simplified)
pub struct Compiler {
    pub session: Session,              // Compilation session
    pub global_ctxt: GlobalCtxt,       // Global context
    pub queries: Queries,              // Query system
}

// Compilation session
pub struct Session {
    pub target: Target,                // Target platform
    pub opts: Options,                 // Compilation options
    pub parse_sess: ParseSess,         // Parse session
    pub source_map: SourceMap,         // Source file mapping
}

// Global context (contains all type information)
pub struct GlobalCtxt<'tcx> {
    pub hir: Hir<'tcx>,               // HIR data
    pub types: Types<'tcx>,           // Type information
    pub arena: Arena<'tcx>,           // Memory arena
}
```

### 1.3 Compilation Timeline

```text
Compilation time distribution (typical 1000-line project):
┌─────────────────────────────────────────────────────────────┐
│ Lex & Parse:    ████░░░░░░░░░░░░░░░░░░  10%  (~50ms)      │
│ Macro Expand:   ██░░░░░░░░░░░░░░░░░░░░   5%  (~25ms)      │
│ HIR Build:      ███░░░░░░░░░░░░░░░░░░░   8%  (~40ms)      │
│ Type Check:     ████████░░░░░░░░░░░░░░  20%  (~100ms)     │
│ Borrow Check:   ██████░░░░░░░░░░░░░░░░  15%  (~75ms)      │
│ MIR Optimize:   ████░░░░░░░░░░░░░░░░░░  10%  (~50ms)      │
│ LLVM Optimize:  ████████████░░░░░░░░░░  25%  (~125ms)     │
│ Code Gen:       ███░░░░░░░░░░░░░░░░░░░   7%  (~35ms)      │
└─────────────────────────────────────────────────────────────┘
Total: ~500ms (debug mode)
```

---

## 2. Frontend: From Source to HIR

### 2.1 Lexical Analysis (Lexing)

**Goal**: Convert character stream into token stream

#### Implementation Location

- `rustc_lexer` crate
- Hand-written DFA (Deterministic Finite Automaton)

#### Token Types

```rust
// rustc_lexer/src/lib.rs
pub enum TokenKind {
    // Literals
    Literal { kind: LiteralKind },
    
    // Identifiers and keywords
    Ident,
    
    // Operators and symbols
    Semi,           // ;
    Comma,          // ,
    Dot,            // .
    OpenParen,      // (
    CloseParen,     // )
    OpenBrace,      // {
    CloseBrace,     // }
    
    // Comments and whitespace
    LineComment,
    BlockComment { terminated: bool },
    Whitespace,
    
    // Lifetimes and labels
    Lifetime { starts_with_number: bool },
}
```

### 2.2 Syntax Analysis (Parsing)

**Goal**: Convert token stream into Abstract Syntax Tree (AST)

#### 2.2.1 Implementation Location

- `rustc_parse` crate
- Recursive descent parser

---

## 5. MIR: Mid-level IR Explained

### 5.1 MIR Overview

MIR (Mid-level Intermediate Representation) is the core intermediate representation of the Rust compiler, between HIR and LLVM IR.

**MIR Advantages**:

- 🎯 **Simple and Clear**: CFG-based (Control Flow Graph)
- 🔍 **Easy to Analyze**: Suitable for data flow analysis
- ⚡ **Optimization Friendly**: Supports multiple optimization passes
- 🛡️ **Type Safe**: Preserves type information

### 5.2 MIR Structure

#### MIR Components

```rust
// rustc_middle/src/mir/mod.rs (simplified)
pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub arg_count: usize,
    pub source_scopes: IndexVec<SourceScope, SourceScopeData>,
}

pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: Option<Terminator<'tcx>>,
}

pub enum Statement<'tcx> {
    Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
    SetDiscriminant { place: Place<'tcx>, variant_index: VariantIdx },
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

pub enum Terminator<'tcx> {
    Goto { target: BasicBlock },
    SwitchInt { discr: Operand<'tcx>, targets: SwitchTargets },
    Return,
    Unreachable,
    Drop { place: Place<'tcx>, target: BasicBlock, unwind: Option<BasicBlock> },
    Call { func: Operand<'tcx>, args: Vec<Operand<'tcx>>, destination: Place<'tcx>, target: Option<BasicBlock> },
}
```

### 5.3 MIR Examples

#### Simple Function

```rust
// Source code
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// MIR
fn add(_1: i32, _2: i32) -> i32 {
    let mut _0: i32;                     // return value
    
    bb0: {
        _0 = Add(move _1, move _2);     // _0 = _1 + _2
        return;                          // return _0
    }
}
```

### 5.4 Viewing MIR

#### Command-line Flags

```bash
# View MIR
rustc +nightly -Z unpretty=mir main.rs

# View specific function's MIR
rustc +nightly -Z dump-mir=all main.rs

# View MIR graphically (requires graphviz)
rustc +nightly -Z dump-mir-graphviz main.rs
```

---

## 10. Practice: Exploring Compiler Internals

### 10.1 Viewing Compiler Output

```bash
# View full compilation process
cargo build -v

# View timing statistics
cargo build -Z time-passes

# View detailed information for each stage
RUSTFLAGS="-Z time-passes" cargo build
```

### 10.2 Viewing MIR

```rust
// main.rs
fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
    println!("{}", factorial(5));
}
```

```bash
# View MIR
rustc +nightly -Z unpretty=mir main.rs > mir.txt
```

### 10.3 Viewing LLVM IR

```bash
# Generate LLVM IR
rustc --emit=llvm-ir main.rs -o main.ll

# View optimized LLVM IR
rustc --emit=llvm-ir -C opt-level=3 main.rs -o main_opt.ll
```

### 10.4 Viewing Assembly

```bash
# Generate assembly
rustc --emit=asm main.rs -o main.s

# Using cargo-asm
cargo install cargo-asm
cargo asm crate_name::function_name
```

---

## Appendix

### A. Common rustc Flags

```bash
# Compilation options
-C opt-level=N        # Optimization level (0, 1, 2, 3, s, z)
-C debuginfo=N        # Debug information (0, 1, 2)
-C lto                # Link-time optimization
-C codegen-units=N    # Code generation parallelism

# Output options
--emit=TYPE           # Output type (asm, llvm-ir, mir, link)
--crate-type=TYPE     # Crate type (bin, lib, dylib, staticlib)

# Debug options
-Z unpretty=TYPE      # Print internal representation
-Z dump-mir=PASS      # Dump MIR
-Z time-passes        # Show compilation time
-Z print-type-sizes   # Print type sizes
```

### B. Compiler Components Index

| Component | Crate | Functionality |
|-----------|-------|---------------|
| Lexical Analysis | `rustc_lexer` | Tokenization |
| Syntax Analysis | `rustc_parse` | AST construction |
| HIR | `rustc_hir` | High-level IR |
| Type Checking | `rustc_typeck` | Type inference |
| Borrow Checking | `rustc_borrowck` | Ownership verification |
| MIR | `rustc_mir_build` | MIR construction |
| Optimization | `rustc_mir_transform` | MIR optimization |
| Code Generation | `rustc_codegen_llvm` | LLVM backend |

### C. Learning Resources

- 📚 [Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/)
- 📚 [MIR Documentation](https://rust-lang.github.io/rustc-guide/mir/index.html)
- 📚 [LLVM Documentation](https://llvm.org/docs/)
- 📹 [RustConf Compiler Talks](https://www.youtube.com/c/RustVideos)

### D. Exercises

#### Beginner Exercises

1. Use `-Z unpretty=mir` to view MIR of simple functions
2. Compare LLVM IR differences between debug and release modes
3. View assembly output at different optimization levels

#### Intermediate Exercises

1. Analyze monomorphization process of generic functions
2. Observe inlining optimization effects on code
3. Use `cargo-expand` to view macro expansion results

#### Advanced Exercises

1. Analyze memory layout for custom data structures
2. Debug complex borrow checker errors
3. Analyze incremental compilation dependency graph

---

**Document Version**: v2.0  
**Last Updated**: 2025-10-20  
**Maintainer**: Rust Learning Community

🔧 **Deep dive into the compiler, master the soul of Rust!** ✨
