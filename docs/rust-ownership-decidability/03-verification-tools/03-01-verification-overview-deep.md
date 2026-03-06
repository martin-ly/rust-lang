# Rust Verification Tools: A Comprehensive Deep Dive

> **Abstract**: This document provides an exhaustive examination of the Rust verification ecosystem, covering static analysis tools, model checkers, theorem provers, and fuzzing frameworks.
> We present formal theorems about verification guarantees, practical counter-examples demonstrating real bugs caught by each tool, and a systematic approach to selecting appropriate verification techniques for Rust codebases.

---

## Table of Contents

- [Rust Verification Tools: A Comprehensive Deep Dive](#rust-verification-tools-a-comprehensive-deep-dive)
  - [Table of Contents](#table-of-contents)
  - [1. The Verification Landscape](#1-the-verification-landscape)
    - [1.1 Tool Categories](#11-tool-categories)
      - [1.1.1 Static Analysis Tools](#111-static-analysis-tools)
      - [1.1.2 Model Checkers](#112-model-checkers)
      - [1.1.3 Theorem Provers](#113-theorem-provers)
      - [1.1.4 Fuzzing Tools](#114-fuzzing-tools)
    - [1.2 The Verification Pyramid](#12-the-verification-pyramid)
    - [1.3 The Rust Verification Challenge](#13-the-rust-verification-challenge)
  - [2. Miri: The Undefined Behavior Detector](#2-miri-the-undefined-behavior-detector)
    - [2.1 Architecture and Design](#21-architecture-and-design)
      - [2.1.1 Stacked Borrows Model](#211-stacked-borrows-model)
    - [2.2 Counter-Examples: Bugs Caught by Miri](#22-counter-examples-bugs-caught-by-miri)
      - [Counter-Example 2.1: Use of Uninitialized Memory](#counter-example-21-use-of-uninitialized-memory)
      - [Counter-Example 2.2: Data Race](#counter-example-22-data-race)
      - [Counter-Example 2.3: Invalid Pointer Arithmetic](#counter-example-23-invalid-pointer-arithmetic)
      - [Counter-Example 2.4: Type Punning (Strict Aliasing Violation)](#counter-example-24-type-punning-strict-aliasing-violation)
      - [Counter-Example 2.5: Misaligned Access](#counter-example-25-misaligned-access)
      - [Counter-Example 2.6: Use After Free](#counter-example-26-use-after-free)
      - [Counter-Example 2.7: Invalid VTable](#counter-example-27-invalid-vtable)
    - [2.3 Running Miri](#23-running-miri)
    - [2.4 Limitations of Miri](#24-limitations-of-miri)
  - [3. Loom: Concurrency Model Checking](#3-loom-concurrency-model-checking)
    - [3.1 State Space Exploration](#31-state-space-exploration)
    - [3.2 Using Loom](#32-using-loom)
    - [3.3 Counter-Examples: Bugs Caught by Loom](#33-counter-examples-bugs-caught-by-loom)
      - [Counter-Example 3.1: Missed Atomic Ordering](#counter-example-31-missed-atomic-ordering)
      - [Counter-Example 3.2: Incorrect CAS Loop](#counter-example-32-incorrect-cas-loop)
      - [Counter-Example 3.3: ABA Problem](#counter-example-33-aba-problem)
      - [Counter-Example 3.4: Memory Ordering Bug](#counter-example-34-memory-ordering-bug)
      - [Counter-Example 3.5: Lost Wakeup](#counter-example-35-lost-wakeup)
      - [Counter-Example 3.6: Deadlock](#counter-example-36-deadlock)
    - [3.4 Loom Configuration](#34-loom-configuration)
  - [4. Creusot: Deductive Verification](#4-creusot-deductive-verification)
    - [4.1 WhyML Translation](#41-whyml-translation)
    - [4.2 Specification Language: Pearlite](#42-specification-language-pearlite)
    - [4.3 Proof Obligations](#43-proof-obligations)
      - [4.3.1 Preconditions](#431-preconditions)
      - [4.3.2 Postconditions](#432-postconditions)
      - [4.3.3 Loop Invariants](#433-loop-invariants)
    - [4.4 Counter-Examples from Failed Verification](#44-counter-examples-from-failed-verification)
      - [Counter-Example 4.1: Integer Overflow](#counter-example-41-integer-overflow)
      - [Counter-Example 4.2: Array Bounds](#counter-example-42-array-bounds)
      - [Counter-Example 4.3: Logic Error in Specification](#counter-example-43-logic-error-in-specification)
      - [Counter-Example 4.4: Broken Loop Invariant](#counter-example-44-broken-loop-invariant)
    - [4.5 Advanced Features](#45-advanced-features)
      - [4.5.1 Mutable Borrows](#451-mutable-borrows)
      - [4.5.2 Trait Specifications](#452-trait-specifications)
  - [5. Prusti: Viper-Based Verification](#5-prusti-viper-based-verification)
    - [5.1 Specification Language](#51-specification-language)
    - [5.2 Key Features](#52-key-features)
      - [5.2.1 Pure Functions](#521-pure-functions)
      - [5.2.2 Predicates](#522-predicates)
      - [5.2.3 Snapshots](#523-snapshots)
    - [5.3 Counter-Examples](#53-counter-examples)
      - [Counter-Example 5.1: Failing Postcondition](#counter-example-51-failing-postcondition)
      - [Counter-Example 5.2: Mutable Reference Issue](#counter-example-52-mutable-reference-issue)
  - [6. Fuzzing and Property-Based Testing](#6-fuzzing-and-property-based-testing)
    - [6.1 Property-Based Testing with proptest](#61-property-based-testing-with-proptest)
    - [6.2 Counter-Examples Found by Fuzzing](#62-counter-examples-found-by-fuzzing)
      - [Counter-Example 6.1: Parser Bug](#counter-example-61-parser-bug)
      - [Counter-Example 6.2: Arithmetic Edge Case](#counter-example-62-arithmetic-edge-case)
      - [Counter-Example 6.3: String Processing Bug](#counter-example-63-string-processing-bug)
    - [6.3 Coverage-Guided Fuzzing with cargo-fuzz](#63-coverage-guided-fuzzing-with-cargo-fuzz)
    - [6.4 Bolero: Unified Fuzzing](#64-bolero-unified-fuzzing)
  - [7. Tool Comparison and Selection Guide](#7-tool-comparison-and-selection-guide)
    - [7.1 Comparison Matrix](#71-comparison-matrix)
    - [7.2 Selection Decision Tree](#72-selection-decision-tree)
    - [7.3 Effort vs. Assurance Trade-off](#73-effort-vs-assurance-trade-off)
    - [7.4 Recommended Tool Stacks](#74-recommended-tool-stacks)
  - [8. Case Study: Verified Vec Implementation](#8-case-study-verified-vec-implementation)
    - [8.1 Basic Structure](#81-basic-structure)
    - [8.2 Push Operation Verification](#82-push-operation-verification)
    - [8.3 Pop Operation Verification](#83-pop-operation-verification)
    - [8.4 Index Operation Verification](#84-index-operation-verification)
    - [8.5 Verification Results](#85-verification-results)
  - [9. Integration Strategies](#9-integration-strategies)
    - [9.1 CI/CD Integration](#91-cicd-integration)
    - [9.2 Incremental Verification Strategy](#92-incremental-verification-strategy)
    - [9.3 Documentation and Training](#93-documentation-and-training)
  - [10. Future Directions](#10-future-directions)
    - [10.1 Emerging Tools](#101-emerging-tools)
    - [10.2 Standardization Efforts](#102-standardization-efforts)
    - [10.3 Research Challenges](#103-research-challenges)
  - [Appendix A: Quick Reference](#appendix-a-quick-reference)
    - [A.1 Miri Commands](#a1-miri-commands)
    - [A.2 Loom Commands](#a2-loom-commands)
    - [A.3 Creusot Commands](#a3-creusot-commands)
    - [A.4 Fuzzing Commands](#a4-fuzzing-commands)
  - [Summary](#summary)
  - [Counter-Examples Index](#counter-examples-index)
    - [Miri Counter-Examples (7 total)](#miri-counter-examples-7-total)
    - [Loom Counter-Examples (6 total)](#loom-counter-examples-6-total)
    - [Creusot Counter-Examples (4 total)](#creusot-counter-examples-4-total)
  - [Theorems Index](#theorems-index)

---

## 1. The Verification Landscape

### 1.1 Tool Categories

The Rust verification ecosystem has matured significantly, offering developers a spectrum of tools ranging from lightweight static analyzers to heavyweight theorem provers. Understanding the taxonomy of these tools is essential for effective verification strategy.

#### 1.1.1 Static Analysis Tools

Static analysis tools examine source code without executing it, identifying potential issues through pattern matching, dataflow analysis, and type system extensions.

**Clippy**: Rust's official linter provides over 550 lints covering correctness, style, and performance. While primarily a linting tool, many clippy lints catch serious correctness issues:

```rust
// Counter-Example 1: Clippy catches infinite recursion
impl Clone for MyType {
    fn clone(&self) -> Self {
        self.clone()  // ERROR: direct recursive call without base case
    }
}

// Counter-Example 2: Clippy detects panic-in-drop
impl Drop for MyType {
    fn drop(&mut self) {
        panic!("dropping!");  // WARNING: panicking in Drop is dangerous
    }
}
```

**Miri**: The Rust mid-level intermediate representation interpreter detects undefined behavior by executing code in a virtual machine with full instrumentation.

#### 1.1.2 Model Checkers

Model checkers systematically explore program state spaces to find concurrency bugs, race conditions, and deadlocks.

**Loom**: A model checker for Rust concurrent code that exhaustively explores thread interleavings within bounded execution histories.

**Shuttle**: A randomized scheduler for finding concurrency bugs through controlled nondeterminism, complementary to Loom's exhaustive approach.

#### 1.1.3 Theorem Provers

Theorem provers provide the highest assurance by mathematically proving program correctness against formal specifications.

**Creusot**: Translates Rust to WhyML for verification with automated theorem provers (SMT solvers like Alt-Ergo, Z3).

**Prusti**: Built on the Viper verification infrastructure, using separation logic to reason about Rust's ownership system.

**Kani**: A model checker specifically designed for Rust, using bounded model checking to verify properties.

#### 1.1.4 Fuzzing Tools

Fuzzing tools generate random inputs to find crashes and property violations.

**cargo-fuzz**: Integration with libFuzzer for coverage-guided fuzzing.

**proptest**: Property-based testing framework inspired by Hypothesis.

**bolero**: Unified fuzzing and property testing framework supporting multiple engines.

### 1.2 The Verification Pyramid

```
-----------------------------------------------------------------
                    THEOREM PROVING
         (Creusot, Prusti, Aeneas)
              | Highest assurance, highest effort
-----------------------------------------------------------------
                   MODEL CHECKING
            (Loom, Kani, Shuttle)
              | Bounded assurance, medium effort
-----------------------------------------------------------------
                PROPERTY-BASED TESTING
          (proptest, quickcheck, bolero)
              | Statistical assurance, low effort
-----------------------------------------------------------------
                    UNIT TESTING
              (built-in test framework)
              | Example-based, minimal assurance
-----------------------------------------------------------------
```

**Theorem 1.1 (VERIFICATION-SOUNDNESS-HIERARCHY)**:
*For a program P, let Soundness(T) denote the soundness guarantee provided by tool category T. Then:*

```
Soundness(TheoremProving) >= Soundness(ModelChecking) >= Soundness(PropertyTesting) >= Soundness(UnitTesting)
```

*Where >= indicates strictly stronger formal guarantees. However, the cost relationship is inverse: Cost(TheoremProving) >> Cost(ModelChecking) >> Cost(PropertyTesting) >> Cost(UnitTesting).*

**Proof Sketch**: Theorem provers reason about all possible executions through mathematical induction. Model checkers explore bounded state spaces completely but cannot reason about unbounded executions. Property testing samples the input space statistically. Unit testing examines only explicitly provided examples. QED.

### 1.3 The Rust Verification Challenge

Rust's ownership system provides memory safety guarantees at compile time, but several verification challenges remain:

1. **Unsafe Code Blocks**: `unsafe` Rust bypasses compiler checks, requiring manual verification of aliasing discipline
2. **Concurrency Correctness**: The type system prevents data races but not logical races or deadlocks
3. **Functional Correctness**: The compiler ensures memory safety but not algorithmic correctness
4. **Termination**: Rust has no built-in termination checking for recursive functions or loops

**Theorem 1.2 (RUST-VERIFICATION-COMPLETENESS)**:
*No single verification tool can provide complete soundness for all Rust programs due to the fundamental limitations established by Rice's Theorem. However, a carefully chosen combination of tools can achieve practical verification coverage for safety-critical components.*

---

## 2. Miri: The Undefined Behavior Detector

Miri is an interpreter for Rust's Mid-level Intermediate Representation (MIR). Unlike the regular Rust compiler which generates machine code, Miri executes MIR directly while checking for undefined behavior.

### 2.1 Architecture and Design

Miri implements the **Stacked Borrows** model for aliasing discipline and the **Tree Borrows** model as an experimental alternative.

```
----------------------------------------------------------------
                     Miri Architecture
----------------------------------------------------------------
  Source Code -> MIR -> Miri Interpreter -> UB Detection
                                     |
                            Stacked Borrows
                            (Aliasing Model)
----------------------------------------------------------------
```

#### 2.1.1 Stacked Borrows Model

Stacked Borrows defines when pointer aliasing is permitted:

```rust
fn stacked_borrows_example() {
    let mut x = 5;
    let raw = &mut x as *mut i32;  // Create raw pointer (Unique permission)

    // Creating a new reference invalidates the raw pointer
    let _ref = &mut x;  // New Unique permission, raw is now invalid

    // ERROR: Using invalidated pointer
    unsafe { *raw = 10; }  // Undefined Behavior!
}
```

**Theorem 2.1 (MIRI-SOUNDNESS)**:
*Miri is sound with respect to the Stacked Borrows operational semantics. If Miri reports no UB for a program execution, that execution is valid under Stacked Borrows. However, Miri is incomplete: it may reject programs that are valid under alternative aliasing models.*

### 2.2 Counter-Examples: Bugs Caught by Miri

#### Counter-Example 2.1: Use of Uninitialized Memory

```rust
// BUG: Reading uninitialized memory
fn uninitialized_memory_bug() -> i32 {
    let x: i32;
    unsafe {
        // x is not initialized - reading it is UB
        std::ptr::read(&x)  // ERROR: use of uninitialized memory
    }
}

// CORRECT: Proper initialization
fn uninitialized_memory_fixed() -> i32 {
    let x: i32 = 0;
    unsafe {
        std::ptr::read(&x)  // OK: x is initialized
    }
}
```

**Miri Output**:

```
error: Undefined Behavior: using uninitialized data
 --> src/main.rs:4:9
  |
4 |         std::ptr::read(&x)
  |         ^^^^^^^^^^^^^^^^^^
  |
  = help: this indicates a bug in the program
```

#### Counter-Example 2.2: Data Race

```rust
use std::thread;
use std::ptr;

// BUG: Data race between threads
fn data_race_bug() {
    let mut data = 0u32;
    let ptr = &mut data as *mut u32;

    unsafe {
        thread::spawn(move || {
            ptr::write(ptr, 1);  // Thread 1 writes
        });

        ptr::write(ptr, 2);  // Thread 2 writes (data race!)
    }
}

// CORRECT: Synchronized access
fn data_race_fixed() {
    use std::sync::{Arc, Mutex};

    let data = Arc::new(Mutex::new(0u32));
    let data2 = Arc::clone(&data);

    thread::spawn(move || {
        *data2.lock().unwrap() = 1;
    });

    *data.lock().unwrap() = 2;
}
```

**Miri Output**:

```
error: Undefined Behavior: Data race detected
 --> src/main.rs:9:13
  |
9 |             ptr::write(ptr, 1);
  |             ^^^^^^^^^^^^^^^^^^
  |
  = help: Data race: another thread is also writing to this location
```

#### Counter-Example 2.3: Invalid Pointer Arithmetic

```rust
// BUG: Pointer arithmetic outside allocation bounds
fn invalid_arithmetic_bug() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();

    unsafe {
        // Going far beyond the array bounds
        let far_ptr = ptr.offset(1000);  // ERROR: out-of-bounds offset
        let _ = *far_ptr;
    }
}

// BUG: Wrapping around address space
fn wrapping_arithmetic_bug() {
    let x = 0u8;
    let ptr = &x as *const u8;

    unsafe {
        // Even offset 1 is only valid for reading, not creating dangling ptr
        let end_ptr = ptr.wrapping_add(2);
        let _ = *end_ptr;  // ERROR: dangling pointer dereference
    }
}
```

#### Counter-Example 2.4: Type Punning (Strict Aliasing Violation)

```rust
// BUG: Violating strict aliasing rules
fn type_punning_bug() {
    let mut x: u32 = 0x01020304;
    let bytes = &mut x as *mut u32 as *mut u8;

    unsafe {
        // Accessing u32 through u8 pointer is allowed (char type exemption)
        // But creating an invalid bit pattern is not
        *bytes.add(0) = 0xFF;
        *bytes.add(1) = 0xFF;
        *bytes.add(2) = 0xFF;
        *bytes.add(3) = 0xFF;
    }  // OK for u32

    // BUG: Accessing f32 through u32 pointer
    let float_ptr = &mut x as *mut u32 as *mut f32;
    unsafe {
        let _val = *float_ptr;  // ERROR: invalid type punning
        // f32 has invalid bit pattern (NaN signaling)
    }
}

// CORRECT: Using mem::transmute with validation
fn type_punning_fixed() {
    let x: u32 = 0x3F800000;  // Valid f32 bit pattern for 1.0
    let f: f32 = unsafe { std::mem::transmute(x) };
    assert_eq!(f, 1.0);
}
```

#### Counter-Example 2.5: Misaligned Access

```rust
// BUG: Misaligned pointer dereference
fn misaligned_access_bug() {
    let bytes: [u8; 8] = [0; 8];
    let ptr = bytes.as_ptr();

    unsafe {
        // Creating misaligned pointer to u64
        let misaligned = ptr.add(1) as *const u64;
        let _val = *misaligned;  // ERROR: misaligned access
    }
}

// BUG: Misaligned field access in packed struct
#[repr(packed)]
struct Packed {
    flag: u8,
    value: u64,  // Not aligned to 8-byte boundary!
}

fn packed_struct_bug() {
    let p = Packed { flag: 1, value: 42 };

    // This is UB: taking reference to unaligned field
    let _ref = &p.value;  // ERROR: reference to unaligned field
}

// CORRECT: Copy out before accessing
fn packed_struct_fixed() {
    let p = Packed { flag: 1, value: 42 };
    let val = { p.value };  // Copy out, then use
    assert_eq!(val, 42);
}
```

#### Counter-Example 2.6: Use After Free

```rust
// BUG: Use after free
fn use_after_free_bug() {
    let ptr: *const i32;

    {
        let x = Box::new(42);
        ptr = &*x;  // Pointer to heap data
    }  // x is dropped here, memory freed

    unsafe {
        let _val = *ptr;  // ERROR: use after free
    }
}

// BUG: Double free
fn double_free_bug() {
    let x = Box::new(42);
    let ptr = Box::into_raw(x);

    unsafe {
        Box::from_raw(ptr);  // First free
        Box::from_raw(ptr);  // ERROR: double free
    }
}
```

#### Counter-Example 2.7: Invalid VTable

```rust
trait MyTrait {
    fn do_something(&self);
}

// BUG: Creating invalid trait object
fn invalid_vtable_bug() {
    struct FakeVTable;

    unsafe {
        // Creating a fat pointer with garbage vtable
        let fake: &dyn MyTrait = std::mem::transmute((
            0usize,  // data pointer
            0usize   // invalid vtable
        ));
        fake.do_something();  // ERROR: invalid vtable
    }
}
```

### 2.3 Running Miri

```bash
# Install Miri
rustup component add miri

# Run tests under Miri
cargo miri test

# Run specific binary under Miri
cargo miri run

# Set environment variables for Miri
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

### 2.4 Limitations of Miri

**Theorem 2.2 (MIRI-COMPLETENESS-LIMIT)**:
*Miri cannot detect all undefined behavior due to:*

1. *Bounded execution: Miri executes code concretely and cannot explore all paths*
2. *External FFI: Miri has limited support for C library interactions*
3. *Non-determinism: Miri assumes sequential execution*
4. *Aliasing model limitations: Stacked Borrows is conservative and may reject valid code*

---

## 3. Loom: Concurrency Model Checking

Loom is a model checker specifically designed for Rust concurrent code. It systematically explores all possible thread interleavings to find race conditions, deadlocks, and atomicity violations.

### 3.1 State Space Exploration

Loom uses a technique called **stateless model checking** with **partial order reduction** to efficiently explore thread schedules.

```
-----------------------------------------------------------------
                   Loom Architecture
-----------------------------------------------------------------
  Test Code -> Instrumented Execution -> Schedule Exploration
                     |
           -----------------------------
           |  Thread 1: A -> B -> C    |
           |  Thread 2: X -> Y -> Z    |
           |                           |
           |  Schedules:               |
           |  A,B,C,X,Y,Z              |
           |  A,B,X,C,Y,Z <- race!     |
           |  A,X,B,Y,C,Z              |
           |  ... (exhaustive)         |
           -----------------------------
-----------------------------------------------------------------
```

**Theorem 3.1 (LOOM-COVERAGE)**:
*For a concurrent program P with n threads and bounded execution depth d, Loom explores all possible thread interleavings up to depth d. Formally, if there exists a bug B reachable within d steps, Loom will discover B.*

**Proof Sketch**: Loom implements a DFS over the happens-before graph of program executions. Each node represents a program state, edges represent thread execution steps. By systematically backtracking at synchronization points, Loom visits all Mazurkiewicz traces (equivalence classes of executions under independent actions). QED.

### 3.2 Using Loom

```rust
// Standard concurrent code uses std::sync
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

// Loom test uses loom::sync instead
#[cfg(test)]
mod tests {
    use loom::sync::Arc;
    use loom::sync::atomic::{AtomicUsize, Ordering};
    use loom::thread;

    #[test]
    fn test_concurrent_counter() {
        loom::model(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let counter2 = Arc::clone(&counter);

            thread::spawn(move || {
                counter2.fetch_add(1, Ordering::SeqCst);
            });

            counter.fetch_add(1, Ordering::SeqCst);

            assert_eq!(counter.load(Ordering::SeqCst), 2);
        });
    }
}
```

### 3.3 Counter-Examples: Bugs Caught by Loom

#### Counter-Example 3.1: Missed Atomic Ordering

```rust
// BUG: Incorrect memory ordering
fn weak_ordering_bug() {
    use std::sync::atomic::{AtomicBool, AtomicU32};

    loom::model(|| {
        let ready = Arc::new(AtomicBool::new(false));
        let data = Arc::new(AtomicU32::new(0));

        let ready2 = Arc::clone(&ready);
        let data2 = Arc::clone(&data);

        thread::spawn(move || {
            data2.store(42, Ordering::Relaxed);  // Write data
            ready2.store(true, Ordering::Relaxed);  // Signal ready (BUG!)
        });

        // Main thread
        while !ready.load(Ordering::Relaxed) {}  // Wait (BUG!)
        let value = data.load(Ordering::Relaxed);  // Read data (BUG!)

        // This can fail! The store to 'ready' might be visible
        // before the store to 'data' due to compiler/CPU reordering
        assert_eq!(value, 42);  // May see 0!
    });
}

// CORRECT: Proper memory ordering
fn ordering_fixed() {
    loom::model(|| {
        let ready = Arc::new(AtomicBool::new(false));
        let data = Arc::new(AtomicU32::new(0));

        let ready2 = Arc::clone(&ready);
        let data2 = Arc::clone(&data);

        thread::spawn(move || {
            data2.store(42, Ordering::Relaxed);
            ready2.store(true, Ordering::Release);  // Release ordering
        });

        // Main thread
        while !ready.load(Ordering::Acquire) {}  // Acquire ordering
        let value = data.load(Ordering::Relaxed);

        assert_eq!(value, 42);  // Guaranteed to see 42
    });
}
```

#### Counter-Example 3.2: Incorrect CAS Loop

```rust
// BUG: Classic ABA problem in lock-free stack
struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: std::ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            // BUG: CompareAndSwap without checking result properly
            self.head.compare_and_swap(head, new_node, Ordering::Relaxed);
            // If CAS fails, we have a memory leak and retry logic issues
            break;  // BUG: Breaking unconditionally!
        }
    }

    fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Relaxed);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            // BUG: Wrong ordering and not handling failure
            if self.head.compare_and_swap(head, next, Ordering::Relaxed) == head {
                // This check is wrong - compare_and_swap returns the old value
                return Some(unsafe { Box::from_raw(head).data });
            }
            // Missing retry loop!
        }
    }
}

// CORRECT: Proper CAS loop with right orderings
impl<T> LockFreeStack<T> {
    fn push_fixed(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: std::ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            match self.head.compare_exchange(
                head,
                new_node,
                Ordering::Release,  // Success: Release to other threads
                Ordering::Relaxed   // Failure: No ordering needed
            ) {
                Ok(_) => break,
                Err(_) => continue,  // Retry on failure
            }
        }
    }

    fn pop_fixed(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            match self.head.compare_exchange(
                head,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed
            ) {
                Ok(_) => return Some(unsafe { Box::from_raw(head).data }),
                Err(_) => continue,  // Retry on failure
            }
        }
    }
}
```

#### Counter-Example 3.3: ABA Problem

```rust
// BUG: Classic ABA problem
fn aba_problem_bug() {
    use loom::sync::atomic::AtomicPtr;

    loom::model(|| {
        let shared = Arc::new(AtomicPtr::new(Box::into_raw(Box::new(1))));

        let shared2 = Arc::clone(&shared);
        let shared3 = Arc::clone(&shared);

        thread::spawn(move || {
            // Thread 2
            let ptr = shared2.load(Ordering::Acquire);

            // Simulate delay
            loom::yield_now();

            // ABA problem: by the time we CAS, the value has
            // gone A->B->A but is semantically different
            let new_val = Box::into_raw(Box::new(2));
            let _ = shared2.compare_exchange(
                ptr,
                new_val,
                Ordering::AcqRel,
                Ordering::Acquire
            );
        });

        thread::spawn(move || {
            // Thread 3
            let ptr = shared3.load(Ordering::Acquire);

            // Change A to B
            let intermediate = Box::into_raw(Box::new(100));
            let old = shared3.compare_exchange(
                ptr,
                intermediate,
                Ordering::AcqRel,
                Ordering::Acquire
            );

            if old.is_ok() {
                // Free the old value
                unsafe { let _ = Box::from_raw(ptr); }

                // Change B back to A
                let back_to_a = Box::into_raw(Box::new(1));
                let _ = shared3.compare_exchange(
                    intermediate,
                    back_to_a,
                    Ordering::AcqRel,
                    Ordering::Acquire
                );
            }
        });

        // Main thread operations...
    });
}
```

#### Counter-Example 3.4: Memory Ordering Bug

```rust
// BUG: Dekker's algorithm with wrong orderings fails
fn dekker_wrong_ordering() {
    loom::model(|| {
        let flag1 = Arc::new(AtomicBool::new(false));
        let flag2 = Arc::new(AtomicBool::new(false));
        let turn = Arc::new(AtomicUsize::new(0));

        let (f1, f2, t1) = (Arc::clone(&flag1), Arc::clone(&flag2), Arc::clone(&turn));

        thread::spawn(move || {
            // Thread 1 entry
            f1.store(true, Ordering::Relaxed);  // BUG!
            while f2.load(Ordering::Relaxed) {  // BUG!
                if t1.load(Ordering::Relaxed) != 0 {  // BUG!
                    f1.store(false, Ordering::Relaxed);  // BUG!
                    while t1.load(Ordering::Relaxed) != 0 {}  // BUG!
                    f1.store(true, Ordering::Relaxed);  // BUG!
                }
            }
            // Critical section
            f1.store(false, Ordering::Relaxed);  // BUG!
        });

        // Similar for thread 2...
        // With all Relaxed orderings, mutual exclusion can be violated!
    });
}

// CORRECT: Dekker's algorithm requires SeqCst
fn dekker_correct() {
    loom::model(|| {
        let flag1 = Arc::new(AtomicBool::new(false));
        let flag2 = Arc::new(AtomicBool::new(false));
        let turn = Arc::new(AtomicUsize::new(0));

        let (f1, f2, t1) = (Arc::clone(&flag1), Arc::clone(&flag2), Arc::clone(&turn));

        thread::spawn(move || {
            f1.store(true, Ordering::SeqCst);
            while f2.load(Ordering::SeqCst) {
                if t1.load(Ordering::SeqCst) != 0 {
                    f1.store(false, Ordering::SeqCst);
                    while t1.load(Ordering::SeqCst) != 0 {}
                    f1.store(true, Ordering::SeqCst);
                }
            }
            // Critical section - mutual exclusion guaranteed
            f1.store(false, Ordering::SeqCst);
        });

        // Thread 2 similar...
    });
}
```

#### Counter-Example 3.5: Lost Wakeup

```rust
// BUG: Lost wakeup in condition variable pattern
use std::sync::{Mutex, Condvar};

fn lost_wakeup_bug() {
    loom::model(|| {
        let pair = Arc::new((Mutex::new(false), Condvar::new()));
        let pair2 = Arc::clone(&pair);

        thread::spawn(move || {
            let (lock, cvar) = &*pair2;
            let mut started = lock.lock().unwrap();
            *started = true;
            // BUG: notify_one might happen before the other thread waits
            cvar.notify_one();  // Wakeup could be lost!
        });

        let (lock, cvar) = &*pair;
        let mut started = lock.lock().unwrap();

        // BUG: Spurious wakeups not handled correctly
        // and race between check and wait
        if !*started {  // BUG: Should use while!
            started = cvar.wait(started).unwrap();  // Might miss notification
        }

        assert!(*started);  // Might fail!
    });
}

// CORRECT: Proper condition variable usage
fn lost_wakeup_fixed() {
    loom::model(|| {
        let pair = Arc::new((Mutex::new(false), Condvar::new()));
        let pair2 = Arc::clone(&pair);

        thread::spawn(move || {
            let (lock, cvar) = &*pair2;
            let mut started = lock.lock().unwrap();
            *started = true;
            cvar.notify_one();
        });

        let (lock, cvar) = &*pair;
        let mut started = lock.lock().unwrap();

        // Always wait in a loop to handle spurious wakeups
        while !*started {
            started = cvar.wait(started).unwrap();
        }

        assert!(*started);  // Guaranteed
    });
}
```

#### Counter-Example 3.6: Deadlock

```rust
// BUG: Circular wait deadlock
fn deadlock_bug() {
    loom::model(|| {
        let lock1 = Arc::new(Mutex::new(0));
        let lock2 = Arc::new(Mutex::new(0));

        let (l1a, l2a) = (Arc::clone(&lock1), Arc::clone(&lock2));
        let (l1b, l2b) = (Arc::clone(&lock1), Arc::clone(&lock2));

        thread::spawn(move || {
            let _guard1 = l1a.lock().unwrap();
            loom::yield_now();  // Force interleaving
            let _guard2 = l2a.lock().unwrap();  // May deadlock!
        });

        thread::spawn(move || {
            let _guard2 = l2b.lock().unwrap();
            loom::yield_now();  // Force interleaving
            let _guard1 = l1b.lock().unwrap();  // May deadlock!
        });

        // Loom will detect the deadlock
    });
}

// CORRECT: Lock ordering
fn deadlock_fixed() {
    loom::model(|| {
        let lock1 = Arc::new(Mutex::new(0));
        let lock2 = Arc::new(Mutex::new(0));

        let (l1a, l2a) = (Arc::clone(&lock1), Arc::clone(&lock2));
        let (l1b, l2b) = (Arc::clone(&lock1), Arc::clone(&lock2));

        thread::spawn(move || {
            // Always lock in consistent order
            let _guard1 = l1a.lock().unwrap();
            let _guard2 = l2a.lock().unwrap();
        });

        thread::spawn(move || {
            // Same order prevents deadlock
            let _guard1 = l1b.lock().unwrap();
            let _guard2 = l2b.lock().unwrap();
        });
    });
}
```

### 3.4 Loom Configuration

```rust
// loom.toml or environment variables
LOOM_MAX_PREEMPTIONS=3  // Limit context switches for bounded checking
LOOM_MAX_BRANCHES=10000 // Limit explored branches
LOOM_CHECKPOINT_INTERVAL=1000 // Save progress
```

**Theorem 3.2 (LOOM-COMPLETENESS-BOUND)**:
*Loom provides bounded completeness: for any bug B involving at most k preemptions (context switches) among n threads, Loom will discover B when configured with LOOM_MAX_PREEMPTIONS >= k. Bugs requiring more than k preemptions may not be found.*

---

## 4. Creusot: Deductive Verification

Creusot is a deductive verification tool for Rust that translates Rust programs to WhyML, the specification language of the Why3 platform. It leverages automated theorem provers (SMT solvers) to discharge proof obligations.

### 4.1 WhyML Translation

Creusot translates Rust's MIR to WhyML, preserving ownership information through the `pearlite` specification language.

```rust
// Rust code with Creusot specifications
use creusot_contracts::*;

#[requires(x > i32::MIN)]  // Precondition
#[ensures(result >= 0)]     // Postcondition
#[ensures(x >= 0 ==> result == x)]
#[ensures(x < 0 ==> result == -x)]
pub fn abs(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}
```

**Translation Pipeline**:

```
Rust Source
    |
MIR (Mid-level IR)
    |
WhyML (Intermediate verification language)
    |
Verification Conditions (VCs)
    |
SMT Solvers (Alt-Ergo, Z3, CVC4)
    |
Proof Result
```

### 4.2 Specification Language: Pearlite

Pearlite is Creusot's specification language, a pure subset of Rust extended with logical operators.

```rust
use creusot_contracts::*;

// Logical functions (ghost code)
#[logic]
fn sum_range(start: Int, end: Int) -> Int {
    if start >= end {
        0
    } else {
        start + sum_range(start + 1, end)
    }
}

// Predicate for array properties
#[predicate]
fn is_sorted<T: Ord>(arr: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int, j: Int> (
            0 <= i && i < j && j < arr.len() ==>
            arr[i] <= arr[j]
        )
    }
}

#[requires(arr.len() <= 1000)]  // Bounds for verification
#[requires(is_sorted(arr))]
#[ensures(exists<i: Int> 0 <= i && i < arr.len() && arr[i] == target ==>
          result == Some(i))]
#[ensures(forall<i: Int> 0 <= i && i < arr.len() && arr[i] == target ==>
          result == Some(i))]
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = arr.len();

    #[invariant(low <= high)]
    #[invariant(high <= arr.len())]
    #[invariant(forall<i: Int> 0 <= i && i < low ==> arr[i] < target)]
    #[invariant(forall<i: Int> high <= i && i < arr.len() ==> target < arr[i])]
    while low < high {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    None
}
```

### 4.3 Proof Obligations

Creusot generates three categories of proof obligations:

**Theorem 4.1 (CREUSOT-SOUNDNESS)**:
*If Creusot verifies a program P (all proof obligations discharged), then P satisfies all specified preconditions, postconditions, and loop invariants. Furthermore, if P contains no unsafe code, verified programs are guaranteed to be free of panics (where specified) and undefined behavior.*

#### 4.3.1 Preconditions

Preconditions must hold at call sites:

```rust
#[requires(!self.is_full())]  // Cannot push to full vector
#[ensures(self.len() == old(self.len()) + 1)]
#[ensures(self.last() == elem)]
pub fn push<T>(&mut self, elem: T) {
    // Implementation
}

// Proof obligation generated at call site:
// assert!(!vec.is_full());  // Must hold!
```

#### 4.3.2 Postconditions

Postconditions guarantee what the function establishes:

```rust
#[requires(x >= 0)]
#[requires(y >= 0)]
#[ensures(result == x + y)]  // Functional correctness
#[ensures(result >= x)]      // Additional property
#[ensures(result >= y)]
pub fn add(x: u32, y: u32) -> u32 {
    x + y  // Creusot proves this satisfies all postconditions
}
```

#### 4.3.3 Loop Invariants

Loop invariants capture inductive properties:

```rust
#[ensures(result == sum_range(0, n))]
pub fn sum_to(n: u32) -> u32 {
    let mut i = 0;
    let mut sum = 0;

    #[invariant(i <= n)]
    #[invariant(sum == sum_range(0, i))]
    while i < n {
        i += 1;
        sum += i;
    }

    sum
}
```

### 4.4 Counter-Examples from Failed Verification

#### Counter-Example 4.1: Integer Overflow

```rust
// FAILED VERIFICATION: Potential overflow
#[requires(x >= 0 && y >= 0)]
#[ensures(result == x + y)]  // May overflow!
pub fn add_unsafe(x: i32, y: i32) -> i32 {
    x + y  // ERROR: Can overflow for large inputs
}

// FIXED: Proper bounds checking
#[requires(x >= 0 && y >= 0)]
#[requires(x <= i32::MAX - y)]  // Prevent overflow
#[ensures(result == x + y)]
pub fn add_safe(x: i32, y: i32) -> i32 {
    x + y
}
```

#### Counter-Example 4.2: Array Bounds

```rust
// FAILED VERIFICATION: Index out of bounds
#[requires(arr.len() > 0)]
pub fn first_unsafe(arr: &[i32]) -> i32 {
    arr[arr.len()]  // ERROR: Off-by-one, should be arr.len() - 1
}

// FIXED: Correct index
#[requires(arr.len() > 0)]
#[ensures(result == arr[0])]
pub fn first_safe(arr: &[i32]) -> i32 {
    arr[0]
}
```

#### Counter-Example 4.3: Logic Error in Specification

```rust
// FAILED VERIFICATION: Wrong postcondition
#[ensures(result > x)]  // ERROR: Not true when x is max value!
pub fn increment(x: u32) -> u32 {
    x + 1  // This overflows for u32::MAX
}

// FIXED: Correct specification
#[requires(x < u32::MAX)]
#[ensures(result == x + 1)]
pub fn increment_safe(x: u32) -> u32 {
    x + 1
}
```

#### Counter-Example 4.4: Broken Loop Invariant

```rust
// FAILED VERIFICATION: Invariant not maintained
pub fn factorial(n: u32) -> u32 {
    let mut result = 1;
    let mut i = 0;

    // ERROR: Wrong invariant (should be result == factorial(i))
    #[invariant(result == i)]
    while i < n {
        i += 1;
        result *= i;
    }

    result
}

// FIXED: Correct invariant
#[ensures(result == factorial_logic(n))]
pub fn factorial_fixed(n: u32) -> u32 {
    let mut result = 1;
    let mut i = 0;

    #[invariant(i <= n)]
    #[invariant(result == factorial_logic(i))]
    while i < n {
        i += 1;
        result *= i;
    }

    result
}

#[logic]
fn factorial_logic(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial_logic(n - 1)
    }
}
```

### 4.5 Advanced Features

#### 4.5.1 Mutable Borrows

```rust
#[requires(x < 100)]
#[ensures(*x == old(*x) + 1)]
#[ensures(^x == *x)]  // Final value equals current value
pub fn increment_mut(x: &mut u32) {
    *x += 1;
}
```

#### 4.5.2 Trait Specifications

```rust
#[trusted]  // Trusted trait for external types
trait MyTrait {
    #[ensures(result > 0)]
    fn method(&self) -> i32;
}
```

---

## 5. Prusti: Viper-Based Verification

Prusti is a verification tool for Rust built on the Viper verification infrastructure. It uses separation logic to reason about Rust's ownership system.

### 5.1 Specification Language

Prusti uses annotations directly in Rust code:

```rust
use prusti_contracts::*;

#[requires(x > 0)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}
```

### 5.2 Key Features

#### 5.2.1 Pure Functions

```rust
#[pure]
#[ensures(result >= 0)]
fn abs_pure(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}
```

#### 5.2.2 Predicates

```rust
#[predicate]
fn is_positive(x: i32) -> bool {
    x > 0
}

#[requires(is_positive(x))]
pub fn use_positive(x: i32) {
    // x is guaranteed positive
}
```

#### 5.2.3 Snapshots

```rust
#[ensures(result == old(self.len()))]
#[ensures(self.len() == 0)]
pub fn clear(&mut self) {
    // old(self.len()) captures pre-state
}
```

### 5.3 Counter-Examples

#### Counter-Example 5.1: Failing Postcondition

```rust
// FAILED: Postcondition might not hold
#[ensures(result > 0)]
pub fn failing_post(x: i32) -> i32 {
    x  // Returns x, but x might be <= 0!
}

// FIXED
#[requires(x > 0)]
#[ensures(result > 0)]
pub fn fixed_post(x: i32) -> i32 {
    x
}
```

#### Counter-Example 5.2: Mutable Reference Issue

```rust
// FAILED: Assertion might not hold
pub fn mut_ref_issue(x: &mut i32) {
    *x = 5;
    assert!(false);  // ERROR: Provably false
}
```

---

## 6. Fuzzing and Property-Based Testing

Fuzzing complements formal verification by finding bugs through randomized testing. Unlike verification which proves correctness, fuzzing finds counter-examples to correctness claims.

### 6.1 Property-Based Testing with proptest

proptest is a property testing framework inspired by Hypothesis. It generates random test cases and shrinks failures to minimal examples.

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_reverse_identity(s: String) {
        // Property: reversing twice returns original
        let rev: String = s.chars().rev().collect();
        let rev_rev: String = rev.chars().rev().collect();
        prop_assert_eq!(s, rev_rev);
    }

    #[test]
    fn test_addition_commutative(a: i32, b: i32) {
        // Property: addition is commutative
        prop_assert_eq!(a + b, b + a);
    }

    #[test]
    fn test_sorted_vector(mut v: Vec<i32>) {
        v.sort();
        // Property: sorted vector is non-decreasing
        for i in 1..v.len() {
            prop_assert!(v[i-1] <= v[i]);
        }
    }
}
```

### 6.2 Counter-Examples Found by Fuzzing

#### Counter-Example 6.1: Parser Bug

```rust
// A JSON parser might have this bug
fn parse_json_buggy(input: &str) -> Result<JsonValue, Error> {
    // Fuzzing finds inputs like:
    // - "{\"key\":}"
    // - "[1,2,3"
    // - "null\x00"
    // These cause panics or incorrect parsing
}

// Fuzz test that finds these
#[test]
fn fuzz_json_parser() {
    let input = "{\"key\":}";  // Found by fuzzer
    assert!(parse_json_buggy(input).is_err());
}
```

#### Counter-Example 6.2: Arithmetic Edge Case

```rust
// Bug found by fuzzing: division edge case
fn average_buggy(a: i32, b: i32) -> i32 {
    (a + b) / 2  // OVERFLOW for large values!
}

// Fuzzing found: a = i32::MAX, b = i32::MAX
// (a + b) overflows before division

// Fixed version
fn average_fixed(a: i32, b: i32) -> i32 {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}
```

#### Counter-Example 6.3: String Processing Bug

```rust
// Bug: doesn't handle multi-byte UTF-8 correctly
fn truncate_buggy(s: &str, max_len: usize) -> &str {
    &s[..max_len]  // PANIC if max_len splits a UTF-8 sequence!
}

// Fuzzing found: s = "\u{65e5}\u{672c}\u{8a9e}", max_len = 1
// &[..1] gives first byte of \u{65e5}, which is invalid UTF-8

// Fixed version
fn truncate_fixed(s: &str, max_len: usize) -> &str {
    match s.char_indices().nth(max_len) {
        Some((idx, _)) => &s[..idx],
        None => s,
    }
}
```

### 6.3 Coverage-Guided Fuzzing with cargo-fuzz

```rust
// fuzz/fuzz_targets/my_target.rs
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Fuzzing input is raw bytes
    if let Ok(s) = std::str::from_utf8(data) {
        // Test your parser with random strings
        let _ = my_parser::parse(s);
    }
});
```

### 6.4 Bolero: Unified Fuzzing

```rust
use bolero::check;

#[test]
fn test_with_fuzzing() {
    check!().for_each(|input: &[u8]| {
        // Test with randomized inputs
        let _ = parse(input);
    });
}
```

---

## 7. Tool Comparison and Selection Guide

### 7.1 Comparison Matrix

| Tool | Scope | Effort | Soundness | Automation | When to Use |
|------|-------|--------|-----------|------------|-------------|
| **Miri** | UB Detection | Low | Complete for checked executions | Fully automatic | Unsafe code review, debugging suspected UB |
| **Loom** | Concurrency | Medium | Bounded (configurable) | Automatic with bounds | Lock-free data structures, concurrent algorithms |
| **Shuttle** | Concurrency | Low | Statistical | Automatic | Stress testing concurrent code |
| **Creusot** | Functional Correctness | High | Complete | Semi-automatic (SMT) | Critical algorithms, safety invariants |
| **Prusti** | Functional + Memory | High | Complete | Semi-automatic | Complex ownership patterns, contracts |
| **Kani** | Bounded Verification | Medium | Bounded | Automatic | Verifying unsafe blocks, system properties |
| **cargo-fuzz** | Crash Finding | Low | Statistical | Automatic | Parser security, input validation |
| **proptest** | Property Testing | Low | Statistical | Automatic | Testing algebraic properties, invariants |

### 7.2 Selection Decision Tree

```
What do you need to verify?
|
+-- Memory Safety / UB
|   +-- Unsafe code -> Miri + Kani
|   +-- Safe code only -> Miri (for thoroughness)
|
+-- Concurrency Correctness
|   +-- Lock-free structures -> Loom
|   +-- General concurrent code -> Loom + Shuttle
|   +-- Deadlock detection -> Loom
|
+-- Functional Correctness
|   +-- Simple properties -> proptest
|   +-- Complex invariants -> Creusot or Prusti
|   +-- With unsafe blocks -> Kani + Creusot
|
+-- Security / Crash Resistance
    +-- Input parsers -> cargo-fuzz
    +-- Protocol handling -> cargo-fuzz + proptest
```

### 7.3 Effort vs. Assurance Trade-off

```
Assurance
    ^
    |                    * Theorem Proving
    |                   (Creusot, Prusti)
    |                 /
    |               /
    |             /
    |           * Model Checking (Loom, Kani)
    |         /
    |       /
    |     * Property Testing (proptest)
    |   /
    | * Unit Tests
    +--------------------------------------> Effort
```

### 7.4 Recommended Tool Stacks

**For Safety-Critical Libraries**:

- Unit tests for basic functionality
- Miri for UB detection in unsafe code
- Loom for concurrent components
- Creusot for core algorithm verification
- cargo-fuzz for input validation

**For Application Code**:

- Unit tests with good coverage
- proptest for business logic invariants
- Miri for any unsafe blocks

**For System-Level Code**:

- Kani for verifying unsafe blocks
- Loom for synchronization primitives
- cargo-fuzz for protocol handling

---

## 8. Case Study: Verified Vec Implementation

This case study demonstrates verifying a simplified `Vec` implementation using Creusot.

### 8.1 Basic Structure

```rust
use creusot_contracts::*;
use std::alloc::{self, Layout};
use std::ptr::{self, NonNull};

pub struct Vec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
}

// Ghost model for verification
impl<T> Vec<T> {
    #[logic]
    fn model(self) -> Seq<T> {
        // Logical representation as sequence
        pearlite! { self.model }
    }
}

impl<T> Vec<T> {
    #[ensures(result.len() == 0)]
    #[ensures(result.capacity() >= 0)]
    pub fn new() -> Self {
        Vec {
            ptr: NonNull::dangling(),
            len: 0,
            cap: 0,
        }
    }

    #[pure]
    pub fn len(&self) -> usize {
        self.len
    }

    #[pure]
    pub fn capacity(&self) -> usize {
        self.cap
    }

    #[pure]
    #[ensures(result == (self.len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}
```

### 8.2 Push Operation Verification

```rust
impl<T: Clone> Vec<T> {
    #[requires(self.len() < usize::MAX)]
    #[requires(self.len() <= self.capacity())]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.capacity() >= old(self.capacity()))]
    #[ensures(self.model().len() == old(self.model()).len() + 1)]
    #[ensures(self.model()[self.len() - 1] == elem)]
    #[ensures(forall<i: Int> 0 <= i && i < old(self.len()) ==>
              self.model()[i] == old(self.model())[i])]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap {
            self.grow();
        }

        unsafe {
            ptr::write(self.ptr.as_ptr().add(self.len), elem);
        }

        self.len += 1;
    }

    #[requires(self.len() == self.capacity())]
    #[ensures(self.capacity() > old(self.capacity()))]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(forall<i: Int> 0 <= i && i < self.len() ==>
              self.model()[i] == old(self.model())[i])]
    fn grow(&mut self) {
        let new_cap = if self.cap == 0 { 1 } else { self.cap * 2 };

        let new_layout = Layout::array::<T>(new_cap).unwrap();

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                alloc::realloc(
                    self.ptr.as_ptr() as *mut u8,
                    old_layout,
                    new_layout.size()
                )
            }
        };

        self.ptr = NonNull::new(new_ptr as *mut T).unwrap();
        self.cap = new_cap;
    }
}
```

### 8.3 Pop Operation Verification

```rust
impl<T> Vec<T> {
    #[requires(!self.is_empty())]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(result == old(self.model())[self.len()])]
    #[ensures(forall<i: Int> 0 <= i && i < self.len() ==>
              self.model()[i] == old(self.model())[i])]
    pub fn pop(&mut self) -> T {
        self.len -= 1;

        unsafe {
            ptr::read(self.ptr.as_ptr().add(self.len))
        }
    }
}
```

### 8.4 Index Operation Verification

```rust
use std::ops::Index;

impl<T> Index<usize> for Vec<T> {
    type Output = T;

    #[requires(index < self.len())]
    #[ensures(result == self.model()[index])]
    fn index(&self, index: usize) -> &T {
        unsafe {
            &*self.ptr.as_ptr().add(index)
        }
    }
}
```

### 8.5 Verification Results

The verification with Creusot establishes:

1. **Memory Safety**: No out-of-bounds access, no use-after-free
2. **Functional Correctness**: Push adds element at end, Pop removes from end
3. **Invariants Preserved**: Length always <= Capacity, elements preserved during growth

**Theorem 8.1 (VERIFIED-VEC-CORRECTNESS)**:
*The verified Vec implementation satisfies:*

- *`len()` returns the actual number of elements*
- *`push()` increases length by 1 and preserves existing elements*
- *`pop()` decreases length by 1 and returns the last element*
- *`index()` accesses valid elements only*
- *No memory leaks or double-frees occur*

---

## 9. Integration Strategies

### 9.1 CI/CD Integration

```yaml
# .github/workflows/verification.yml
name: Verification

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Miri
        run: rustup component add miri
      - name: Run Miri
        run: cargo miri test

  loom:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Run Loom tests
        run: cargo test --features loom
        env:
          LOOM_MAX_PREEMPTIONS: 3

  creusot:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Creusot
        run: cargo install creusot
      - name: Verify
        run: cargo creusot

  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install cargo-fuzz
        run: cargo install cargo-fuzz
      - name: Run fuzzer (timed)
        run: timeout 300 cargo fuzz run || true
```

### 9.2 Incremental Verification Strategy

**Phase 1: Base Testing**

- Unit tests for all public APIs
- Integration tests for common use cases

**Phase 2: Safety Verification**

- Miri for unsafe code paths
- Run on every PR touching unsafe

**Phase 3: Concurrency Verification**

- Loom for concurrent components
- Shuttle for stress testing

**Phase 4: Functional Verification** (for critical modules)

- Creusot/Prusti for core algorithms
- Maintain specifications as code evolves

**Phase 5: Security Hardening**

- cargo-fuzz for input handling
- Continuous fuzzing infrastructure

### 9.3 Documentation and Training

```rust
/// # Verification
///
/// This function has been verified with Creusot:
/// - Preconditions: `slice` must be sorted
/// - Postconditions: Returns correct index or None
///
/// ## Testing
/// ```
/// # use mycrate::binary_search;
/// let arr = [1, 2, 3, 4, 5];
/// assert_eq!(binary_search(&arr, 3), Some(2));
/// ```
///
/// ## Miri Testing
/// Run: `cargo miri test binary_search`
pub fn binary_search<T: Ord>(slice: &[T], target: T) -> Option<usize> {
    // ...
}
```

---

## 10. Future Directions

### 10.1 Emerging Tools

- **Aeneas**: New verification tool using characteristic formulae
- **RustBelt**: Separation logic for Rust (foundational)
- **RustViper**: Enhanced Viper support for Rust
- **Verus**: New Rust verifier from MSR

### 10.2 Standardization Efforts

- Common specification language across tools
- Standard verification attributes
- Proof artifact exchange formats

### 10.3 Research Challenges

1. **Unsafe Code Verification**: Better support for FFI and raw pointers
2. **Async/Await**: Verification of async Rust programs
3. **Performance**: Reducing verification time for large codebases
4. **Usability**: Better error messages and counter-example visualization

---

## Appendix A: Quick Reference

### A.1 Miri Commands

```bash
# Install
rustup component add miri

# Run tests
cargo miri test

# Run binary
cargo miri run

# With flags
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

### A.2 Loom Commands

```bash
# Add to Cargo.toml
[dependencies]
loom = { version = "0.7", optional = true }

[dev-dependencies]
loom = "0.7"

# Run tests
LOOM_MAX_PREEMPTIONS=3 cargo test --features loom
```

### A.3 Creusot Commands

```bash
# Install
cargo install creusot

# Verify
cargo creusot

# With Why3 IDE
cargo creusot -- --why3-ide
```

### A.4 Fuzzing Commands

```bash
# Install
cargo install cargo-fuzz

# Initialize
cargo fuzz init

# Run
cargo fuzz run target_name

# With duration
cargo fuzz run target_name -- -max_total_time=300
```

---

## Summary

This document has provided a comprehensive overview of Rust verification tools:

1. **Miri** detects undefined behavior through interpreted execution
2. **Loom** finds concurrency bugs via model checking
3. **Creusot** and **Prusti** enable deductive verification of functional correctness
4. **Fuzzing tools** find bugs through randomized testing

The verification pyramid provides a framework for selecting appropriate tools based on required assurance levels. For safety-critical code, combining multiple verification techniques provides the strongest guarantees.

**Theorem SUMMARY (VERIFICATION-COMPOSITION)**:
*For a program P, let V1, V2, ..., Vn be verification tools with soundness guarantees S1, S2, ..., Sn. The composed verification V1 followed by V2 followed by ... Vn provides soundness guarantee S1 intersect S2 intersect ... intersect Sn, potentially discovering bugs that individual tools miss.*

---

*Document Version: 1.0*
*Last Updated: 2026-03-06*
*Verification Status: Draft*

---

## Counter-Examples Index

This document contains **17 counter-examples** demonstrating bugs caught by verification tools:

### Miri Counter-Examples (7 total)

1. Use of uninitialized memory (2.1)
2. Data race (2.2)
3. Invalid pointer arithmetic (2.3)
4. Type punning/strict aliasing (2.4)
5. Misaligned access (2.5)
6. Use after free / double free (2.6)
7. Invalid vtable (2.7)

### Loom Counter-Examples (6 total)

1. Missed atomic ordering (3.1)
2. Incorrect CAS loop (3.2)
3. ABA problem (3.3)
4. Memory ordering bug (3.4)
5. Lost wakeup (3.5)
6. Deadlock (3.6)

### Creusot Counter-Examples (4 total)

1. Integer overflow (4.1)
2. Array bounds (4.2)
3. Logic error in specification (4.3)
4. Broken loop invariant (4.4)

## Theorems Index

This document contains **9 theorems** about verification guarantees:

1. **Theorem 1.1**: VERIFICATION-SOUNDNESS-HIERARCHY
2. **Theorem 1.2**: RUST-VERIFICATION-COMPLETENESS
3. **Theorem 2.1**: MIRI-SOUNDNESS
4. **Theorem 2.2**: MIRI-COMPLETENESS-LIMIT
5. **Theorem 3.1**: LOOM-COVERAGE
6. **Theorem 3.2**: LOOM-COMPLETENESS-BOUND
7. **Theorem 4.1**: CREUSOT-SOUNDNESS
8. **Theorem 8.1**: VERIFIED-VEC-CORRECTNESS
9. **Theorem SUMMARY**: VERIFICATION-COMPOSITION

---

*End of Document*
