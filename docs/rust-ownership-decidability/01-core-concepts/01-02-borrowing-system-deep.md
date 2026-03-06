# 01-02: The Rust Borrowing System - A Formal Deep Dive

## Table of Contents

- [01-02: The Rust Borrowing System - A Formal Deep Dive](#01-02-the-rust-borrowing-system---a-formal-deep-dive)
  - [Table of Contents](#table-of-contents)
  - [1. Introduction and Overview](#1-introduction-and-overview)
    - [1.1 The Fundamental Insight](#11-the-fundamental-insight)
    - [1.2 Historical Context](#12-historical-context)
    - [1.3 Chapter Roadmap](#13-chapter-roadmap)
  - [2. Borrowing Formal Semantics](#2-borrowing-formal-semantics)
    - [2.1 Preliminaries](#21-preliminaries)
      - [2.1.1 Syntax](#211-syntax)
      - [2.1.2 Contexts](#212-contexts)
    - [2.2 Borrow Judgment](#22-borrow-judgment)
      - [2.2.1 Immutable Borrow Rule](#221-immutable-borrow-rule)
      - [2.2.2 Mutable Borrow Rule](#222-mutable-borrow-rule)
      - [2.2.3 Dereference Rules](#223-dereference-rules)
    - [2.3 Lifetime Parameters](#23-lifetime-parameters)
      - [2.3.1 Lifetime Quantification](#231-lifetime-quantification)
      - [2.3.2 Lifetime Constraints](#232-lifetime-constraints)
      - [2.3.3 Lifetime in Function Signatures](#233-lifetime-in-function-signatures)
    - [2.4 Operational Semantics](#24-operational-semantics)
      - [2.4.1 Small-Step Semantics](#241-small-step-semantics)
      - [2.4.2 Memory Model](#242-memory-model)
    - [2.5 Type Rules for Borrowing](#25-type-rules-for-borrowing)
      - [2.5.1 Subtyping with Lifetimes](#251-subtyping-with-lifetimes)
      - [2.5.2 Variance Rules](#252-variance-rules)
  - [3. Borrowing Rules Formalization](#3-borrowing-rules-formalization)
    - [3.1 Theorem: BORROW-XOR-MUTATE](#31-theorem-borrow-xor-mutate)
      - [3.1.1 Formal Statement](#311-formal-statement)
      - [3.1.2 Proof](#312-proof)
      - [3.1.3 Consequences](#313-consequences)
    - [3.2 Theorem: BORROW-DOESNT-TRANSFER](#32-theorem-borrow-doesnt-transfer)
      - [3.2.1 Formal Statement](#321-formal-statement)
      - [3.2.2 Proof](#322-proof)
      - [3.2.3 Contrast with Move Semantics](#323-contrast-with-move-semantics)
    - [3.3 Theorem: MUTABLE-BORROW-EXCLUSIVITY](#33-theorem-mutable-borrow-exclusivity)
      - [3.3.1 Formal Statement](#331-formal-statement)
      - [3.3.2 Proof](#332-proof)
    - [3.4 Theorem: BORROW-LIFETIME-VALIDITY](#34-theorem-borrow-lifetime-validity)
      - [3.4.1 Formal Statement](#341-formal-statement)
      - [3.4.2 Proof](#342-proof)
    - [3.5 Theorem: NO-DANGLING-REFERENCES](#35-theorem-no-dangling-references)
      - [3.5.1 Formal Statement](#351-formal-statement)
      - [3.5.2 Proof](#352-proof)
  - [4. Lifetime Analysis](#4-lifetime-analysis)
    - [4.1 Lifetime as Sets of Program Points](#41-lifetime-as-sets-of-program-points)
      - [4.1.1 Definition](#411-definition)
      - [4.1.2 Program Points](#412-program-points)
      - [4.1.3 Lifetime Construction](#413-lifetime-construction)
    - [4.2 Lifetime Inclusion](#42-lifetime-inclusion)
      - [4.2.1 Definition](#421-definition)
      - [4.2.2 Formal Definition](#422-formal-definition)
      - [4.2.3 Visual Representation](#423-visual-representation)
    - [4.3 Lifetime Constraint Solving](#43-lifetime-constraint-solving)
      - [4.3.1 Constraint Generation](#431-constraint-generation)
      - [4.3.2 Constraint Graph](#432-constraint-graph)
      - [4.3.3 Constraint Solving Algorithm](#433-constraint-solving-algorithm)
    - [4.4 Lifetime Elision Rules (Formal)](#44-lifetime-elision-rules-formal)
      - [4.4.1 Elision Desugaring](#441-elision-desugaring)
      - [4.4.2 Formal Elision Function](#442-formal-elision-function)
    - [4.5 Lifetime Subtyping in Detail](#45-lifetime-subtyping-in-detail)
      - [4.5.1 Covariance](#451-covariance)
      - [4.5.2 Contravariance](#452-contravariance)
      - [4.5.3 Invariance](#453-invariance)
  - [5. Counter-Examples: The 15 Canonical Cases](#5-counter-examples-the-15-canonical-cases)
    - [5.1 Counter-Example 1: Mutable Borrow While Immutable Active](#51-counter-example-1-mutable-borrow-while-immutable-active)
    - [5.2 Counter-Example 2: Two Mutable Borrows](#52-counter-example-2-two-mutable-borrows)
    - [5.3 Counter-Example 3: Borrow Across Function Boundary](#53-counter-example-3-borrow-across-function-boundary)
    - [5.4 Counter-Example 4: Return Local Reference](#54-counter-example-4-return-local-reference)
    - [5.5 Counter-Example 5: Self-Referential Struct](#55-counter-example-5-self-referential-struct)
    - [5.6 Counter-Example 6: Lifetime Variance Confusion](#56-counter-example-6-lifetime-variance-confusion)
    - [5.7 Counter-Example 7: Higher-Ranked Trait Bounds](#57-counter-example-7-higher-ranked-trait-bounds)
    - [5.8 Counter-Example 8: Lifetime in Associated Types](#58-counter-example-8-lifetime-in-associated-types)
    - [5.9 Counter-Example 9: GAT Lifetime Constraints](#59-counter-example-9-gat-lifetime-constraints)
    - [5.10 Counter-Example 10: Impl Trait Lifetime Capture](#510-counter-example-10-impl-trait-lifetime-capture)
    - [5.11 Counter-Example 11: Async Lifetime Issues](#511-counter-example-11-async-lifetime-issues)
    - [5.12 Counter-Example 12: Iterator Invalidation](#512-counter-example-12-iterator-invalidation)
    - [5.13 Counter-Example 13: Vec Reallocation Invalidation](#513-counter-example-13-vec-reallocation-invalidation)
    - [5.14 Counter-Example 14: String Slice Invalidation](#514-counter-example-14-string-slice-invalidation)
    - [5.15 Counter-Example 15: Closure Lifetime Capture](#515-counter-example-15-closure-lifetime-capture)
  - [6. Non-Lexical Lifetimes (NLL)](#6-non-lexical-lifetimes-nll)
    - [6.1 The Problem with Lexical Lifetimes](#61-the-problem-with-lexical-lifetimes)
    - [6.2 NLL Algorithm](#62-nll-algorithm)
      - [6.2.1 Core Algorithm](#621-core-algorithm)
      - [6.2.2 Dataflow Analysis](#622-dataflow-analysis)
      - [6.2.3 Borrow Conflict Detection](#623-borrow-conflict-detection)
    - [6.3 NLL Examples](#63-nll-examples)
      - [6.3.1 Basic Example](#631-basic-example)
      - [6.3.2 Branching Example](#632-branching-example)
      - [6.3.3 Loop Example](#633-loop-example)
      - [6.3.4 Complex Control Flow](#634-complex-control-flow)
    - [6.4 Two-Phase Borrows](#64-two-phase-borrows)
      - [6.4.1 Formalization](#641-formalization)
    - [6.5 Limitations of NLL](#65-limitations-of-nll)
  - [7. Polonius: Next-Generation Borrow Checker](#7-polonius-next-generation-borrow-checker)
    - [7.1 Origins vs Scopes](#71-origins-vs-scopes)
      - [7.1.1 NLL Approach (Scopes)](#711-nll-approach-scopes)
      - [7.1.2 Polonius Approach (Origins)](#712-polonius-approach-origins)
    - [7.2 Origin-Based Analysis](#72-origin-based-analysis)
      - [7.2.1 Core Concept](#721-core-concept)
      - [7.2.2 Dataflow Equations](#722-dataflow-equations)
    - [7.3 Polonius vs NLL](#73-polonius-vs-nll)
      - [7.3.1 Example: Conditional Borrows](#731-example-conditional-borrows)
      - [7.3.2 Example: Loop Carried Dependencies](#732-example-loop-carried-dependencies)
    - [7.4 Polonius Algorithm](#74-polonius-algorithm)
      - [7.4.1 Datalog Formulation](#741-datalog-formulation)
      - [7.4.2 Implementation Sketch](#742-implementation-sketch)
    - [7.5 Polonius Benefits](#75-polonius-benefits)
    - [7.6 Polonius Status](#76-polonius-status)
  - [8. Advanced Patterns](#8-advanced-patterns)
    - [8.1 Reborrowing](#81-reborrowing)
      - [8.1.1 Definition](#811-definition)
      - [8.1.2 Formal Semantics](#812-formal-semantics)
      - [8.1.3 Common Patterns](#813-common-patterns)
    - [8.2 Splitting Borrows](#82-splitting-borrows)
      - [8.2.1 Slice Splitting](#821-slice-splitting)
      - [8.2.2 Formalization](#822-formalization)
      - [8.2.3 Struct Field Splitting](#823-struct-field-splitting)
      - [8.2.4 Array Splitting Pattern](#824-array-splitting-pattern)
    - [8.3 Borrowing with Interior Mutability](#83-borrowing-with-interior-mutability)
      - [8.3.1 Cell Types](#831-cell-types)
      - [8.3.2 RefCell](#832-refcell)
      - [8.3.3 Formal Semantics of Interior Mutability](#833-formal-semantics-of-interior-mutability)
    - [8.4 Lending Iterator Pattern](#84-lending-iterator-pattern)
      - [8.4.1 Definition](#841-definition)
      - [8.4.2 Implementation Example](#842-implementation-example)
      - [8.4.3 Use Case: In-Place Parsing](#843-use-case-in-place-parsing)
    - [8.5 Self-Referential Structs with Pin](#85-self-referential-structs-with-pin)
      - [8.5.1 The Problem](#851-the-problem)
      - [8.5.2 Pin Solution](#852-pin-solution)
      - [8.5.3 Formal Properties of Pin](#853-formal-properties-of-pin)
  - [9. Case Study: HashMap Iterator](#9-case-study-hashmap-iterator)
    - [9.1 HashMap Overview](#91-hashmap-overview)
    - [9.2 Iterator Types](#92-iterator-types)
    - [9.3 Borrow Checker Analysis](#93-borrow-checker-analysis)
      - [9.3.1 Lifetime Relationships](#931-lifetime-relationships)
      - [9.3.2 Key Constraints](#932-key-constraints)
      - [9.3.3 Why Keys are Immutable](#933-why-keys-are-immutable)
    - [9.4 Advanced Pattern: Entry API](#94-advanced-pattern-entry-api)
      - [9.4.1 Entry Definition](#941-entry-definition)
      - [9.4.2 Borrow Checker Guarantees](#942-borrow-checker-guarantees)
    - [9.5 Concurrent Access Pattern](#95-concurrent-access-pattern)
      - [9.5.1 The Problem](#951-the-problem)
      - [9.5.2 Solutions](#952-solutions)
    - [9.6 Performance Implications](#96-performance-implications)
  - [10. Appendix: Rust 1.94 Features](#10-appendix-rust-194-features)
    - [10.1 Precise Capturing (Rust 1.82+)](#101-precise-capturing-rust-182)
    - [10.2 Lifetime Binder Syntax](#102-lifetime-binder-syntax)
    - [10.3 const Mut References](#103-const-mut-references)
    - [10.4 Pin Enhancements](#104-pin-enhancements)
    - [10.5 async Closure Improvements](#105-async-closure-improvements)
  - [Summary](#summary)
  - [References](#references)

---

## 1. Introduction and Overview

The Rust borrowing system represents one of the most significant innovations in programming language design. While ownership establishes the foundation for memory safety without garbage collection, borrowing provides the mechanism by which multiple parts of a program can safely access data without transferring ownership. This chapter provides a comprehensive, formal treatment of Rust's borrowing semantics.

### 1.1 The Fundamental Insight

The core insight of Rust's borrowing system is that memory safety violations arise from **aliasing combined with mutation**. If we can ensure that:

1. Data is either aliased OR mutated, but never both simultaneously
2. All references are always valid (point to live data)
3. No dangling references exist

Then we have achieved memory safety without runtime overhead.

### 1.2 Historical Context

The concept of borrowing has roots in several areas:

- **Region-based memory management** (Tofte & Talpin, 1994)
- **Linear types** and **affine types** (Wadler, 1990)
- **Alias types** and **ownership types** (Clarke et al., 1998)
- **Separation logic** (Reynolds, 2002)

Rust's innovation was combining these theoretical foundations with practical usability, creating a system that programmers can effectively use for systems programming.

### 1.3 Chapter Roadmap

This chapter proceeds as follows:

- Section 2 establishes the formal semantics of borrowing through inference rules
- Section 3 formalizes the core theorems governing borrowing
- Section 4 presents 15 detailed counter-examples
- Section 5 covers Non-Lexical Lifetimes
- Section 6 explores the Polonius borrow checker
- Section 7 discusses advanced patterns
- Section 8 provides a detailed case study

---

## 2. Borrowing Formal Semantics

We begin with a formal operational semantics for Rust's borrowing system. Our presentation uses a standard natural deduction style with contexts, judgments, and inference rules.

### 2.1 Preliminaries

#### 2.1.1 Syntax

```
Types:
  T, U ::= i32 | bool | () | Box<T> | &amp;'a T | &amp;'a mut T | [T; n] | Vec<T>
         | struct { fields } | enum { variants } | fn(T1, ..., Tn) -> U

Expressions:
  e ::= x | n | true | false | () | Box::new(e) | *e | &amp;e | &amp;mut e
      | e.f | e1; e2 | { e } | if e1 { e2 } else { e3 }
      | loop { e } | break | continue | return e
      | f(e1, ..., en) | e1.f(e2, ..., en)

Values:
  v ::= n | true | false | () | box v | &amp;x | &amp;mut x

Lifetimes:
  'a, 'b ::= 'static | 'anon | 'named

Program Points:
  p ::= entry | exit | before(e) | after(e)
```

#### 2.1.2 Contexts

```
Γ ::= ∅ | Γ, x: T                 (typing context)
Σ ::= ∅ | Σ, x ↦ v                (value store)
Λ ::= ∅ | Λ, 'a                   (lifetime context)
B ::= ∅ | B, (x, kind, 'a)        (borrow set)
```

where `kind ∈ {shared, mut}`

### 2.2 Borrow Judgment

The fundamental judgment for borrowing is:

```
Γ ⊢ e : T    (e has type T in context Γ)
```

#### 2.2.1 Immutable Borrow Rule

```
      Γ ⊢ x: T
--------------------------- (borrow-ref)
  Γ ⊢ &x: &'a T

Conditions:
  1. 'a must be a valid lifetime in Λ
  2. x must be alive at the creation point of 'a
  3. No conflicting mutable borrows of x are active
```

**Explanation**: The immutable borrow rule states that if `x` has type `T` in context Γ, then taking a shared reference to `x` produces a value of type `&'a T`. The lifetime `'a` represents the scope during which this reference is valid.

#### 2.2.2 Mutable Borrow Rule

```
        Γ ⊢ x: T
----------------------------- (borrow-mut)
  Γ ⊢ &mut x: &'a mut T

Conditions:
  1. 'a must be a valid lifetime in Λ
  2. x must be alive at the creation point of 'a
  3. x must be mutable (not immutable binding)
  4. No other borrows (shared or mutable) of x are active
```

**Explanation**: The mutable borrow rule is more restrictive. It requires that no other borrows exist simultaneously, ensuring unique access.

#### 2.2.3 Dereference Rules

```
      Γ ⊢ e: &'a T
------------------------- (deref-shared)
      Γ ⊢ *e: T

    Γ ⊢ e: &'a mut T
------------------------- (deref-mut)
      Γ ⊢ *e: T

    Γ ⊢ e: Box<T>
------------------------- (deref-box)
      Γ ⊢ *e: T
```

### 2.3 Lifetime Parameters

#### 2.3.1 Lifetime Quantification

```
∀'a. 'a: lifetime → &'a T is valid for 'a
```

This states that for any lifetime `'a`, a reference `&'a T` is valid throughout `'a`.

#### 2.3.2 Lifetime Constraints

```
'a: 'b  (read as: 'a outlives 'b)

Meaning: The lifetime 'a encompasses at least all program points in 'b
         'a ⊇ 'b (set inclusion)
```

#### 2.3.3 Lifetime in Function Signatures

```
fn foo<'a, 'b>(x: &'a T, y: &'b U) -> &'a V where 'a: 'b

Γ, 'a: lifetime, 'b: lifetime, 'a: 'b ⊢
  foo : ∀'a, 'b. &'a T -> &'b U -> &'a V
```

### 2.4 Operational Semantics

#### 2.4.1 Small-Step Semantics

We define the transition relation `⟨Σ, e⟩ → ⟨Σ', e'⟩`:

```
                      x ↦ v ∈ Σ
-------------------------------------------------- (var)
           ⟨Σ, x⟩ → ⟨Σ, v⟩

              ⟨Σ, e⟩ → ⟨Σ', e'⟩
--------------------------------------------- (borrow-step)
      ⟨Σ, &e⟩ → ⟨Σ', &e'⟩

              x ↦ v ∈ Σ
--------------------------------------------- (borrow-val)
         ⟨Σ, &x⟩ → ⟨Σ, &x⟩

              x ↦ v ∈ Σ
--------------------------------------------- (borrow-mut-val)
        ⟨Σ, &mut x⟩ → ⟨Σ, &mut x⟩
```

#### 2.4.2 Memory Model

The memory model tracks:

```
Memory M ::= Loc → Value ∪ ⊥
Ownership O ::= Path → {owned, borrowed(shared, n), borrowed(mut), moved}
```

### 2.5 Type Rules for Borrowing

#### 2.5.1 Subtyping with Lifetimes

```
'a: 'b
------------------------ (sub-ref)
&'a T <: &'b T

'a: 'b
------------------------ (sub-mut)
&'a mut T <: &'b mut T
```

**Covariance**: `&'a T` is covariant in `'a`
**Invariance**: `&'a mut T` is invariant in both `'a` and `T`

#### 2.5.2 Variance Rules

```
Type                Variance in 'a        Variance in T
---------------------------------------------------------
&'a T               Covariant             Covariant
&'a mut T           Covariant             Invariant
Box<T>              -                     Covariant
Vec<T>              -                     Covariant
fn(T) -> U          Contravariant         Covariant
*const T            -                     Covariant
*mut T              -                     Invariant
```

---

## 3. Borrowing Rules Formalization

This section formalizes the core theorems that govern Rust's borrowing behavior.

### 3.1 Theorem: BORROW-XOR-MUTATE

**Statement**: At any program point p, for any value v:

- Either there exist n ≥ 0 immutable borrows of v, OR
- There exists exactly 1 mutable borrow of v
- Never both simultaneously

#### 3.1.1 Formal Statement

```
∀p ∈ ProgramPoints. ∀v ∈ Values.
  let B_v = {b ∈ B | b references v} in
  (∀b ∈ B_v. b.kind = shared) ∨
  (∃! b ∈ B_v. b.kind = mut ∧ |B_v| = 1)
```

#### 3.1.2 Proof

**Proof by induction on program execution trace**:

*Base case*: At program entry, B = ∅, so the property holds vacuously.

*Inductive step*: Assume the property holds at program point p. We show it holds at the next point p'.

The execution can take one of the following actions:

1. **Create shared borrow**: `let r = &v;`
   - Precondition: No active mutable borrow of v
   - Postcondition: Add (v, shared, 'a) to B
   - If previously all borrows were shared, still all shared ✓
   - If previously no borrows, now all shared ✓

2. **Create mutable borrow**: `let r = &mut v;`
   - Precondition: No active borrows of v
   - Postcondition: Add (v, mut, 'a) to B
   - Exactly one mutable borrow exists ✓

3. **Drop a borrow**: Borrow lifetime ends
   - Remove borrow from B
   - If B_v was all shared, still all shared or empty ✓
   - If B_v had one mutable, now empty ✓

4. **Other operations**: Do not modify B_v

Thus the property is preserved. ∎

#### 3.1.3 Consequences

This theorem ensures:

- No data races: Multiple writers are impossible
- No iterator invalidation: Reading while modifying is impossible
- No use-after-free: References cannot outlive their referents

### 3.2 Theorem: BORROW-DOESNT-TRANSFER

**Statement**: Borrowing creates a view (reference), not a transfer of ownership:

```
owns(x, T) ⊢ &x: &T ⊸ owns(x, T)
```

#### 3.2.1 Formal Statement

Given:

- Initial state: Σ(x) = v, Ownership(x) = owned
- Operation: `let r = &x;`
- Final state: Σ(x) = v, Ownership(x) = borrowed(shared, 1)

When `r` goes out of scope:

- Ownership(x) returns to owned

#### 3.2.2 Proof

**Proof by operational semantics**:

1. Before borrow: `O(x) = owned`
2. During borrow: `O(x) = borrowed(shared, n)` where n ≥ 1
3. After all borrows drop: `O(x) = owned`

The key insight is that ownership is temporarily restricted, not transferred. The original owner regains full control after all borrows end. ∎

#### 3.2.3 Contrast with Move Semantics

```
// Move: ownership transfers permanently
let x = Box::new(5);
let y = x;          // x is moved, cannot use x again

// Borrow: ownership temporarily restricted
let x = Box::new(5);
let y = &x;         // x is borrowed, can use x after y drops
```

### 3.3 Theorem: MUTABLE-BORROW-EXCLUSIVITY

**Statement**: `&mut T` guarantees unique access:

```
&mut x ∧ &mut x ⊢ False
```

#### 3.3.1 Formal Statement

At any program point:

```
¬∃v. ∃r1, r2. r1 ≠ r2 ∧ r1: &mut v ∧ r2: &mut v
```

#### 3.3.2 Proof

**Proof by contradiction**:

Assume there exist two distinct mutable borrows `r1` and `r2` to the same value `v` at program point `p`.

Case analysis on how `r2` could be created:

1. `r2` created after `r1`: The borrow checker would reject because `v` already has an active mutable borrow.

2. `r2` created before `r1`: The borrow checker would reject because `v` already has an active mutable borrow.

3. `r1` and `r2` are the same reference: Contradicts `r1 ≠ r2`.

4. `r2` is derived from `r1` (reborrow): This is allowed but `r1` is disabled during `r2`'s lifetime.

All cases lead to contradiction or require that the borrows are not simultaneously active. ∎

### 3.4 Theorem: BORROW-LIFETIME-VALIDITY

**Statement**: All borrows are valid for their entire lifetime:

```
Γ ⊢ &x: &'a T ⟹ alive(x) throughout 'a
```

#### 3.4.1 Formal Statement

For any borrow `r = &x` with lifetime `'a`:

```
∀p ∈ 'a. alive_at(x, p)
```

#### 3.4.2 Proof

**Proof by lifetime construction**:

The borrow checker constructs lifetimes such that:

1. `'a` starts at the point where `&x` is created
2. `'a` ends at the last use of the borrow
3. The lifetime `'a` is constrained to not exceed `x`'s lifetime

By construction, `x` must outlive `'a`. ∎

### 3.5 Theorem: NO-DANGLING-REFERENCES

**Statement**: Well-typed Rust programs have no dangling references.

#### 3.5.1 Formal Statement

```
⊢ e: T ⟹ ¬∃r ∈ references(e). dangling(r)
```

#### 3.5.2 Proof

**Proof by type system soundness**:

1. A reference `r: &'a T` can only be created from a value `v` that lives at least as long as `'a`.

2. The type of `r` carries the lifetime constraint that the referent must be valid.

3. When `v` is dropped, any borrows of `v` must have already ended (enforced by lifetime analysis).

4. Therefore, when `r` is used, `v` is guaranteed to be valid.

∎

---

## 4. Lifetime Analysis

This section formalizes how Rust analyzes and checks lifetimes.

### 4.1 Lifetime as Sets of Program Points

#### 4.1.1 Definition

A lifetime `'a` is a set of program points:

```
'a = {p₁, p₂, ..., pₙ} where each pᵢ is a program point
```

#### 4.1.2 Program Points

```
p ::=
  | entry(f)           -- Entry to function f
  | exit(f)            -- Exit from function f
  | stmt(n)            -- Statement number n
  | expr(e)            -- Expression e
  | def(x)             -- Definition of variable x
  | use(x)             -- Use of variable x
  | drop(x)            -- Drop of variable x
```

#### 4.1.3 Lifetime Construction

For a variable `x` declared at point `def(x)`:

```
lifetime(x) = {p | p is between def(x) and last_use(x)} ∪ {drop(x)}
```

### 4.2 Lifetime Inclusion

#### 4.2.1 Definition

```
'a ⊆ 'b means 'a outlives 'b (equivalently: 'b lives within 'a)
```

#### 4.2.2 Formal Definition

```
'a: 'b ⟺ 'b ⊆ 'a
```

As sets:

```
'a: 'b ⟺ ∀p ∈ 'b. p ∈ 'a
```

#### 4.2.3 Visual Representation

```
Program execution: →→→→→→→→→→→→→→→→→
'a:              [===========]
'b:                  [====]

'a: 'b holds because 'b is contained within 'a
```

### 4.3 Lifetime Constraint Solving

#### 4.3.1 Constraint Generation

Given a program, we generate constraints:

```
// From borrow creation
&'a x  ⟹  lifetime(x): 'a

// From function calls
fn foo<'a>(x: &'a T)  ⟹  'actual: 'a at call site

// From return values
fn foo<'a>() -> &'a T  ⟹  'a: 'output_lifetime
```

#### 4.3.2 Constraint Graph

```
'a: 'b  becomes edge: 'b → 'a

Example:
  'static: 'a
  'a: 'b
  'b: 'c

Graph: 'c → 'b → 'a → 'static
```

#### 4.3.3 Constraint Solving Algorithm

```rust
fn solve_constraints(constraints: &[Constraint]) -> Result<Assignment, Error> {
    // Build graph
    let mut graph = Graph::new();
    for 'a: 'b in constraints {
        graph.add_edge('b, 'a);
    }

    // Check for cycles involving 'static (error)
    if graph.has_path('static, 'a) && 'a != 'static {
        // 'static cannot depend on non-static lifetime
        return Err(Error::InvalidConstraint);
    }

    // Compute minimal solution
    let mut assignment = HashMap::new();
    assignment.insert('static, Lifetime::Static);

    // Propagate constraints
    for lifetime in graph.topological_sort() {
        let min_lifetime = graph.predecessors(lifetime)
            .map(|pred| assignment[pred])
            .fold(Lifetime::Empty, |a, b| a.union(b));
        assignment.insert(lifetime, min_lifetime);
    }

    Ok(assignment)
}
```

### 4.4 Lifetime Elision Rules (Formal)

#### 4.4.1 Elision Desugaring

Rust allows eliding lifetimes in common patterns. Here is the formal desugaring:

**Rule 1: Single input lifetime**

```
// Elided
fn foo(x: &T) -> &U

// Desugared
fn foo<'a>(x: &'a T) -> &'a U
```

**Rule 2: Multiple input lifetimes, one is &self or &mut self**

```
// Elided
impl Bar {
    fn foo(&self, x: &T) -> &U
}

// Desugared
impl Bar {
    fn foo<'a, 'b>(&'a self, x: &'b T) -> &'a U
}
```

**Rule 3: Multiple input lifetimes, no method receiver**

```
// Elided - ERROR, cannot elide
fn foo(x: &T, y: &U) -> &V

// Must be explicit
fn foo<'a, 'b, 'c>(x: &'a T, y: &'b U) -> &'c V
```

#### 4.4.2 Formal Elision Function

```
elide(fn) = match fn.inputs {
    [] => fn,
    [(&'a T)] => substitute(fn, 'a, fresh())
    [(self: &'a Self), ...] => {
        let 'self = fresh();
        substitute(substitute(fn, 'a, 'self), output_lifetime, 'self)
    }
    _ => error("cannot elide")
}
```

### 4.5 Lifetime Subtyping in Detail

#### 4.5.1 Covariance

```
'a: 'b
------------------------
&'a T <: &'b T

Meaning: A longer-lived reference can be used where a shorter-lived one is expected.
```

#### 4.5.2 Contravariance

```
'a: 'b
------------------------
fn(&'b T) <: fn(&'a T)

Meaning: A function accepting shorter-lived references can accept longer-lived ones.
```

#### 4.5.3 Invariance

```
T = U
------------------------
&'a mut T = &'a mut U

Cell<T> = Cell<U>

Meaning: No subtyping allowed - types must be exactly equal.
```

---

## 5. Counter-Examples: The 15 Canonical Cases

This section presents 15 canonical counter-examples that illustrate common borrow checker errors and their resolutions.

### 5.1 Counter-Example 1: Mutable Borrow While Immutable Active

**Problem**: Attempting to create a mutable borrow while immutable borrows are active.

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    let x = &data[0];        // Immutable borrow starts
    println!("{}", x);       // Use the borrow

    let y = &mut data;       // ERROR: cannot borrow mutably
    y.push(4);
}
```

**Error Message**:

```
error[E0502]: cannot borrow `data` as mutable because it is also borrowed as immutable
 --> src/main.rs:6:13
  |
3 |     let x = &data[0];
  |             -------- immutable borrow occurs here
...
6 |     let y = &mut data;
  |             ^^^^^^^^^ mutable borrow occurs here
7 |     y.push(4);
8 | }
  | - immutable borrow ends here
```

**Explanation**: The immutable borrow `x` is still alive when we try to create `y`. This violates BORROW-XOR-MUTATE.

**Solution**:

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    {
        let x = &data[0];
        println!("{}", x);
    } // Immutable borrow ends here

    let y = &mut data;
    y.push(4);
}
```

### 5.2 Counter-Example 2: Two Mutable Borrows

**Problem**: Attempting to create two simultaneous mutable borrows.

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    let x = &mut data;
    let y = &mut data;  // ERROR: second mutable borrow

    x.push(4);
    y.push(5);
}
```

**Error Message**:

```
error[E0499]: cannot borrow `data` as mutable more than once at a time
 --> src/main.rs:5:13
  |
4 |     let x = &mut data;
  |             --------- first mutable borrow occurs here
5 |     let y = &mut data;
  |             ^^^^^^^^^ second mutable borrow occurs here
6 |
7 |     x.push(4);
  |     --------- first borrow later used here
```

**Explanation**: This violates MUTABLE-BORROW-EXCLUSIVITY. Two mutable borrows would allow aliased mutation.

**Solution**:

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    {
        let x = &mut data;
        x.push(4);
    }

    {
        let y = &mut data;
        y.push(5);
    }
}
```

### 5.3 Counter-Example 3: Borrow Across Function Boundary

**Problem**: Returning a reference to a local variable.

```rust
fn get_reference() -> &i32 {
    let x = 5;
    &x  // ERROR: returns reference to local
}
```

**Error Message**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:1:24
  |
1 | fn get_reference() -> &i32 {
  |                        ^ expected named lifetime parameter
  |
help: consider using the `'static` lifetime
  |
1 | fn get_reference() -> &'static i32 {
  |                        +++++++
```

**Explanation**: The local variable `x` is dropped when the function returns, making any reference to it dangling.

**Solution**:

```rust
fn get_value() -> i32 {
    let x = 5;
    x  // Return by value, not reference
}

// Or with proper lifetime annotation:
fn get_reference<'a>(x: &'a i32) -> &'a i32 {
    x  // Return reference to parameter
}
```

### 5.4 Counter-Example 4: Return Local Reference

**Problem**: More complex case of returning a reference to stack data.

```rust
struct Config {
    value: String,
}

fn get_config_string() -> &str {
    let config = Config {
        value: String::from("hello"),
    };
    &config.value  // ERROR
}
```

**Error Message**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:6:28
  |
6 | fn get_config_string() -> &str {
  |                            ^ expected named lifetime parameter
```

**Explanation**: `config` is a local variable that will be dropped. Returning a reference to its field creates a dangling pointer.

**Solution**:

```rust
fn get_config_string(config: &Config) -> &str {
    &config.value  // Reference to parameter, valid as long as config lives
}

// Or return owned data:
fn get_config_string() -> String {
    let config = Config {
        value: String::from("hello"),
    };
    config.value  // Move ownership
}
```

### 5.5 Counter-Example 5: Self-Referential Struct

**Problem**: Struct containing a reference to its own field.

```rust
struct Parser {
    text: String,
    current: &str,  // Reference to text
}

impl Parser {
    fn new(text: String) -> Parser {
        Parser {
            current: &text,  // ERROR
            text,
        }
    }
}
```

**Error Message**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:3:14
  |
3 |     current: &str,
  |              ^ expected named lifetime parameter
```

**Explanation**: The reference `current` would point into `text`, but the struct could be moved, invalidating the reference.

**Solution**:

```rust
// Use indices instead of references
struct Parser {
    text: String,
    current_pos: usize,
}

// Or use reference-counted types
use std::rc::Rc;
struct Parser {
    text: Rc<String>,
}

// Or Pin for self-referential structs (advanced)
use std::pin::Pin;
use std::marker::PhantomPinned;

struct Parser {
    text: String,
    current: *const str,
    _pin: PhantomPinned,
}
```

### 5.6 Counter-Example 6: Lifetime Variance Confusion

**Problem**: Incorrect assumptions about lifetime variance.

```rust
fn extend_lifetime<'a, 'b>(x: &'a str) -> &'b str
where
    'a: 'b,
{
    x
}

fn misuse() {
    let r: &str;
    {
        let s = String::from("hello");
        r = extend_lifetime(&s);  // ERROR: s doesn't live long enough
    }
    println!("{}", r);
}
```

**Error Message**:

```
error[E0597]: `s` does not live long enough
 --> src/main.rs:12:32
  |
12 |         r = extend_lifetime(&s);
  |                                ^ borrowed value does not live long enough
13 |     }
  |     - `s` dropped here while still borrowed
14 |     println!("{}", r);
  |                    - borrow later used here
```

**Explanation**: The constraint `'a: 'b` means `'a` outlives `'b`, so `&'a` can become `&'b`. But we cannot extend beyond the actual lifetime of the data.

**Solution**:

```rust
// Correct usage - don't extend beyond actual lifetime
fn use_correctly() {
    let s = String::from("hello");
    let r = extend_lifetime(&s);
    println!("{}", r);
} // s and r drop together
```

### 5.7 Counter-Example 7: Higher-Ranked Trait Bounds

**Problem**: Incorrect HRTB usage.

```rust
fn process<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s1 = String::from("hello");
    let result = f(&s1);

    let s2 = String::from("world");
    let result2 = f(&s2);

    // ERROR: result might reference s1 which is still borrowed
    drop(s1);
    println!("{}", result);
}
```

**Explanation**: The HRTB ensures the closure returns a reference with the same lifetime as its input, but this can create complex lifetime constraints.

**Solution**:

```rust
fn process_fixed<F>(f: F)
where
    F: Fn(&str) -> String,  // Return owned String instead
{
    let s1 = String::from("hello");
    let result = f(&s1);

    drop(s1);  // Now valid
    println!("{}", result);
}
```

### 5.8 Counter-Example 8: Lifetime in Associated Types

**Problem**: Lifetime constraints in associated types.

```rust
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

struct Wrapper<'a> {
    data: &'a str,
}

impl<'a> Container for Wrapper<'a> {
    type Item = str;  // Missing lifetime!
    fn get(&self) -> &str {
        self.data
    }
}
```

**Error Message**:

```
error[E0106]: missing lifetime specifier
 --> src/main.rs:10:17
  |
10 |     type Item = str;
  |                 ^^^ expected named lifetime parameter
```

**Solution**:

```rust
trait Container<'a> {
    type Item: 'a;
    fn get(&self) -> &'a Self::Item;
}

impl<'a> Container<'a> for Wrapper<'a> {
    type Item = str;
    fn get(&self) -> &'a str {
        self.data
    }
}

// Or with Generic Associated Types (Rust 1.65+)
trait Container {
    type Item<'a> where Self: 'a;
    fn get(&self) -> &Self::Item<'_>;
}
```

### 5.9 Counter-Example 9: GAT Lifetime Constraints

**Problem**: Generic Associated Types with incorrect lifetime constraints.

```rust
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next<'a>(&'a self) -> Option<Self::Item<'a>>;
}

struct WindowIter<'t> {
    data: &'t [i32],
    pos: usize,
}

impl<'t> LendingIterator for WindowIter<'t> {
    type Item<'a> = &'a [i32] where Self: 'a;

    fn next<'a>(&'a self) -> Option<Self::Item<'a>> {
        let result = self.data.get(self.pos..self.pos + 2)?;
        // ERROR: cannot advance iterator
        // self.pos += 1;  // Can't mutate through shared reference
        Some(result)
    }
}
```

**Problem**: The `next` method takes `&self`, preventing mutation needed for iteration.

**Solution**:

```rust
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

impl<'t> LendingIterator for WindowIter<'t> {
    type Item<'a> = &'a [i32] where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        let result = self.data.get(self.pos..self.pos + 2)?;
        self.pos += 1;  // Now valid
        Some(result)
    }
}
```

### 5.10 Counter-Example 10: Impl Trait Lifetime Capture

**Problem**: Lifetime elision with `impl Trait`.

```rust
fn make_iter(data: &Vec<i32>) -> impl Iterator<Item = &i32> {
    data.iter()
}

fn use_iter() {
    let iter;
    {
        let data = vec![1, 2, 3];
        iter = make_iter(&data);
    }  // data dropped
    for x in iter {  // ERROR
        println!("{}", x);
    }
}
```

**Error Message**:

```
error[E0597]: `data` does not live long enough
 --> src/main.rs:9:28
  |
9 |         iter = make_iter(&data);
  |                            ^^^^ borrowed value does not live long enough
10 |     }
  |     - `data` dropped here while still borrowed
```

**Explanation**: The `impl Trait` captures the lifetime of the input, but the returned iterator outlives the data.

**Solution**:

```rust
fn make_iter<'a>(data: &'a Vec<i32>) -> impl Iterator<Item = &'a i32> + 'a {
    data.iter()
}

fn use_iter_correctly() {
    let data = vec![1, 2, 3];
    let iter = make_iter(&data);
    for x in iter {
        println!("{}", x);
    }
}
```

### 5.11 Counter-Example 11: Async Lifetime Issues

**Problem**: Lifetimes across await points.

```rust
async fn process_data(data: &str) -> String {
    let result = fetch_data().await;  // Suspension point
    format!("{} - {}", data, result)  // data must be valid across await
}

async fn caller() {
    let result;
    {
        let local = String::from("hello");
        result = process_data(&local).await;  // ERROR
    }
    println!("{}", result);
}
```

**Error Message**:

```
error[E0597]: `local` does not live long enough
 --> src/main.rs:11:32
  |
11 |         result = process_data(&local).await;
  |                                ^^^^^^ borrowed value does not live long enough
```

**Explanation**: Async functions that borrow data must ensure the borrow is valid for the entire future lifetime, including across await points.

**Solution**:

```rust
async fn process_data_owned(data: String) -> String {
    let result = fetch_data().await;
    format!("{} - {}", data, result)
}

async fn caller_fixed() {
    let local = String::from("hello");
    let result = process_data_owned(local).await;
    println!("{}", result);
}
```

### 5.12 Counter-Example 12: Iterator Invalidation

**Problem**: Modifying a collection while iterating.

```rust
fn main() {
    let mut data = vec![1, 2, 3, 4, 5];

    for x in &data {
        if *x % 2 == 0 {
            data.push(*x * 2);  // ERROR
        }
    }
}
```

**Error Message**:

```
error[E0502]: cannot borrow `data` as mutable because it is also borrowed as immutable
 --> src/main.rs:6:13
  |
4 |     for x in &data {
  |              ----- immutable borrow occurs here
5 |         if *x % 2 == 0 {
6 |             data.push(*x * 2);
  |             ^^^^ mutable borrow occurs here
```

**Explanation**: The iterator holds a reference to the vector. Modifying the vector could invalidate the iterator's internal pointers.

**Solution**:

```rust
fn main() {
    let mut data = vec![1, 2, 3, 4, 5];

    // Collect modifications first
    let to_add: Vec<i32> = data.iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * 2)
        .collect();

    data.extend(to_add);

    // Or use retain for in-place filtering
    data.retain(|&x| x % 2 != 0);
}
```

### 5.13 Counter-Example 13: Vec Reallocation Invalidation

**Problem**: References invalidated by vector growth.

```rust
fn main() {
    let mut data = vec![1, 2, 3];
    let first = &data[0];

    // Trigger reallocation
    for i in 0..100 {
        data.push(i);  // May reallocate
    }

    println!("{}", first);  // ERROR: first may be dangling
}
```

**Error Message**:

```
error[E0502]: cannot borrow `data` as mutable because it is also borrowed as immutable
 --> src/main.rs:7:9
  |
4 |     let first = &data[0];
  |                 -------- immutable borrow occurs here
...
7 |         data.push(i);
  |         ^^^^ mutable borrow occurs here
```

**Explanation**: Pushing to a vector may reallocate its buffer, moving all elements to a new location. Existing references would then point to freed memory.

**Solution**:

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    // Reserve capacity first
    data.reserve(100);
    let first = &data[0];  // Now safe - no reallocation will occur

    for i in 0..100 {
        data.push(i);
    }

    println!("{}", first);
}
```

### 5.14 Counter-Example 14: String Slice Invalidation

**Problem**: String slices invalidated by mutation.

```rust
fn main() {
    let mut s = String::from("hello world");
    let word = &s[0..5];  // Slice referencing s

    s.clear();  // ERROR: mutable borrow while slice exists

    println!("{}", word);
}
```

**Error Message**:

```
error[E0502]: cannot borrow `s` as mutable because it is also borrowed as immutable
 --> src/main.rs:5:5
  |
3 |     let word = &s[0..5];
  |               --------- immutable borrow occurs here
4 |
5 |     s.clear();
  |     ^^^^^^^^^ mutable borrow occurs here
```

**Explanation**: `clear()` modifies the string, which would invalidate the slice. The borrow checker prevents this.

**Solution**:

```rust
fn main() {
    let mut s = String::from("hello world");

    {
        let word = &s[0..5];
        println!("{}", word);
    } // Slice dropped here

    s.clear();  // Now valid
}
```

### 5.15 Counter-Example 15: Closure Lifetime Capture

**Problem**: Closures capturing references with incorrect lifetimes.

```rust
fn make_closure<'a>(s: &'a str) -> impl Fn() -> &'a str {
    move || s
}

fn use_closure() {
    let closure;
    {
        let local = String::from("hello");
        closure = make_closure(&local);
    } // local dropped

    println!("{}", closure());  // ERROR: use after free
}
```

**Error Message**:

```
error[E0597]: `local` does not live long enough
 --> src/main.rs:10:32
  |
10 |         closure = make_closure(&local);
  |                                ^^^^^^ borrowed value does not live long enough
11 |     }
  |     - `local` dropped here while still borrowed
```

**Explanation**: The closure captures the reference, but the returned closure outlives the referenced data.

**Solution**:

```rust
fn make_closure_owned(s: String) -> impl Fn() -> String {
    move || s.clone()
}

fn use_closure_fixed() {
    let local = String::from("hello");
    let closure = make_closure_owned(local);
    println!("{}", closure());
}
```

---

## 6. Non-Lexical Lifetimes (NLL)

Non-Lexical Lifetimes (NLL) represent a significant evolution in Rust's borrow checker. Introduced in Rust 2018, NLL allows borrows to end before the end of their lexical scope, based on actual usage rather than block structure.

### 6.1 The Problem with Lexical Lifetimes

Before NLL, lifetimes were tied to lexical scopes:

```rust
// Pre-NLL error
fn lexical_issue() {
    let mut data = vec![1, 2, 3];
    let x = &data[0];
    println!("{}", x);  // Last use of x

    // ERROR: x still considered alive here
    data.push(4);
}
```

Under lexical lifetimes, `x` was considered alive until the end of the block, even after its last use.

### 6.2 NLL Algorithm

NLL uses dataflow analysis to determine when borrows actually end.

#### 6.2.1 Core Algorithm

```
1. Build Control Flow Graph (CFG)
2. Identify all borrow expressions
3. Compute liveness for each borrow
4. Check for conflicts at each program point
```

#### 6.2.2 Dataflow Analysis

```rust
// Borrow set computation
fn compute_borrow_set(cfg: &Cfg) -> BorrowSet {
    let mut borrow_set = BorrowSet::new();

    for block in cfg.blocks() {
        for statement in block.statements() {
            if let Some(borrow) = extract_borrow(statement) {
                borrow_set.add(borrow);
            }
        }
    }

    borrow_set
}

// Liveness analysis
fn liveness_analysis(cfg: &Cfg, borrow_set: &BorrowSet) -> Liveness {
    let mut liveness = Liveness::new();

    for borrow in borrow_set.iter() {
        let live_points = compute_live_points(cfg, borrow);
        liveness.insert(borrow, live_points);
    }

    liveness
}
```

#### 6.2.3 Borrow Conflict Detection

```rust
fn check_borrows(cfg: &Cfg, liveness: &Liveness) -> Result<(), Vec<BorrowError>> {
    let mut errors = Vec::new();

    for point in cfg.program_points() {
        let active_borrows: Vec<_> = liveness
            .active_at(point)
            .collect();

        // Check BORROW-XOR-MUTATE
        let mutable: Vec<_> = active_borrows
            .iter()
            .filter(|b| b.is_mutable())
            .collect();
        let immutable: Vec<_> = active_borrows
            .iter()
            .filter(|b| !b.is_mutable())
            .collect();

        if mutable.len() > 1 {
            errors.push(BorrowError::MultipleMutable);
        }

        if !mutable.is_empty() && !immutable.is_empty() {
            errors.push(BorrowError::MixedBorrows);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
```

### 6.3 NLL Examples

#### 6.3.1 Basic Example

```rust
fn nll_basic() {
    let mut data = vec![1, 2, 3];
    let x = &data[0];
    println!("{}", x);  // Last use

    // Under NLL: x's borrow ends here
    data.push(4);  // OK!
}
```

#### 6.3.2 Branching Example

```rust
fn nll_branching(cond: bool) {
    let mut data = vec![1, 2, 3];

    if cond {
        let x = &data[0];
        println!("{}", x);
    }  // x's borrow ends here

    data.push(4);  // OK!
}
```

#### 6.3.3 Loop Example

```rust
fn nll_loop() {
    let mut data = vec![1, 2, 3];

    for i in 0..3 {
        let x = &data[i];
        println!("{}", x);
    }  // x's borrow ends each iteration

    data.push(4);  // OK!
}
```

#### 6.3.4 Complex Control Flow

```rust
fn nll_complex(data: &mut Vec<i32>) {
    // Borrow data mutably
    let first = &mut data[0];
    *first += 1;

    // After last use of first, can borrow again
    let second = &mut data[1];
    *second += 1;

    // Both borrows ended, can use data
    data.push(42);
}
```

### 6.4 Two-Phase Borrows

NLL introduces two-phase borrows for method calls:

```rust
fn two_phase_example() {
    let mut vec = vec![1, 2, 3];

    // Desugars to:
    // 1. Reserve phase: &mut vec (for push)
    // 2. Active phase: &vec[0] (for indexing)
    // 3. Invoke: Vec::push(&mut vec, *<&vec[0]>)
    vec.push(vec[0]);  // OK with two-phase borrows!
}
```

#### 6.4.1 Formalization

```
Two-phase borrow phases:
1. RESERVE: Borrow is created but not yet active
2. ACTIVE: Borrow is in use

Transition:
  RESERVE ──use──→ ACTIVE
  ACTIVE  ──drop──→ END
```

### 6.5 Limitations of NLL

NLL still has limitations:

```rust
fn nll_limitation() {
    let mut data = vec![1, 2, 3];
    let x = &data[0];
    let y = &data[1];

    println!("{}", x);  // x used here
    // Even though x is done, y is still considered active
    // because they're in the same "borrow region"

    // ERROR: y still active
    data.push(4);
}
```

---

## 7. Polonius: Next-Generation Borrow Checker

Polonius represents the next generation of Rust's borrow checker, using a fundamentally different approach based on "origins" rather than scopes.

### 7.1 Origins vs Scopes

#### 7.1.1 NLL Approach (Scopes)

```
NLL: Track where borrows are active (scope-based)
'a = {p₁, p₂, p₃, ...}  // Set of program points
```

#### 7.1.2 Polonius Approach (Origins)

```
Polonius: Track where data flows (origin-based)
origin('a) = {loan₁, loan₂, ...}  // Set of loans

A loan is a borrow expression like `&x` or `&mut y`
```

### 7.2 Origin-Based Analysis

#### 7.2.1 Core Concept

Polonius asks: "What loans could this reference be based on?"

```rust
let x = &mut data;  // loan L1: mut borrow of data
let y = x;          // y has same origin as x: {L1}

// If we try to access data:
// Polonius checks: does accessing data conflict with any loan in y's origin?
// L1 is a mutable borrow of data → CONFLICT
```

#### 7.2.2 Dataflow Equations

```
// Origin computation
origin(x) = ⋃ {origin(y) | x is derived from y}

// Loan generation
loan(&x) = fresh_loan(x, kind)

// Conflict detection
conflict(p) = ∃l ∈ active_loans(p). conflicts_with(l, operation_at(p))
```

### 7.3 Polonius vs NLL

#### 7.3.1 Example: Conditional Borrows

```rust
// Code that NLL rejects but Polonius accepts
fn polonius_wins(cond: bool) {
    let mut data = (0, 0);

    let x = if cond {
        &mut data.0
    } else {
        &mut data.1
    };

    *x = 1;

    // NLL: data was mutably borrowed, can't access
    // Polonius: x could only borrow .0 OR .1, never both
    let y = &data.0;  // Polonius accepts, NLL may reject
    println!("{}", y);
}
```

#### 7.3.2 Example: Loop Carried Dependencies

```rust
// Polonius handles complex loop patterns better
fn loop_pattern(data: &mut [i32]) {
    for i in 0..data.len() {
        let x = &mut data[i];
        *x += 1;
        // NLL: borrow might carry to next iteration
        // Polonius: each iteration's borrow is distinct
    }
}
```

### 7.4 Polonius Algorithm

#### 7.4.1 Datalog Formulation

Polonius is expressed as Datalog rules:

```datalog
% Loan origins
origin_live_at(O, P) :- loan_origin(L, O), loan_issued_at(L, P).

% Origin transfer
origin_contains(O1, L) :- origin_contains(O2, L), subset(O2, O1).

% Loan invalidation
loan_invalidated_at(L, P) :-
    loan_origin(L, O),
    access_kind(O, mutate),
    path_accessed(P, O).

% Error detection
error(L, P) :-
    loan_live_at(L, P),
    loan_invalidated_at(L, P).
```

#### 7.4.2 Implementation Sketch

```rust
struct PoloniusEngine {
    facts: Facts,
    output: Output,
}

impl PoloniusEngine {
    fn new() -> Self {
        Self {
            facts: Facts::default(),
            output: Output::default(),
        }
    }

    fn add_loan(&mut self, loan: Loan, point: Point) {
        self.facts.loan_issued_at.push((loan, point));
    }

    fn add_origin_subset(&mut self, sup: Origin, sub: Origin, point: Point) {
        self.facts.subset_base.push((sup, sub, point));
    }

    fn compute(&mut self) {
        // Run Datalog computation
        let algorithm = Algorithm::DatafrogOpt;
        algorithm.compute(&self.facts, &mut self.output);
    }

    fn errors(&self) -> &[Error] {
        &self.output.errors
    }
}
```

### 7.5 Polonius Benefits

1. **More permissive**: Accepts valid programs NLL rejects
2. **Unified model**: Same model for borrow checking and lifetime errors
3. **Better errors**: More precise error messages
4. **Extensible**: Easier to extend for new language features

### 7.6 Polonius Status

As of Rust 1.94, Polonius is available as an experimental feature:

```bash
rustc -Zpolonius program.rs
```

Future versions will make it the default borrow checker.

---

## 8. Advanced Patterns

This section explores advanced borrowing patterns in Rust.

### 8.1 Reborrowing

#### 8.1.1 Definition

Reborrowing converts one reference type to another, typically shortening the lifetime.

```rust
// Reborrowing pattern
fn reborrow_example<T: DerefMut<Target=U>, U>(r: &mut T) -> &mut U {
    &mut **r  // Reborrow: &mut T → &mut U
}
```

#### 8.1.2 Formal Semantics

```
Γ ⊢ r: &'a mut T    T: DerefMut<Target=U>
------------------------------------------- (reborrow-mut)
      Γ ⊢ &mut *r: &'b mut U

where 'b: 'a (shorter lifetime)
```

#### 8.1.3 Common Patterns

```rust
// Pattern 1: Reborrow for method dispatch
fn use_vec(vec: &mut Vec<i32>) {
    // Automatic reborrow: &mut Vec → &mut [i32]
    process_slice(vec);
}

fn process_slice(slice: &mut [i32]) {
    // Work with slice
}

// Pattern 2: Nested reborrowing
fn nested_reborrow(data: &mut &mut String) -> &mut str {
    &mut **data  // &mut &mut String → &mut String → &mut str
}

// Pattern 3: Reborrow in loops
fn loop_reborrow(items: &mut Vec<String>) {
    for item in items.iter_mut() {
        // item: &mut String (reborrowed from iterator)
        item.push_str("!");
    }
}
```

### 8.2 Splitting Borrows

#### 8.2.1 Slice Splitting

```rust
fn split_slice(data: &mut [i32]) -> (&mut [i32], &mut [i32]) {
    let mid = data.len() / 2;
    data.split_at_mut(mid)  // Splits one &mut into two
}
```

#### 8.2.2 Formalization

```
Γ ⊢ data: &'a mut [T; N]    n < N
------------------------------------------------
Γ ⊢ (&data[0..n], &data[n..N]): (&'b mut [T], &'c mut [T])

where 'b ⊆ 'a, 'c ⊆ 'a, 'b and 'c are disjoint
```

#### 8.2.3 Struct Field Splitting

```rust
struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

fn split_point(p: &mut Point3D) -> (&mut f64, &mut f64, &mut f64) {
    (&mut p.x, &mut p.y, &mut p.z)
}
```

#### 8.2.4 Array Splitting Pattern

```rust
fn split_array<T>(arr: &mut [T; 4]) -> (&mut T, &mut T, &mut T, &mut T) {
    let [a, b, c, d]: &mut [T; 4] = arr;
    (a, b, c, d)
}
```

### 8.3 Borrowing with Interior Mutability

#### 8.3.1 Cell Types

```rust
use std::cell::Cell;

// Cell allows mutation through shared reference
fn cell_example(c: &Cell<i32>) {
    c.set(c.get() + 1);  // OK: Cell uses interior mutability
}
```

#### 8.3.2 RefCell

```rust
use std::cell::RefCell;

fn refcell_example(rc: &RefCell<Vec<i32>>) {
    {
        let mut vec = rc.borrow_mut();
        vec.push(1);
    }

    {
        let vec = rc.borrow();
        println!("{:?}", *vec);
    }
}
```

#### 8.3.3 Formal Semantics of Interior Mutability

```
Interior mutability types are INVARIANT:
- Cell<T>: invariant in T
- RefCell<T>: invariant in T
- Mutex<T>: invariant in T

This prevents unsound subtyping:
Cell<&'static str> <: Cell<&'a str> is FALSE
```

### 8.4 Lending Iterator Pattern

#### 8.4.1 Definition

A lending iterator yields references with lifetimes tied to the iterator itself:

```rust
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

#### 8.4.2 Implementation Example

```rust
struct WindowIter<'t> {
    data: &'t [i32],
    pos: usize,
    window_size: usize,
}

impl<'t> LendingIterator for WindowIter<'t> {
    type Item<'a> = &'a [i32] where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        let window = self.data.get(self.pos..self.pos + self.window_size)?;
        self.pos += 1;
        Some(window)
    }
}
```

#### 8.4.3 Use Case: In-Place Parsing

```rust
struct Parser<'input> {
    input: &'input str,
    pos: usize,
}

impl<'input> LendingIterator for Parser<'input> {
    type Item<'a> = &'a str where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        let start = self.pos;
        while self.pos < self.input.len() && !self.input[self.pos..].starts_with(' ') {
            self.pos += 1;
        }

        if start == self.pos {
            return None;
        }

        let token = &self.input[start..self.pos];
        self.pos += 1; // Skip space
        Some(token)
    }
}
```

### 8.5 Self-Referential Structs with Pin

#### 8.5.1 The Problem

```rust
// Cannot do this safely:
struct SelfRef {
    data: String,
    ptr: &str,  // Points to data
}
```

#### 8.5.2 Pin Solution

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfRef {
    data: String,
    ptr: *const str,
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(SelfRef {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data as *const str;
        boxed.ptr = ptr;

        Box::into_pin(boxed)
    }

    fn get_ptr(self: Pin<&Self>) -> &str {
        unsafe { &*self.ptr }
    }
}
```

#### 8.5.3 Formal Properties of Pin

```
Pin<P<T>> guarantees:
1. If T: !Unpin, the pointee will not move
2. P is a pointer type (Box, Rc, Arc, &mut)
3. Safe to create self-referential structs

Self: Unpin means the type CAN be moved even when pinned
Self: !Unpin means the type CANNOT be moved when pinned
```

---

## 9. Case Study: HashMap Iterator

This section provides a detailed analysis of how the borrow checker interacts with `HashMap::iter_mut()`.

### 9.1 HashMap Overview

```rust
pub struct HashMap<K, V, S = RandomState> {
    // ...
}

impl<K, V, S> HashMap<K, V, S> {
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        // Returns iterator over mutable references to entries
    }
}
```

### 9.2 Iterator Types

```rust
pub struct IterMut<'a, K, V> {
    inner: RawIter<(K, V)>,
    marker: PhantomData<&'a mut HashMap<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        // Yield next entry
    }
}
```

### 9.3 Borrow Checker Analysis

#### 9.3.1 Lifetime Relationships

```
map: &'b mut HashMap<K, V>
  │
  │ iter_mut()
  ▼
iter: IterMut<'a, K, V> where 'a: 'b
  │
  │ next()
  ▼
item: (&'a K, &'a mut V)
```

#### 9.3.2 Key Constraints

1. **Iterator borrows map**: `IterMut<'a>` holds reference to map
2. **Items borrow from iterator**: Each item borrows from the iterator
3. **Mutable values, immutable keys**: Keys are immutable, values mutable

#### 9.3.3 Why Keys are Immutable

```rust
// This is NOT allowed:
fn broken<K, V>(map: &mut HashMap<K, V>) {
    for (k, v) in map.iter_mut() {
        *k = some_new_key;  // ERROR
        *v = some_new_value; // OK
    }
}
```

Reason: Changing keys would change their hash values, invalidating the hash table structure.

### 9.4 Advanced Pattern: Entry API

#### 9.4.1 Entry Definition

```rust
pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}
```

#### 9.4.2 Borrow Checker Guarantees

```rust
fn entry_example(map: &mut HashMap<String, i32>) {
    match map.entry("key".to_string()) {
        Entry::Occupied(e) => {
            *e.get_mut() += 1;
        }
        Entry::Vacant(e) => {
            e.insert(0);
        }
    }
    // Entry dropped here, map usable again
}
```

### 9.5 Concurrent Access Pattern

#### 9.5.1 The Problem

```rust
// Cannot do this:
fn concurrent_access(map: &mut HashMap<String, i32>) {
    let iter = map.iter();
    for (k, v) in iter {
        map.insert(k.clone(), *v + 1);  // ERROR: can't mutate while iterating
    }
}
```

#### 9.5.2 Solutions

```rust
// Solution 1: Collect keys first
fn solution1(map: &mut HashMap<String, i32>) {
    let keys: Vec<_> = map.keys().cloned().collect();
    for k in keys {
        let v = map[&k];
        map.insert(k, v + 1);
    }
}

// Solution 2: Use retain
fn solution2(map: &mut HashMap<String, i32>) {
    map.retain(|k, v| {
        *v += 1;
        true // Keep all entries
    });
}

// Solution 3: Use Entry API
fn solution3(map: &mut HashMap<String, i32>) {
    for k in map.keys().cloned().collect::<Vec<_>>() {
        map.entry(k).and_modify(|v| *v += 1);
    }
}
```

### 9.6 Performance Implications

The borrow checker's constraints on HashMap iterators have performance implications:

1. **No aliasing**: Iterator guarantees unique access
2. **Cache efficiency**: Sequential access pattern
3. **No reallocation during iteration**: Safety guarantee

---

## 10. Appendix: Rust 1.94 Features

This appendix covers borrow checker features and improvements in Rust 1.94.

### 10.1 Precise Capturing (Rust 1.82+)

```rust
// Rust 1.82+ precise capturing
fn precise_capture<'a, 'b>(
    x: &'a i32,
    y: &'b i32,
) -> impl use<'a> IntoIterator<Item = &'a i32> {
    // Only captures 'a, not 'b
    [x].into_iter()
}
```

### 10.2 Lifetime Binder Syntax

```rust
// Rust 1.87+ improved lifetime syntax
fn foo<T>(x: &impl for<'a> Trait<'a>) { }

// Equivalent to:
fn foo<T, U>(x: &U) where U: for<'a> Trait<'a> { }
```

### 10.3 const Mut References

```rust
// Rust 1.83+ const mutable references
const fn modify_in_const(x: &mut i32) {
    *x += 1;
}
```

### 10.4 Pin Enhancements

```rust
// Rust 1.82+ Pin::as_deref_mut
impl<P: DerefMut> Pin<P> {
    pub fn as_deref_mut(self: &mut Pin<P>) -> &mut P::Target {
        // ...
    }
}
```

### 10.5 async Closure Improvements

```rust
// Rust 1.84+ async closure improvements
let closure = async || {
    // Better lifetime inference for captures
};
```

---

## Summary

This chapter has provided a comprehensive formal treatment of Rust's borrowing system:

1. **Formal Semantics**: We defined the judgment rules for borrowing and operational semantics.

2. **Core Theorems**: We proved four fundamental theorems:
   - BORROW-XOR-MUTATE: No aliased mutation
   - BORROW-DOESNT-TRANSFER: Borrowing is temporary
   - MUTABLE-BORROW-EXCLUSIVITY: Unique mutable access
   - BORROW-LIFETIME-VALIDITY: References are always valid

3. **Lifetime Analysis**: We formalized lifetimes as sets of program points and described constraint solving.

4. **Counter-Examples**: We analyzed 15 common borrow checker errors and their solutions.

5. **NLL**: We covered Non-Lexical Lifetimes and their dataflow-based analysis.

6. **Polonius**: We introduced the next-generation origin-based borrow checker.

7. **Advanced Patterns**: We explored reborrowing, splitting borrows, lending iterators, and self-referential structs.

8. **Case Study**: We analyzed HashMap iterators in detail.

The borrowing system is the cornerstone of Rust's memory safety guarantees, enabling zero-cost abstractions without garbage collection.

---

## References

1. Matsakis, N. D., & Klock, F. S. (2014). The Rust Language. ACM SIGAda Ada Letters.

2. Jung, R., et al. (2017). RustBelt: Securing the Foundations of the Rust Programming Language. POPL.

3. Weiss, A., Patterson, D., & Ahmed, A. (2021). Rust Verification Tools. PLDI.

4. Vytiniotis, D., Peyton Jones, S., & Schrijvers, T. (2010). Let Should Not Be Generalized. TLDI.

5. Tofte, M., & Talpin, J. P. (1994). Implementation of the Typed Call-by-Value λ-Calculus using a Stack of Regions. POPL.

---

*Document Version: 1.0*
*Target Rust Version: 1.94*
*Last Updated: 2026*
