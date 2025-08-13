# 05. Move Semantics

## 1. Introduction: The Default of Transfer

In Rust, **Move Semantics** is the default behavior for transferring ownership of a value from one binding (variable) to another. It is a cornerstone of Rust's model for resource management, ensuring that every value has a single, unique owner, thereby preventing issues like double-frees and data races at compile time.

Formally, a move operation can be modeled as a state transition. Given a value `v` owned by a variable `x`, moving it to `y` transitions the system state:

**Definition (Move Operation):**
`Move(x, y, v): Owner(v) = x ⊢ Owner(v) = y ∧ Uninit(x)`

This notation signifies that after the move, `y` becomes the new owner of the value `v`, and `x` is transitioned to an uninitialized state, rendering it statically unusable by the compiler.

This default behavior applies to any type that does not implement the `Copy` trait.

## 2. The `Copy` Trait: An Exception for Simple Types

The primary exception to move semantics is the `Copy` trait. `Copy` is a marker trait that, when implemented for a type, changes the assignment behavior from a move to a bitwise copy.

- **Behavior**: If `T` implements `Copy`, assigning `x: T` to `y` will create a bit-for-bit duplicate of `x`'s data on the stack. Both `x` and `y` will be valid, independent instances.
- **Requirement**: A type can only implement `Copy` if all of its fields/components are also `Copy`. This rule transitively prevents types that manage heap resources or require a `Drop` implementation (like `String`, `Vec<T>`, `Box<T>`) from being `Copy`.
- **Common `Copy` Types**: All primitive numeric types (`i32`, `f64`, etc.), the boolean type (`bool`), the character type (`char`), and immutable references (`&T`).

## 3. The Asymmetry of Move vs. The Symmetry of Copy

The distinction between move and copy semantics introduces a fundamental asymmetry in how variables can be treated after an assignment.

- **Move (Asymmetric)**: The operation `let y = x;` is asymmetric. It fundamentally alters `x` by invalidating it. The source and destination are not treated equally; one is consumed, and one is created.

  ```rust
  let s1 = String::from("hello"); // s1 is owner
  let s2 = s1;                    // Ownership moves to s2
  // println!("{}", s1);          // COMPILE ERROR: s1 is invalidated
  ```

- **Copy (Symmetric)**: The operation `let y = x;` is symmetric. It is a simple duplication of value. `x` is unaffected, and `y` is an independent copy. Both variables are equally valid and usable after the operation.

  ```rust
  let n1 = 42; // n1 is owner
  let n2 = n1; // n1 is copied to n2
  println!("{} and {}", n1, n2); // OK: both n1 and n2 are valid
  ```

## 4. Partial Moves

Rust's ownership system operates at a fine-grained level, allowing individual fields of a composite type (like a `struct` or `tuple`) to be moved. This is known as a **partial move**.

```rust
struct Person {
    name: String,
    age: u8, // u8 is Copy
}

let p = Person { name: String::from("Ada"), age: 42 };

// Move the 'name' field, which is not Copy
let name = p.name;

// The 'age' field can still be accessed because u8 is Copy.
// However, the original variable 'p' cannot be used as a whole.
// println!("Age: {}", p.age); // This is often disallowed by the compiler
// let p2 = p; // COMPILE ERROR: use of partially moved value: `p`
```

The key consequence of a partial move is that **the aggregate variable (`p` in this case) becomes partially uninitialized and cannot be used as a whole any longer**. It cannot be moved, and even accessing its remaining `Copy` fields through the original variable is often disallowed to prevent confusion and enforce a clear ownership model.

## 5. Move Semantics in Practice

Move semantics are consistently applied across the language:

- **Function Arguments**: When a variable is passed to a function, its ownership is moved to the function's parameter if the type is not `Copy`. The calling context loses access to the variable.
- **Function Returns**: A function can return a value, moving its ownership out of the function scope and into the calling context.
- **Pattern Matching**: Destructuring a value in a `match` statement or `if let` binding can move ownership of parts of the value into new variables.

## 6. Conclusion

Move semantics is not merely a feature but the foundational principle of Rust's ownership system. By mandating a single owner and making ownership transfer an explicit 'move', Rust eradicates a wide array of memory safety bugs at compile time. It provides a clear, predictable, and efficient model for resource management, which, when combined with the borrow checker, forms the core of Rust's safety and performance guarantees.
"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 概述
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 形式化分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


