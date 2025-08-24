# const求值理论（形式化补充）

## 1. const函数与const泛型

- const fn、const泛型在编译期求值，提升类型安全与性能。
- 形式化：$\text{ConstEval}: \text{ConstFn} \times \text{ConstArgs} \to \text{ConstValue}$

## 1.3 工程伪代码与类型推导

```rust
// const fn示例
const fn square(x: i32) -> i32 { x * x }
const N: usize = 4;
let arr: [i32; square(N as i32) as usize] = [0; 16];

// const泛型示例
struct ArrayWrapper<T, const N: usize> { data: [T; N] }
```

## 2.1 类型推导与编译期保证

- const fn类型推导：
  - $\Gamma \vdash f: \text{ConstFn}$
  - $\Gamma \vdash f(a): \tau$
- 编译期保证：
  - 所有const上下文禁止未定义行为

## 3.1 编译期计算能力证明链条

- const系统可表达原始递归函数
- 归纳证明：
  - 对所有const表达式递归展开，受限于编译期资源，等价于原始递归子集

## 4. 参考文献

- Rust Reference, Const Generics RFC, TAPL
