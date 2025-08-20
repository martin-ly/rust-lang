# 内存安全验证(Memory Safety Verification)

- 文档版本: 1.0  
- 创建日期: 2025-01-27  
- 状态: 已完成

## 1. 目标

- 消除悬垂引用、双重释放、越界访问与数据竞争(在安全子集)。

## 2. 不变式

```math
\text{Aliasing} \Rightarrow \text{Immutability} \quad \land \quad \text{Mutability} \Rightarrow \text{Uniqueness}
```

## 3. 规则(摘要)

- 借用规则: `&T` 只读别名; `&mut T` 唯一可变
- 生命周期收敛: 所有借用在owner有效期内

## 4. Rust示例(安全释放)

```rust
struct Resource { buf: Vec<u8> }
impl Resource { fn len(&self) -> usize { self.buf.len() } }
fn use_resource(r: &Resource) -> usize { r.len() }
```

## 5. 定理

- Safety: 遵循借用与生命周期规则的程序不触发UB。

## 6. 工具化

- Miri/Valgrind 交叉验证
- 符号执行: 针对边界与释放路径

## 最小可验证示例(MVE)

```rust
fn sum(xs: &[i32]) -> i32 { xs.iter().copied().sum() }

#[test]
fn borrow_rules_hold() {
    let data = vec![1,2,3];
    let s = sum(&data);
    assert_eq!(s, 6);
    // 编译期禁止可变与不可变混用别名：
    // let r = &data; let m = &mut data; // should not compile
}
```

## 证明义务(Proof Obligations)

- M1: 对切片 `&[T]` 仅存在不可变别名(不变式保持)
- M2: 任何可变借用不存在并发别名(唯一性)
- M3: 生命周期终止前不发生释放(无悬垂)

---

## 形式化证明映射

- 所有权/借用与生命周期：
  - 文档：`formal_rust/language/01_ownership_borrowing/01_formal_ownership_system.md`、`formal_rust/language/21_lifetime_elision_theory.md`
- 类型安全骨架（进展/保持）：
  - Coq：`formal_rust/framework/proofs/coq/type_system_progress_preservation.v`
  - Lean：`formal_rust/framework/proofs/lean/TypeSystem/ProgressPreservation.lean`