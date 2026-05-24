
### 10.4 边界测试：RPITIT（Return Position Impl Trait In Traits）的实现一致性（编译错误）

```rust,ignore
trait Factory {
    fn create() -> impl Iterator<Item = i32>;
}

struct MyFactory;

impl Factory for MyFactory {
    // ❌ 编译错误: RPITIT 要求所有实现返回"相同"类型
    // fn create() -> impl Iterator<Item = i32> {
    //     vec![1, 2, 3].into_iter() // 与另一个实现返回的类型不同
    // }

    fn create() -> std::vec::IntoIter<i32> {
        vec![1, 2, 3].into_iter()
    }
}

fn main() {}
```

> **修正**: **RPITIT**（Return Position Impl Trait In Traits，稳定于 1.75）允许 trait 方法返回 `impl Trait`：1) 调用方无需知道具体类型，只依赖 trait bound；2) 不同实现可返回不同具体类型（但 API 签名统一）。限制：1) trait 定义中的 `impl Trait` 在实现时不能替换为具体类型名（必须保持 `impl Trait`）；2) `async fn` in trait 是 RPITIT 的特例（返回 `impl Future`）。RPITIT 与 GAT 的关系：1) RPITIT 是 GAT 的语法糖（`fn foo() -> impl Trait` ≈ `type Foo: Trait; fn foo() -> Self::Foo`）；2) GAT 更灵活但语法更冗长。这与 Java 的接口默认方法（返回具体类型，无抽象返回类型）或 C++ 的虚函数（返回类型必须完全相同，不支持协变返回）不同——Rust 的 RPITIT 是类型系统的创新，平衡了抽象和实现灵活性。[来源: [RPITIT RFC](https://rust-lang.github.io/rfcs/2289-associated-type-bounds.html)] · [来源: [Async Fn In Traits](https://blog.rust-lang.org/2023/12/21/async-fn-rpitit.html)]
