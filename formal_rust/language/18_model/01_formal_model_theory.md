# 批判性分析

- Rust 在形式化建模、系统建模等领域具备类型安全和内存安全优势，但相关工具链和生态尚不如主流学术语言（如 Haskell、OCaml）成熟。
- 与 C++/Java 等工程语言相比，Rust 的建模能力更注重安全和并发，但表达能力和抽象层次略逊。
- 在嵌入式、分布式等场景，Rust 建模优势明显，但高阶建模和自动化验证工具仍有提升空间。

## 典型案例

- 使用 Rust 结合 Prusti、Kani 等工具进行嵌入式系统建模与验证。
- Rust 在分布式系统中实现安全的协议建模。
- 结合 trait 和泛型实现高可扩展性的领域建模。
