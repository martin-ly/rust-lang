# 安全工程（Security Engineering）

## 1. 定义与软件工程对标

**安全工程**是指系统性地设计、实现和维护安全机制，防止数据泄露、未授权访问和攻击。软件工程wiki认为，安全工程是高可靠性系统的基石。
**Security engineering** is the systematic design, implementation, and maintenance of security mechanisms to prevent data leaks, unauthorized access, and attacks. In software engineering, security is foundational for reliable systems.

## 2. Rust 1.88 最新特性

- **所有权与生命周期**：静态消除悬垂指针和数据竞争。
- **trait对象向上转型**：便于安全策略抽象。
- **LazyLock**：安全的全局状态管理。

## 3. 典型惯用法（Idioms）

- 使用类型系统防止未初始化和越界访问
- 结合serde加密/解密敏感数据
- 利用trait抽象认证、授权和审计

## 4. 代码示例

```rust
trait Auth {
    fn authenticate(&self, user: &str, pass: &str) -> bool;
}
```

## 5. 软件工程概念对照

- **最小权限原则（Least Privilege）**：Rust类型系统限制资源访问。
- **防御性编程（Defensive Programming）**：编译期消除大部分安全隐患。
- **安全默认（Secure by Default）**：Rust默认内存安全。

## 6. FAQ

- Q: Rust如何提升系统安全性？
  A: 静态类型、所有权和生命周期机制在编译期消除绝大多数安全漏洞。

---
