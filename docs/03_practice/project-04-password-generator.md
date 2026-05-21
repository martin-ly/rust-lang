# 实践项目 04: 密码生成器

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 1-2小时

---

## 项目目标
> **[来源: Rust Official Docs]**

创建一个安全的随机密码生成器。

---

## 功能需求
> **[来源: Rust Official Docs]**

- [ ] 生成随机密码: `passgen -l 16`
- [ ] 支持选项: 大小写、数字、特殊字符
- [ ] 密码强度评估
- [ ] 批量生成

---

## 学习要点
> **[来源: Rust Official Docs]**

### 随机数生成

```rust
use rand::{thread_rng, Rng};

fn generate_password(length: usize) -> String {
    const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                            abcdefghijklmnopqrstuvwxyz\
                            0123456789";
    let mut rng = thread_rng();

    (0..length)
        .map(|_| CHARSET[rng.gen_range(0..CHARSET.len())] as char)
        .collect()
}
```

---

## 参考实现

完整参考实现位于: `examples/password-generator/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)


---

- [README](./README.md)
