# 实践项目 04: 密码生成器

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 1-2小时

---

## 项目目标

创建一个安全的随机密码生成器。

---

## 功能需求

- [ ] 生成随机密码: `passgen -l 16`
- [ ] 支持选项: 大小写、数字、特殊字符
- [ ] 密码强度评估
- [ ] 批量生成

---

## 学习要点

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
