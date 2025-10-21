# 认证与授权

> **核心库**: jsonwebtoken, oauth2, argon2  
> **适用场景**: JWT、OAuth2、密码哈希

---

## 📋 核心库

| 库 | 用途 | 推荐度 |
|-----|------|--------|
| **jsonwebtoken** | JWT | ⭐⭐⭐⭐⭐ |
| **oauth2** | OAuth2 | ⭐⭐⭐⭐⭐ |
| **argon2** | 密码哈希 | ⭐⭐⭐⭐⭐ |

---

## 🔐 jsonwebtoken

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
}

fn main() {
    let claims = Claims { sub: "user123".to_string(), exp: 10000000000 };
    
    let token = encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret("secret".as_ref())
    ).unwrap();
    
    let decoded = decode::<Claims>(
        &token,
        &DecodingKey::from_secret("secret".as_ref()),
        &Validation::default()
    ).unwrap();
    
    println!("{:?}", decoded.claims);
}
```

---

## 🔒 argon2

```rust
use argon2::{Argon2, PasswordHasher, PasswordVerifier};
use argon2::password_hash::{rand_core::OsRng, SaltString};

fn main() {
    let password = b"password123";
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    
    let hash = argon2.hash_password(password, &salt).unwrap().to_string();
    println!("Hash: {}", hash);
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
