# 文本处理

> **核心库**: regex, once_cell, lazy_static  
> **适用场景**: 正则表达式、字符串处理、Unicode 支持

---

## 📋 目录

- [文本处理](#文本处理)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [文本处理的挑战](#文本处理的挑战)
  - [🔍 正则表达式 (regex)](#-正则表达式-regex)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [简单匹配](#简单匹配)
      - [捕获组](#捕获组)
      - [多次匹配](#多次匹配)
      - [替换](#替换)
    - [高级特性](#高级特性)
      - [命名捕获组](#命名捕获组)
      - [Unicode 字符类](#unicode-字符类)
  - [🔐 懒加载静态变量](#-懒加载静态变量)
    - [once\_cell (推荐)](#once_cell-推荐)
    - [lazy\_static (传统方案)](#lazy_static-传统方案)
    - [OnceCell (运行时初始化)](#oncecell-运行时初始化)
  - [🌐 Unicode 处理](#-unicode-处理)
    - [unicode-normalization](#unicode-normalization)
    - [unicode-segmentation](#unicode-segmentation)
    - [大小写转换](#大小写转换)
  - [💡 最佳实践](#-最佳实践)
    - [1. 正则表达式性能优化](#1-正则表达式性能优化)
      - [✅ 推荐：缓存编译结果](#-推荐缓存编译结果)
      - [❌ 避免：循环中编译正则](#-避免循环中编译正则)
    - [2. 错误处理](#2-错误处理)
      - [✅ 推荐](#-推荐)
    - [3. Unicode 安全](#3-unicode-安全)
      - [✅ 推荐：使用字形簇](#-推荐使用字形簇)
      - [❌ 避免：直接切片](#-避免直接切片)
    - [4. 字符串构建](#4-字符串构建)
      - [✅ 推荐：预分配容量](#-推荐预分配容量)
  - [⚡ 性能优化](#-性能优化)
    - [基准测试结果](#基准测试结果)
    - [优化技巧](#优化技巧)
    - [实战示例](#实战示例)
  - [🔧 常见问题](#-常见问题)
    - [Q1: regex 支持哪些正则表达式语法？](#q1-regex-支持哪些正则表达式语法)
    - [Q2: 如何处理多行文本？](#q2-如何处理多行文本)
    - [Q3: 如何进行不区分大小写的匹配？](#q3-如何进行不区分大小写的匹配)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 文本处理的挑战

1. **正则表达式编译**: 每次编译正则表达式都有性能开销
2. **Unicode 复杂性**: 不同语言的字符编码和规范化
3. **字符串分配**: 频繁的字符串操作会导致内存分配
4. **线程安全**: 静态数据在多线程环境下的安全性

---

## 🔍 正则表达式 (regex)

### 核心特性

**regex** 是 Rust 中最强大的正则表达式库：

- ✅ **高性能**: 基于有限自动机，O(n) 时间复杂度
- ✅ **Unicode 原生支持**: 完整的 Unicode 类和属性
- ✅ **编译时优化**: 可以缓存编译结果
- ✅ **安全保证**: 不会造成 ReDoS (正则表达式拒绝服务)

### 基础用法

#### 简单匹配

```rust
use regex::Regex;

fn main() {
    let re = Regex::new(r"\d{4}-\d{2}-\d{2}").unwrap();
    
    let text = "今天是 2025-10-20";
    if re.is_match(text) {
        println!("找到日期格式!");
    }
    
    // 提取匹配
    if let Some(caps) = re.find(text) {
        println!("日期: {}", caps.as_str());
    }
}
```

#### 捕获组

```rust
use regex::Regex;

fn parse_email(email: &str) -> Option<(String, String)> {
    let re = Regex::new(r"^([a-zA-Z0-9._%+-]+)@([a-zA-Z0-9.-]+\.[a-zA-Z]{2,})$").unwrap();
    
    re.captures(email).map(|caps| {
        let user = caps.get(1).unwrap().as_str().to_string();
        let domain = caps.get(2).unwrap().as_str().to_string();
        (user, domain)
    })
}

fn main() {
    if let Some((user, domain)) = parse_email("alice@example.com") {
        println!("用户: {}, 域名: {}", user, domain);
    }
}
```

#### 多次匹配

```rust
use regex::Regex;

fn extract_numbers(text: &str) -> Vec<i32> {
    let re = Regex::new(r"\d+").unwrap();
    
    re.find_iter(text)
        .filter_map(|m| m.as_str().parse().ok())
        .collect()
}

fn main() {
    let numbers = extract_numbers("价格: 100元, 折扣: 20%, 最终: 80元");
    println!("数字: {:?}", numbers); // [100, 20, 80]
}
```

#### 替换

```rust
use regex::Regex;

fn main() {
    let re = Regex::new(r"\b(\w+)\b").unwrap();
    
    // 简单替换
    let result = re.replace_all("hello world", "***");
    println!("{}", result); // "*** ***"
    
    // 带函数的替换
    let result = re.replace_all("hello world", |caps: &regex::Captures| {
        caps[0].to_uppercase()
    });
    println!("{}", result); // "HELLO WORLD"
}
```

### 高级特性

#### 命名捕获组

```rust
use regex::Regex;

fn parse_log_entry(log: &str) -> Option<(String, String, String)> {
    let re = Regex::new(
        r"(?P<level>\w+)\s+(?P<timestamp>\d{4}-\d{2}-\d{2})\s+(?P<message>.+)"
    ).unwrap();
    
    re.captures(log).map(|caps| {
        let level = caps.name("level").unwrap().as_str().to_string();
        let timestamp = caps.name("timestamp").unwrap().as_str().to_string();
        let message = caps.name("message").unwrap().as_str().to_string();
        (level, timestamp, message)
    })
}

fn main() {
    let log = "ERROR 2025-10-20 Database connection failed";
    if let Some((level, timestamp, message)) = parse_log_entry(log) {
        println!("级别: {}, 时间: {}, 消息: {}", level, timestamp, message);
    }
}
```

#### Unicode 字符类

```rust
use regex::Regex;

fn main() {
    // 匹配任何 Unicode 字母
    let re = Regex::new(r"\p{L}+").unwrap();
    
    let text = "Hello 世界 мир";
    for mat in re.find_iter(text) {
        println!("{}", mat.as_str());
    }
    // 输出: Hello, 世界, мир
    
    // 匹配中文字符
    let re_chinese = Regex::new(r"\p{Han}+").unwrap();
    let chinese: Vec<_> = re_chinese
        .find_iter("这是中文 mixed with English")
        .map(|m| m.as_str())
        .collect();
    println!("{:?}", chinese); // ["这是中文"]
}
```

---

## 🔐 懒加载静态变量

### once_cell (推荐)

**once_cell** 是标准库即将采用的官方方案：

```rust
use once_cell::sync::Lazy;
use regex::Regex;

// 全局静态正则表达式 - 只编译一次
static EMAIL_REGEX: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$").unwrap()
});

static URL_REGEX: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"https?://[^\s]+").unwrap()
});

fn validate_email(email: &str) -> bool {
    EMAIL_REGEX.is_match(email)
}

fn extract_urls(text: &str) -> Vec<String> {
    URL_REGEX
        .find_iter(text)
        .map(|m| m.as_str().to_string())
        .collect()
}

fn main() {
    assert!(validate_email("test@example.com"));
    
    let urls = extract_urls("访问 https://example.com 或 http://rust-lang.org");
    println!("{:?}", urls);
}
```

### lazy_static (传统方案)

```rust
use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    static ref PHONE_REGEX: Regex = Regex::new(
        r"^1[3-9]\d{9}$"
    ).unwrap();
    
    static ref IP_REGEX: Regex = Regex::new(
        r"^(\d{1,3}\.){3}\d{1,3}$"
    ).unwrap();
}

fn validate_phone(phone: &str) -> bool {
    PHONE_REGEX.is_match(phone)
}

fn validate_ip(ip: &str) -> bool {
    IP_REGEX.is_match(ip)
}
```

### OnceCell (运行时初始化)

```rust
use once_cell::sync::OnceCell;
use regex::Regex;

static CONFIG_PATTERN: OnceCell<Regex> = OnceCell::new();

fn get_config_pattern() -> &'static Regex {
    CONFIG_PATTERN.get_or_init(|| {
        // 可以在运行时动态配置
        let pattern = std::env::var("PATTERN").unwrap_or_else(|_| r"\d+".to_string());
        Regex::new(&pattern).unwrap()
    })
}
```

---

## 🌐 Unicode 处理

### unicode-normalization

Unicode 规范化确保相同的字符有唯一表示：

```rust
use unicode_normalization::UnicodeNormalization;

fn main() {
    // NFD: 分解形式 (é = e + ́)
    let s1 = "café"; // 使用组合字符
    let nfd: String = s1.nfd().collect();
    println!("NFD: {} (字节数: {})", nfd, nfd.len());
    
    // NFC: 组合形式 (é = é)
    let nfc: String = s1.nfc().collect();
    println!("NFC: {} (字节数: {})", nfc, nfc.len());
    
    // 比较前应该规范化
    let s2 = "café"; // 使用单个字符 é
    assert_ne!(s1, s2); // 字节不同
    assert_eq!(
        s1.nfc().collect::<String>(),
        s2.nfc().collect::<String>()
    ); // 规范化后相同
}
```

### unicode-segmentation

按字形簇分割字符串：

```rust
use unicode_segmentation::UnicodeSegmentation;

fn main() {
    let s = "👨‍👩‍👧‍👦hello世界";
    
    // 按字形簇分割
    let graphemes: Vec<&str> = s.graphemes(true).collect();
    println!("字形簇: {:?}", graphemes);
    // ["👨‍👩‍👧‍👦", "h", "e", "l", "l", "o", "世", "界"]
    
    // 计数正确的字符数
    println!("字符数: {}", s.graphemes(true).count()); // 8
    println!("字节数: {}", s.len()); // 远大于 8
    
    // 按单词分割
    let words: Vec<&str> = s.split_word_bounds().collect();
    println!("单词: {:?}", words);
}
```

### 大小写转换

```rust
fn main() {
    let s = "Rust 编程";
    
    // 简单转换
    println!("大写: {}", s.to_uppercase()); // RUST 编程
    println!("小写: {}", s.to_lowercase()); // rust 编程
    
    // Unicode 大小写折叠（用于不区分大小写的比较）
    let s1 = "HELLO";
    let s2 = "hello";
    assert_ne!(s1, s2);
    
    // 使用 unicase crate 进行不区分大小写的比较
    use unicase::UniCase;
    assert_eq!(UniCase::new(s1), UniCase::new(s2));
}
```

---

## 💡 最佳实践

### 1. 正则表达式性能优化

#### ✅ 推荐：缓存编译结果

```rust
use once_cell::sync::Lazy;
use regex::Regex;

static DATE_PATTERN: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"\d{4}-\d{2}-\d{2}").unwrap()
});

fn process_dates(texts: &[&str]) -> Vec<String> {
    texts.iter()
        .filter_map(|text| DATE_PATTERN.find(text))
        .map(|m| m.as_str().to_string())
        .collect()
}
```

#### ❌ 避免：循环中编译正则

```rust
// 极度低效！
fn process_dates_bad(texts: &[&str]) -> Vec<String> {
    texts.iter()
        .filter_map(|text| {
            let re = Regex::new(r"\d{4}-\d{2}-\d{2}").unwrap(); // 每次都编译！
            re.find(text)
        })
        .map(|m| m.as_str().to_string())
        .collect()
}
```

### 2. 错误处理

#### ✅ 推荐

```rust
use regex::Regex;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ValidationError {
    #[error("无效的邮箱格式: {0}")]
    InvalidEmail(String),
    
    #[error("正则表达式编译失败: {0}")]
    RegexError(#[from] regex::Error),
}

pub fn validate_email(email: &str) -> Result<(), ValidationError> {
    let re = Regex::new(r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$")?;
    
    if re.is_match(email) {
        Ok(())
    } else {
        Err(ValidationError::InvalidEmail(email.to_string()))
    }
}
```

### 3. Unicode 安全

#### ✅ 推荐：使用字形簇

```rust
use unicode_segmentation::UnicodeSegmentation;

fn truncate_safely(s: &str, max_len: usize) -> String {
    s.graphemes(true)
        .take(max_len)
        .collect()
}

fn main() {
    let s = "👨‍👩‍👧‍👦hello";
    println!("{}", truncate_safely(s, 3)); // "👨‍👩‍👧‍👦he" (不会切断表情符号)
}
```

#### ❌ 避免：直接切片

```rust
// 危险！可能切断 UTF-8 字符
let s = "👨‍👩‍👧‍👦hello";
// let bad = &s[..3]; // 运行时 panic!
```

### 4. 字符串构建

#### ✅ 推荐：预分配容量

```rust
fn build_large_string(items: &[&str]) -> String {
    let total_len: usize = items.iter().map(|s| s.len()).sum();
    let mut result = String::with_capacity(total_len);
    
    for item in items {
        result.push_str(item);
    }
    
    result
}
```

---

## ⚡ 性能优化

### 基准测试结果

| 操作 | 性能 | 说明 |
|------|------|------|
| **Regex 编译** | 10-100 μs | 昂贵，应该缓存 |
| **Regex 匹配** | 10-100 ns/字符 | 线性时间 |
| **String 分配** | 100-1000 ns | 应尽量复用 |
| **Unicode 规范化** | 5-20 ns/字符 | 相对快速 |

### 优化技巧

1. **使用 `Lazy` 缓存正则表达式**
2. **预分配字符串容量**: `String::with_capacity()`
3. **使用 `&str` 而非 `String`**: 避免不必要的分配
4. **考虑 `Cow<str>`**: 按需克隆
5. **批量处理**: 减少函数调用开销

### 实战示例

```rust
use once_cell::sync::Lazy;
use regex::Regex;

static SANITIZE_REGEX: Lazy<Regex> = Lazy::new(|| {
    Regex::new(r"[^\w\s-]").unwrap()
});

/// 高性能的字符串清理
pub fn sanitize_filename(name: &str) -> String {
    // 1. 预分配
    let mut result = String::with_capacity(name.len());
    
    // 2. 使用缓存的正则表达式
    for segment in SANITIZE_REGEX.split(name) {
        if !segment.is_empty() {
            if !result.is_empty() {
                result.push('_');
            }
            result.push_str(segment);
        }
    }
    
    // 3. 限制长度
    if result.len() > 255 {
        result.truncate(255);
    }
    
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sanitize() {
        assert_eq!(sanitize_filename("hello world!"), "hello_world");
        assert_eq!(sanitize_filename("file@#$name.txt"), "file_name_txt");
    }
}
```

---

## 🔧 常见问题

### Q1: regex 支持哪些正则表达式语法？

**A**: regex 支持大部分标准正则语法，但**不支持**：

- 回溯引用 (`\1`, `\2`)
- 负向预查 (`(?!...)`)
- 正向预查 (`(?=...)`)

这是为了保证 O(n) 时间复杂度和防止 ReDoS。

### Q2: 如何处理多行文本？

**A**: 使用多行模式标志：

```rust
let re = Regex::new(r"(?m)^line").unwrap();
// (?m) 使 ^ 匹配每行开头
```

### Q3: 如何进行不区分大小写的匹配？

**A**: 使用 `(?i)` 标志：

```rust
let re = Regex::new(r"(?i)hello").unwrap();
assert!(re.is_match("HELLO"));
```

---

## 📚 延伸阅读

- [regex 官方文档](https://docs.rs/regex/)
- [Unicode 标准](https://www.unicode.org/)
- [正则表达式最佳实践](https://docs.rs/regex/latest/regex/#performance)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
