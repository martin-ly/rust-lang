//! 字符串算法示例
//!
//! 本示例展示C08算法模块的字符串算法：
//! - KMP算法
//! - Rabin-Karp算法
//! - 字符串匹配
//!
//! 运行方式:
//! ```bash
//! cargo run --example string_algorithms_demo
//! ```

fn main() {
    println!("🚀 字符串算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. KMP算法
    println!("\n📊 KMP算法:");
    println!("{}", "-".repeat(60));
    let text = "ABABDABACDABABCABCABAB";
    let pattern = "ABABCABCAB";
    let result = kmp_search(text, pattern);
    println!("文本: {}", text);
    println!("模式: {}", pattern);
    match result {
        Some(pos) => println!("找到匹配，起始位置: {}", pos),
        None => println!("未找到匹配"),
    }

    // 2. 简单字符串匹配
    println!("\n📊 简单字符串匹配:");
    println!("{}", "-".repeat(60));
    let text = "Hello, World!";
    let pattern = "World";
    let result = naive_search(text, pattern);
    println!("文本: {}", text);
    println!("模式: {}", pattern);
    match result {
        Some(pos) => println!("找到匹配，起始位置: {}", pos),
        None => println!("未找到匹配"),
    }

    // 3. 算法说明
    println!("\n💡 字符串算法说明:");
    println!("{}", "-".repeat(60));
    println!("  KMP: O(n+m) 时间复杂度，利用前缀信息");
    println!("  Rabin-Karp: 基于哈希的字符串匹配");
    println!("  简单匹配: O(n*m) 时间复杂度，但实现简单");

    println!("\n✅ 字符串算法演示完成！");
}

/// KMP算法的简化实现（演示概念）
fn kmp_search(text: &str, pattern: &str) -> Option<usize> {
    let text: Vec<char> = text.chars().collect();
    let pattern: Vec<char> = pattern.chars().collect();
    let n = text.len();
    let m = pattern.len();

    if m == 0 {
        return Some(0);
    }
    if m > n {
        return None;
    }

    let lps = compute_lps(&pattern);

    let mut i = 0; // text的索引
    let mut j = 0; // pattern的索引

    while i < n {
        if text[i] == pattern[j] {
            i += 1;
            j += 1;
        }

        if j == m {
            return Some(i - j);
        } else if i < n && text[i] != pattern[j] {
            if j != 0 {
                j = lps[j - 1];
            } else {
                i += 1;
            }
        }
    }

    None
}

/// 计算最长公共前缀后缀（LPS）数组
fn compute_lps(pattern: &[char]) -> Vec<usize> {
    let m = pattern.len();
    let mut lps = vec![0; m];
    let mut len = 0;
    let mut i = 1;

    while i < m {
        if pattern[i] == pattern[len] {
            len += 1;
            lps[i] = len;
            i += 1;
        } else if len != 0 {
            len = lps[len - 1];
        } else {
            lps[i] = 0;
            i += 1;
        }
    }

    lps
}

/// 简单的字符串匹配算法（暴力搜索）
fn naive_search(text: &str, pattern: &str) -> Option<usize> {
    let text: Vec<char> = text.chars().collect();
    let pattern: Vec<char> = pattern.chars().collect();
    let n = text.len();
    let m = pattern.len();

    if m == 0 {
        return Some(0);
    }
    if m > n {
        return None;
    }

    for i in 0..=n - m {
        let mut j = 0;
        while j < m && text[i + j] == pattern[j] {
            j += 1;
        }
        if j == m {
            return Some(i);
        }
    }

    None
}
