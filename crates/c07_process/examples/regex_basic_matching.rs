//! regex 基础匹配与捕获示例
//!
//! 展示 `regex` crate 的核心 API：
//! - `Regex::new` / `RegexBuilder`
//! - 捕获组与命名捕获
//! - 替换与迭代器
//! - `RegexSet` 多模式匹配
//!
//! 运行方式：
//! cargo run -p c07_process --example regex_basic_matching

use regex::{Regex, RegexBuilder, RegexSet};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 regex 基础匹配与捕获示例\n");

    // 1. 简单存在性判断
    let date_re = Regex::new(r"\d{4}-\d{2}-\d{2}")?;
    let text = "Release date: 2026-06-29";
    println!("文本: {text}");
    println!("  是否匹配日期格式: {}", date_re.is_match(text));

    // 2. find / find_iter：位置与所有匹配
    let word_re = Regex::new(r"[a-zA-Z_][a-zA-Z0-9_]*")?;
    print!("  标识符列表: ");
    for m in word_re.find_iter("let foo1 = bar2 + baz3;") {
        print!("{} ", m.as_str());
    }
    println!();

    // 3. 捕获组与命名捕获
    let iso_re = Regex::new(r"(?<year>\d{4})-(?<month>\d{2})-(?<day>\d{2})")?;
    let caps = iso_re
        .captures("Date: 2026-06-29")
        .ok_or("no date captured")?;
    println!(
        "  命名捕获: year={}, month={}, day={}",
        &caps["year"], &caps["month"], &caps["day"]
    );

    // 4. RegexBuilder：运行时配置匹配语义
    let case_insensitive = RegexBuilder::new(r"rust")
        .case_insensitive(true)
        .build()?;
    println!(
        "  大小写不敏感匹配 'RustLang': {}",
        case_insensitive.is_match("RustLang")
    );

    // 5. 替换：字符串与闭包
    let digits = Regex::new(r"\d+")?;
    let masked = digits.replace_all("ID: 12345, code: 42", "***");
    println!("  替换数字为掩码: {masked}");

    let incremented = digits.replace_all("a1b2c3", |caps: &regex::Captures| {
        caps[0].parse::<i32>().unwrap_or(0).wrapping_add(1).to_string()
    });
    println!("  数字加 1: {incremented}");

    // 6. RegexSet：多模式同时匹配
    let set = RegexSet::new(&[
        r"^\d+$",          // 纯数字
        r"^[a-zA-Z]+$",    // 纯字母
        r"^[a-zA-Z0-9_]+$", // 标识符
    ])?;
    let input = "abc123";
    let matched: Vec<usize> = set.matches(input).into_iter().collect();
    println!("  '{input}' 在多模式集合中的命中索引: {matched:?}");

    // 7. 分词：split / splitn
    let sep = Regex::new(r"\s*,\s*")?;
    let parts: Vec<&str> = sep.split("foo, bar ,baz").collect();
    println!("  按逗号切分: {parts:?}");

    let limited: Vec<&str> = sep.splitn("a, b, c, d", 3).collect();
    println!("  限制为 3 段: {limited:?}");

    println!("\n✅ regex 基础匹配与捕获示例完成");
    Ok(())
}
