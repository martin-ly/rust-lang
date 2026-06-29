//! chrono 日期时间解析与格式化示例
//! chrono date/time parsing and formatting demonstration
//!
//! 运行: cargo run -p c07_process --example chrono_parse_format
use chrono::{DateTime, FixedOffset, Local, NaiveDate, NaiveDateTime, Utc};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🕒 chrono 解析与格式化示例\n");

    demonstrate_parse_with_offset()?;
    demonstrate_naive_parse()?;
    demonstrate_formatting()?;
    demonstrate_iso8601()?;

    println!("\n✅ 演示完成");
    Ok(())
}

fn demonstrate_parse_with_offset() -> Result<(), Box<dyn std::error::Error>> {
    println!("--- 带偏移量字符串解析 ---");
    let input = "2026-06-29T21:50:42+08:00";
    let dt: DateTime<FixedOffset> =
        DateTime::parse_from_str(input, "%Y-%m-%dT%H:%M:%S%:z")?;
    println!("  输入: {input}");
    println!("  解析结果: {dt}");
    println!("  对应 UTC: {}", dt.with_timezone(&Utc));
    Ok(())
}

fn demonstrate_naive_parse() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n--- Naive 类型解析 ---");
    let input = "2026-06-29 21:50:42";
    let naive = NaiveDateTime::parse_from_str(input, "%Y-%m-%d %H:%M:%S")?;
    println!("  输入: {input}");
    println!("  NaiveDateTime: {naive}");

    // 显式声明为本地时间后再转换
    let local = naive.and_local_timezone(Local).single().ok_or("歧义或不存在的时间")?;
    println!("  本地时间: {local}");
    println!("  UTC 时间: {}", local.with_timezone(&Utc));
    Ok(())
}

fn demonstrate_formatting() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n--- 自定义格式化输出 ---");
    let now = Local::now();
    println!("  默认: {now}");
    println!("  中文格式: {}", now.format("%Y年%m月%d日 %H:%M:%S"));
    println!("  紧凑格式: {}", now.format("%Y%m%d-%H%M%S"));
    println!("  RFC 3339: {}", now.to_rfc3339());

    let date = NaiveDate::from_ymd_opt(2026, 6, 29).ok_or("非法日期")?;
    println!("  仅日期: {}", date.format("%A, %B %d, %Y"));
    Ok(())
}

fn demonstrate_iso8601() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n--- ISO 8601 / RFC 3339 互操作 ---");
    let utc = Utc::now();
    let rfc = utc.to_rfc3339();
    println!("  UTC -> RFC 3339: {rfc}");

    let parsed: DateTime<Utc> = rfc.parse()?;
    println!("  RFC 3339 -> UTC: {parsed}");
    assert_eq!(utc.timestamp(), parsed.timestamp());
    Ok(())
}
