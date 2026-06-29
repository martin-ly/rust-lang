//! chrono 时区转换与 Duration 计算示例
//! chrono timezone conversion and Duration calculation demonstration
//!
//! 运行: cargo run -p c07_process --example chrono_timezone_duration
use chrono::{DateTime, Duration, FixedOffset, Local, TimeZone, Utc};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🌍 chrono 时区与 Duration 示例\n");

    demonstrate_utc_to_local();
    demonstrate_fixed_offset()?;
    let _ = demonstrate_duration_arithmetic();
    demonstrate_negative_duration();
    demonstrate_std_duration_conversion();

    println!("\n✅ 演示完成");
    Ok(())
}

fn demonstrate_utc_to_local() {
    println!("--- UTC 与本地时区转换 ---");
    let utc_now = Utc::now();
    let local_now = utc_now.with_timezone(&Local);
    println!("  UTC 现在:  {utc_now}");
    println!("  本地现在: {local_now}");

    // 统一时区后才能比较
    assert_eq!(utc_now, local_now.with_timezone(&Utc));
    println!("  统一为 UTC 后相等: ✅");
}

fn demonstrate_fixed_offset() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n--- 固定偏移时区 ---");
    let sh = FixedOffset::east_opt(8 * 3600).ok_or("无法构造 +08:00 偏移")?;
    let ny = FixedOffset::west_opt(5 * 3600).ok_or("无法构造 -05:00 偏移")?;

    let flight = Utc.with_ymd_and_hms(2026, 6, 29, 14, 0, 0).single().ok_or("时间不存在")?;
    println!("  起飞 UTC:        {flight}");
    println!("  起飞 上海 +08:00: {}", flight.with_timezone(&sh));
    println!("  起飞 纽约 -05:00: {}", flight.with_timezone(&ny));
    Ok(())
}

fn demonstrate_duration_arithmetic() {
    println!("\n--- Duration 日期运算 ---");
    let start = Utc::now();
    let one_day = Duration::days(1);
    let two_hours = Duration::hours(2);
    let thirty_minutes = Duration::minutes(30);

    let deadline = start + one_day + two_hours + thirty_minutes;
    let remaining = deadline - start;

    println!("  当前:     {start}");
    println!("  截止时间: {deadline}");
    println!(
        "  剩余: {} 天 {} 小时 {} 分钟",
        remaining.num_days(),
        remaining.num_hours() % 24,
        remaining.num_minutes() % 60
    );
}

fn demonstrate_negative_duration() {
    println!("\n--- 负 Duration ---");
    let now = Utc::now();
    let past = now + Duration::seconds(-300);
    println!("  现在:      {now}");
    println!("  5 分钟前:  {past}");

    let diff = past - now;
    println!("  时间差:    {diff} (秒: {})", diff.num_seconds());
}

fn demonstrate_std_duration_conversion() {
    println!("\n--- chrono Duration 与 std Duration 互转 ---");
    let chrono_positive = Duration::milliseconds(1500);
    let std_dur = chrono_positive.to_std().expect("正值可安全转换");
    println!("  chrono -> std: {:?}", std_dur);

    let back = Duration::from_std(std_dur).expect("std Duration 在范围内");
    println!("  std -> chrono: {}", back);

    // 负值不能直接转 std::time::Duration
    let chrono_negative = Duration::seconds(-10);
    assert!(chrono_negative.to_std().is_err());
    println!("  负 Duration -> std: 转换失败 ✅ (符合预期)");

    // DateTime 与 UNIX 时间戳
    let unix = DateTime::UNIX_EPOCH;
    println!("  UNIX 纪元 (UTC): {unix}");
}
