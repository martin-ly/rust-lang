//! regex 常见验证场景示例
//!
//! 展示如何使用 `regex` crate 完成常见文本验证与解析任务：
//! - 邮箱格式检查
//! - URL 结构解析
//! - IPv4 地址校验
//! - 常用日志格式字段解析
//!
//! 注意：以下正则为教学示例，生产环境应使用专用库（如 `url`、`email_address`）
//! 或经过充分测试的严格模式。
//!
//! 运行方式：
//! cargo run -p c07_process --example regex_common_validation

use regex::Regex;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 regex 常见验证场景示例\n");

    // 1. 邮箱格式验证（简化教学版）
    let email_re = Regex::new(r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$")?;
    let emails = [
        "user@example.com",
        "rust.lang+tag@docs.rs",
        "invalid-email",
        "@missing-local.org",
    ];
    println!("邮箱验证:");
    for email in emails {
        println!("  {email:<30} -> {}", if email_re.is_match(email) { "✅" } else { "❌" });
    }

    // 2. URL 结构解析（捕获 scheme、host、port、path）
    let url_re = Regex::new(r"^(?<scheme>https?)://(?<host>[^:/]+)(?::(?<port>\d+))?(?<path>/.*)?$")?;
    let urls = [
        "https://doc.rust-lang.org/book/",
        "http://localhost:8080/api/v1/users",
        "https://crates.io",
        "ftp://files.example.com/file.txt",
    ];
    println!("\nURL 解析:");
    for url in urls {
        match url_re.captures(url) {
            Some(caps) => {
                let scheme = &caps["scheme"];
                let host = &caps["host"];
                let port = caps.name("port").map(|m| m.as_str()).unwrap_or("default");
                let path = caps.name("path").map(|m| m.as_str()).unwrap_or("/");
                println!("  {url}");
                println!("    scheme={scheme}, host={host}, port={port}, path={path}");
            }
            None => println!("  {url} -> ❌ 不匹配 HTTP/HTTPS URL 结构"),
        }
    }

    // 3. IPv4 地址校验
    let ipv4_re = Regex::new(r"^(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(?:\.(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}$")?;
    let ips = ["192.168.1.1", "255.255.255.255", "10.0.0.256", "127.0.0.1"];
    println!("\nIPv4 校验:");
    for ip in ips {
        println!("  {ip:<20} -> {}", if ipv4_re.is_match(ip) { "✅" } else { "❌" });
    }

    // 4. 日志字段解析（Common Log Format 简化版）
    // 示例: 127.0.0.1 - alice [10/Oct/2023:13:55:36 -0700] "GET /index.html HTTP/1.1" 200 2326
    let log_re = Regex::new(
        r#"^(?<ip>\S+)\s+\S+\s+(?<user>\S+)\s+\[(?<time>[^\]]+)\]\s+"(?<method>\S+)\s+(?<path>\S+)\s+(?<proto>\S+)"\s+(?<status>\d{3})\s+(?<size>\d+|-)$"#,
    )?;
    let log_line = r#"127.0.0.1 - alice [10/Oct/2023:13:55:36 -0700] "GET /index.html HTTP/1.1" 200 2326"#;
    println!("\n日志解析:");
    if let Some(caps) = log_re.captures(log_line) {
        println!("  原始日志: {log_line}");
        println!("    IP     : {}", &caps["ip"]);
        println!("    User   : {}", &caps["user"]);
        println!("    Time   : {}", &caps["time"]);
        println!("    Method : {}", &caps["method"]);
        println!("    Path   : {}", &caps["path"]);
        println!("    Proto  : {}", &caps["proto"]);
        println!("    Status : {}", &caps["status"]);
        println!("    Size   : {}", &caps["size"]);
    }

    // 5. 从用户输入构建正则时的错误处理示范
    println!("\n用户输入正则的错误处理:");
    let user_input = r"(invalid("; // 不完整的分组
    match Regex::new(user_input) {
        Ok(_) => println!("  编译成功"),
        Err(e) => println!("  编译失败（应失败）: {e}"),
    }

    println!("\n✅ regex 常见验证场景示例完成");
    Ok(())
}
