//! 权威来源: https://releases.rs/docs/1.95.0/
//! 权威source: https://releases.rs/docs/1.95.0/
//! 运行方式:
//! Run way :
//! cargo run --example bool_try_from_demo -p c02_type_system
//! ```

// ==================== 示例 1: 基础用法 ====================

/// `bool::try_from` 基础转换
fn demo_basic_try_from() {
    println!("--- bool::try_from 基础 ---");

    // 0 → false
    let b0: bool = bool::try_from(0u8).unwrap();
    println!("  bool::try_from(0u8) = {}", b0);
    assert!(!b0);

    // 1 → true
    let b1: bool = bool::try_from(1u8).unwrap();
    println!("  bool::try_from(1u8) = {}", b1);
    assert!(b1);

    // 2 → Err
    let result = bool::try_from(2u8);
    println!("  bool::try_from(2u8) = {:?}", result);
    assert!(result.is_err());

    // 所有整数类型都支持: u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    let from_i32 = bool::try_from(0i32);
    println!("  bool::try_from(0i32) = {:?}", from_i32);
    assert_eq!(from_i32, Ok(false));

    let from_u64 = bool::try_from(1u64);
    println!("  bool::try_from(1u64) = {:?}", from_u64);
    assert_eq!(from_u64, Ok(true));
}

// ==================== 示例 2: FFI 边界 — C 布尔值转换 ====================

fn demo_ffi_boolean() {
    println!("\n--- FFI: C 整数标志安全转换 ---");

    // 模拟从 C 接收的整数标志
    fn get_flag_from_c() -> u8 {
        1 // C 代码返回 1 表示 true
    }

    fn get_invalid_flag_from_c() -> u8 {
        42 // 某些 C 代码错误地返回了 42
    }

    // 安全转换
    match bool::try_from(get_flag_from_c()) {
        Ok(flag) => println!("  C flag (1) -> bool: {}", flag),
        Err(_) => println!("  C flag 无效"),
    }

    // 捕获无效值
    match bool::try_from(get_invalid_flag_from_c()) {
        Ok(flag) => println!("  C flag (42) -> bool: {}", flag),
        Err(_) => println!("  C flag (42) 无效 ❌ — 数据损坏或协议不匹配"),
    }

    // 与旧写法对比
    let raw = get_invalid_flag_from_c();
    let unsafe_bool = raw != 0; // 旧写法: 42 被静默当作 true!
    println!("  危险: raw != 0 会把 42 静默转为 true = {}", unsafe_bool);
    println!("  安全: try_from 会拒绝 42，防止隐藏数据错误 ✅");
}

// ==================== 示例 3: 数据库 / 配置文件解析 ====================

/// 从数据库或配置文件中读取整数字段并验证
/// from database or in field and
fn demo_config_parsing() {
    println!("\n--- 配置解析: 数据库/JSON 整数字段 ---");

    #[derive(Debug, PartialEq)]
    struct AppConfig {
        debug_mode: bool,
        enable_cache: bool,
        strict_validation: bool,
    }

    // 模拟从数据库读取的配置值
    let db_values: [(&str, i32); 3] = [
        ("debug_mode", 1),
        ("enable_cache", 0),
        ("strict_validation", 1),
    ];

    let mut config = AppConfig {
        debug_mode: false,
        enable_cache: false,
        strict_validation: false,
    };

    for (key, value) in db_values {
        match bool::try_from(value) {
            Ok(flag) => {
                match key {
                    "debug_mode" => config.debug_mode = flag,
                    "enable_cache" => config.enable_cache = flag,
                    "strict_validation" => config.strict_validation = flag,
                    _ => {}
                }
                println!("  {} = {} ✅", key, flag);
            }
            Err(_) => {
                println!("  {} = {} ❌ 无效布尔值", key, value);
            }
        }
    }

    println!("  解析结果: {:?}", config);
    assert!(config.debug_mode);
    assert!(!config.enable_cache);
    assert!(config.strict_validation);
}

// ==================== 示例 4: 网络协议 — 二进制标志位 ====================

/// 解析网络协议中的标志字节
/// network protocol in mark
fn demo_network_protocol() {
    println!("\n--- 网络协议: 二进制标志解析 ---");

    // 模拟一个 8 位标志字节
    let flags: u8 = 0b0000_0101; // bits 0 和 2 被设置

    // 提取单个位并安全转换
    let bit0 = bool::try_from(flags & 1).unwrap();
    let bit1 = bool::try_from((flags >> 1) & 1).unwrap();
    let bit2 = bool::try_from((flags >> 2) & 1).unwrap();
    let bit7 = bool::try_from((flags >> 7) & 1).unwrap();

    println!("  标志字节: 0b{:08b}", flags);
    println!("  bit 0 (ACK): {}", bit0);
    println!("  bit 1 (SYN): {}", bit1);
    println!("  bit 2 (FIN): {}", bit2);
    println!("  bit 7 (RSV): {}", bit7);

    assert!(bit0);
    assert!(!bit1);
    assert!(bit2);
    assert!(!bit7);

    // 验证: 提取结果只能是 0 或 1，所以 unwrap 是安全的
    println!("  ✅ 位运算结果只有 0/1，try_from 永远不会失败");
}

// ==================== 示例 5: 与 as bool / != 0 的对比 ====================

/// 对比安全转换与危险转换
/// to conversion and conversion
fn demo_comparison() {
    println!("\n--- 安全 vs 危险转换对比 ---");

    let values = [0u8, 1, 2, 255];

    println!(
        "  {:>5} | {:>15} | {:>15} | {:>20}",
        "值", "try_from", "v != 0", "as bool (编译错)"
    );
    println!("  {:-^5}-+-{:-^15}-+-{:-^15}-+-{:-^20}", "", "", "", "");

    for &v in &values {
        let safe = bool::try_from(v);
        let dangerous = v != 0;
        println!(
            "  {:>5} | {:>15?} | {:>15} | {:>20}",
            v, safe, dangerous, "—"
        );
    }

    println!("\n  结论:");
    println!("    - try_from: 拒绝 2 和 255，防止隐藏错误 ✅");
    println!("    - v != 0:   静默接受所有非零值，包括 2/255 ❌");
    println!("    - 在 FFI、协议解析、配置读取中，try_from 更安全");
}

// ==================== 示例 6: 泛型函数中的使用 ====================

fn demo_generic_conversion() {
    println!("\n--- 泛型: 整数到 bool 的通用解析 ---");

    fn parse_bool_flag<T>(value: T) -> Result<bool, &'static str>
    where
        bool: TryFrom<T>,
    {
        bool::try_from(value).map_err(|_| "invalid boolean value: expected 0 or 1")
    }

    let flags: Vec<Result<bool, _>> = vec![
        parse_bool_flag(0u8),
        parse_bool_flag(1u16),
        parse_bool_flag(0i32),
        parse_bool_flag(1u64),
        parse_bool_flag(2u8), // 无效
    ];

    for (i, flag) in flags.iter().enumerate() {
        match flag {
            Ok(b) => println!("  flag[{}] = {} ✅", i, b),
            Err(e) => println!("  flag[{}] 错误: {} ❌", i, e),
        }
    }

    assert_eq!(flags[0], Ok(false));
    assert_eq!(flags[1], Ok(true));
    assert_eq!(flags[4], Err("invalid boolean value: expected 0 or 1"));
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `bool: TryFrom<{{integer}}>` 专题演示\n");

    demo_basic_try_from();
    demo_ffi_boolean();
    demo_config_parsing();
    demo_network_protocol();
    demo_comparison();
    demo_generic_conversion();

    println!("\n✅ `bool::try_from` 演示完成！");
    println!("   关键要点:");
    println!("   - 0 → false, 1 → true，其他值返回 Err");
    println!("   - 支持所有整数类型: u8/u16/u32/u64/u128/usize/i8/i16/i32/i64/i128/isize");
    println!("   - 适用场景: FFI 边界、数据库/配置解析、网络协议标志");
    println!("   - 优势: 拒绝 2/255 等非法值，避免 v != 0 的静默错误");
    println!("   - 对比: 比 match v {{ 0 => false, 1 => true, _ => error }} 更简洁");
}
