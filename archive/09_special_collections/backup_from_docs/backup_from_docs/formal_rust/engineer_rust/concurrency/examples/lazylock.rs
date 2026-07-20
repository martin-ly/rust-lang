// 1.88 新特性：LazyLock 并发初始化
use std::sync::LazyLock;

static CONFIG: LazyLock<String> = LazyLock::new(|| "init".to_string());

fn main() {
    println!("CONFIG = {}", *CONFIG);
} 