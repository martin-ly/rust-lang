// 配置与环境管理：多环境配置读取示例
// Config & Environment Management: Multi-Env Config Example
trait ConfigSource {
    fn get(&self, key: &str) -> Option<String>;
}

struct EnvConfig;

impl ConfigSource for EnvConfig {
    fn get(&self, key: &str) -> Option<String> {
        std::env::var(key).ok()
    }
}

fn main() {
    std::env::set_var("APP_MODE", "production");
    let config = EnvConfig;
    println!("APP_MODE={}", config.get("APP_MODE").unwrap());
} 