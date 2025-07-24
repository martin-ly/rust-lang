// 国际化与本地化：本地化适配器示例
// i18n & l10n: Localizer Adapter Example
trait Localizer {
    fn translate(&self, key: &str, locale: &str) -> String;
}

struct SimpleLocalizer;

impl Localizer for SimpleLocalizer {
    fn translate(&self, key: &str, locale: &str) -> String {
        match (key, locale) {
            ("hello", "zh-CN") => "你好".to_string(),
            ("hello", "en-US") => "Hello".to_string(),
            _ => key.to_string(),
        }
    }
}

fn main() {
    let loc = SimpleLocalizer;
    println!("{}", loc.translate("hello", "zh-CN"));
    println!("{}", loc.translate("hello", "en-US"));
} 