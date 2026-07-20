// 可扩展性与插件：trait插件接口示例
// Extensibility & Plugin: Trait Plugin Interface Example
trait Plugin {
    fn name(&self) -> &'static str;
    fn execute(&self, input: &str) -> String;
}

struct EchoPlugin;

impl Plugin for EchoPlugin {
    fn name(&self) -> &'static str { "Echo" }
    fn execute(&self, input: &str) -> String {
        format!("[Echo] {}", input)
    }
}

fn main() {
    let plugin = EchoPlugin;
    println!("{}", plugin.execute("hello"));
} 