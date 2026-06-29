//! 插件架构：静态 Trait Registry 示例
//!
//! 本示例展示如何在不依赖动态链接库的情况下，通过 trait + Vec<Box<dyn Trait>>
//! 构建一个可扩展的插件系统。所有插件在编译期确定，类型安全由 Rust 编译器保证。

use std::collections::HashMap;

/// 插件接口：每个插件提供一个唯一名称与执行逻辑。
pub trait GreetPlugin: Send + Sync {
    fn name(&self) -> &'static str;
    fn greet(&self, name: &str) -> String;
}

/// 插件注册表：持有所有已注册的插件并提供统一调度接口。
pub struct PluginRegistry {
    plugins: Vec<Box<dyn GreetPlugin>>,
    index: HashMap<&'static str, usize>,
}

impl PluginRegistry {
    pub fn new() -> Self {
        Self {
            plugins: Vec::new(),
            index: HashMap::new(),
        }
    }

    /// 注册一个插件。若名称已存在则返回旧插件。
    pub fn register(&mut self, plugin: Box<dyn GreetPlugin>) -> Option<Box<dyn GreetPlugin>> {
        let name = plugin.name();
        if let Some(&idx) = self.index.get(name) {
            return Some(std::mem::replace(&mut self.plugins[idx], plugin));
        }
        self.index.insert(name, self.plugins.len());
        self.plugins.push(plugin);
        None
    }

    /// 按名称执行单个插件。
    pub fn run(&self, name: &str, input: &str) -> Option<String> {
        self.index
            .get(name)
            .and_then(|&idx| self.plugins.get(idx))
            .map(|p| p.greet(input))
    }

    /// 执行所有插件并返回结果列表。
    pub fn run_all(&self, input: &str) -> Vec<String> {
        self.plugins.iter().map(|p| p.greet(input)).collect()
    }

    pub fn names(&self) -> Vec<&'static str> {
        self.plugins.iter().map(|p| p.name()).collect()
    }
}

impl Default for PluginRegistry {
    fn default() -> Self {
        Self::new()
    }
}

struct English;
impl GreetPlugin for English {
    fn name(&self) -> &'static str {
        "english"
    }
    fn greet(&self, name: &str) -> String {
        format!("Hello, {}!", name)
    }
}

struct Spanish;
impl GreetPlugin for Spanish {
    fn name(&self) -> &'static str {
        "spanish"
    }
    fn greet(&self, name: &str) -> String {
        format!("¡Hola, {}!", name)
    }
}

struct Japanese;
impl GreetPlugin for Japanese {
    fn name(&self) -> &'static str {
        "japanese"
    }
    fn greet(&self, name: &str) -> String {
        format!("こんにちは, {}!", name)
    }
}

fn main() {
    let mut registry = PluginRegistry::new();
    registry.register(Box::new(English));
    registry.register(Box::new(Spanish));
    registry.register(Box::new(Japanese));

    println!("registered plugins: {:?}", registry.names());

    for greeting in registry.run_all("Rust") {
        println!("{}", greeting);
    }

    if let Some(out) = registry.run("spanish", "plugin architecture") {
        println!("selected: {}", out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_registry_runs_all_plugins() {
        let mut registry = PluginRegistry::new();
        registry.register(Box::new(English));
        registry.register(Box::new(Spanish));
        let out = registry.run_all("World");
        assert_eq!(out.len(), 2);
        assert!(out.iter().any(|s| s.contains("Hello")));
        assert!(out.iter().any(|s| s.contains("Hola")));
    }

    #[test]
    fn static_registry_selects_by_name() {
        let mut registry = PluginRegistry::new();
        registry.register(Box::new(Japanese));
        assert_eq!(
            registry.run("japanese", "Rust"),
            Some("こんにちは, Rust!".to_string())
        );
    }
}
