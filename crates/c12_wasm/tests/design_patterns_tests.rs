//! # 设计模式测试
//!
//! 测试 ecosystem_examples 中的设计模式实现

#[cfg(test)]
mod tests {
    use c12_wasm::ecosystem_examples::design_patterns::*;

    // ========================================================================
    // 工厂模式测试
    // ========================================================================

    #[test]
    fn test_factory_pattern() {
        use factory::*;

        // 测试 HTML 渲染器
        let html_renderer = create_renderer(RendererType::Html);
        let html_output = html_renderer.render("test content");
        assert_eq!(html_output, "<div>test content</div>");

        // 测试 Markdown 渲染器
        let md_renderer = create_renderer(RendererType::Markdown);
        let md_output = md_renderer.render("test content");
        assert_eq!(md_output, "**test content**");
    }

    #[test]
    fn test_wasm_renderer_factory() {
        use factory::WasmRendererFactory;

        let factory = WasmRendererFactory::new();
        let output = factory.render_html("Hello WASM");
        assert_eq!(output, "<div>Hello WASM</div>");
    }

    // ========================================================================
    // 建造者模式测试
    // ========================================================================

    #[test]
    fn test_builder_pattern() {
        use builder::*;

        let config = ConfigBuilder::new()
            .url("https://api.example.com".to_string())
            .timeout(5000)
            .retries(3)
            .build();

        assert!(config.is_ok());
        let config = config.unwrap();
        assert_eq!(config.timeout(), 5000);
        assert_eq!(config.retries(), 3);
        assert_eq!(config.url(), "https://api.example.com");
    }

    #[test]
    fn test_builder_with_defaults() {
        use builder::*;

        let config = ConfigBuilder::new()
            .url("https://test.com".to_string())
            .build();

        assert!(config.is_ok());
        let config = config.unwrap();
        // 应该使用默认值
        assert_eq!(config.timeout(), 3000);
        assert_eq!(config.retries(), 1);
    }

    #[test]
    fn test_builder_missing_required_field() {
        use builder::*;

        let config = ConfigBuilder::new().timeout(5000).build();

        // 没有设置必需的 URL，应该失败
        assert!(config.is_err());
    }

    // ========================================================================
    // 单例模式测试
    // ========================================================================

    // Note: Singleton pattern tests are skipped in integration tests
    // as they use global state and wasm-bindgen exports.
    // See unit tests in src/ecosystem_examples.rs for singleton tests.

    // ========================================================================
    // 观察者模式测试
    // ========================================================================

    // Note: Observer pattern uses JavaScript functions and cannot be tested
    // in Rust-only integration tests. See examples in demo/index.html for usage.

    // ========================================================================
    // 策略模式测试
    // ========================================================================

    // Note: Strategy pattern is tested through the Sorter WASM interface
    // See examples/07_design_patterns.rs for usage

    // ========================================================================
    // 适配器模式测试
    // ========================================================================

    // Note: Adapter pattern is tested through the WASM interface
    // See examples/07_design_patterns.rs for usage

    // ========================================================================
    // 集成测试：多个模式组合使用
    // ========================================================================

    #[test]
    fn test_patterns_integration() {
        use builder::*;
        use factory::*;

        // 1. 使用建造者创建HTTP配置
        let config = ConfigBuilder::new()
            .url("https://test.com".to_string())
            .timeout(3000)
            .retries(2)
            .build()
            .unwrap();

        // 2. 使用工厂创建渲染器
        let factory = WasmRendererFactory::new();
        let content = format!("Config timeout: {}ms", config.timeout());
        let html = factory.render_html(&content);

        // 验证结果
        assert!(html.contains("3000ms"));
        assert!(html.contains("<div>"));
    }
}
