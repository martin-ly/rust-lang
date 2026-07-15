mod async_control_flow_example {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/docs/tier_03_snippets/async_control_flow_example.rs"
    ));
}

#[tokio::test]
#[cfg_attr(miri, ignore)]
async fn test_async_control_flow_snippet_runs() {
    async_control_flow_example::run().await;
}
