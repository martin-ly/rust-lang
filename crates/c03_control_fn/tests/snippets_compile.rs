mod async_control_flow_example {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/docs/snippets/async_control_flow_example.rs"));
}

#[tokio::test]
async fn test_async_control_flow_snippet_runs() {
    async_control_flow_example::run().await;
}


