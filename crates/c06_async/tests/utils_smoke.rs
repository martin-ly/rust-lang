use std::time::Duration;

#[tokio::test]
async fn exec_strategy_basic_works() {
    let runner = c06_async::utils::ExecStrategyBuilder::new()
        .concurrency(2)
        .attempts(3)
        .start_delay(Duration::from_millis(10))
        .timeout(Duration::from_millis(200))
        .build();

    let out = runner
        .run(
            |attempt| async move {
                if attempt < 2 { Err(anyhow::anyhow!("transient")) } else { Ok::<_, anyhow::Error>(42) }
            },
            None::<fn(&anyhow::Error)->bool>,
        )
        .await
        .expect("should not error");

    assert_eq!(out, Some(42));
}


