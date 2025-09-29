use std::time::Duration;

#[tokio::test]
async fn interval_stream_accumulates() {
    use tokio_stream::{wrappers::IntervalStream, StreamExt};
    let interval = tokio::time::interval(Duration::from_millis(1));
    let mut s = IntervalStream::new(interval).take(4);
    let mut acc = 0u64;
    let mut i = 0u64;
    while let Some(_) = s.next().await {
        acc += i;
        i += 1;
    }
    assert_eq!(acc, 0 + 1 + 2 + 3);
}


