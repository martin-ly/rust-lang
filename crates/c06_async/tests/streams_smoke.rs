use std::time::Duration;

#[tokio::test]
#[cfg_attr(miri, ignore)]
async fn interval_stream_accumulates() {
    use tokio_stream::StreamExt;
    use tokio_stream::wrappers::IntervalStream;
    let interval = tokio::time::interval(Duration::from_millis(1));
    let mut s = IntervalStream::new(interval).take(4);
    let mut acc = 0u64;
    let mut i = 0u64;
    while s.next().await.is_some() {
        acc += i;
        i += 1;
    }
    assert_eq!(acc, 1 + 2 + 3);
}
