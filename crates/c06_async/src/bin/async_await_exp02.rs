use c06_async::r#await::await02::*;

fn main() {
    let runtime = tokio::runtime::Runtime::new().unwrap();
    runtime.block_on(process());
}

