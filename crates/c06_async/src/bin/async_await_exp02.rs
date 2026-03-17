use c06_async::r#await::await02::*;

fn main() {
    let runtime = tokio::runtime::Runtime::new().expect("创建 Tokio 运行时不应失败");
    runtime.block_on(process());
}
