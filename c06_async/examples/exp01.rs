use tokio; // 引入tokio库

#[tokio::main]
async fn main() {
    let result = async_function().await;
    println!("{}", result);
}

async fn async_function() -> String {
    "Hello from async function!".to_string()
}