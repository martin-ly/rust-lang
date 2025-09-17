use c10_networks::hello::HelloRequest;
use c10_networks::hello::greeter_client::GreeterClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = GreeterClient::connect("http://127.0.0.1:50051").await?;
    let resp = client
        .say_hello(tonic::Request::new(HelloRequest { name: "c10".into() }))
        .await?;
    println!("gRPC resp: {:?}", resp.into_inner());
    Ok(())
}
