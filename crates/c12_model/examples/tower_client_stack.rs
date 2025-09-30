#![allow(clippy::print_stdout)]

#[cfg(all(feature = "tokio-adapter", feature = "tower-examples"))]
#[tokio::main(flavor = "multi_thread")] 
async fn main() {
    use http::{Request, StatusCode};
    use hyper::{Body, Client};
    use std::time::Duration;
    use tower::{ServiceBuilder, ServiceExt, timeout::Timeout, limit::ConcurrencyLimitLayer, retry::{RetryLayer, Policy}};

    #[derive(Clone)]
    struct SimplePolicy;
    impl<E> Policy<Request<Body>, hyper::Response<Body>, E> for SimplePolicy {
        type Future = std::future::Ready<Self>;
        fn retry(&self, _req: &Request<Body>, result: Result<&hyper::Response<Body>, &E>) -> Option<Self::Future> {
            if let Ok(resp) = result { if resp.status() == StatusCode::REQUEST_TIMEOUT { return Some(std::future::ready(SimplePolicy)); } }
            None
        }
        fn clone_request(&self, req: &Request<Body>) -> Option<Request<Body>> { Some(req.clone()) }
    }

    let client = Client::new();
    let svc = ServiceBuilder::new()
        .layer(ConcurrencyLimitLayer::new(64))
        .layer(Timeout::new(Duration::from_secs(2)))
        .layer(RetryLayer::new(SimplePolicy))
        .service(client);

    let uri = "http://example.com".parse().unwrap();
    let req = Request::builder().method("GET").uri(uri).body(Body::empty()).unwrap();
    let res = svc.oneshot(req).await;
    println!("tower_client_stack: result={:?}", res.map(|r| r.status()));
}

#[cfg(not(all(feature = "tokio-adapter", feature = "tower-examples")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter,tower-examples\nExample: cargo run -p c12_model --example tower_client_stack --features tokio-adapter,tower-examples");
}


