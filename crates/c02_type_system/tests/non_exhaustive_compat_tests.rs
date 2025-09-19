#[non_exhaustive]
enum ApiEvent { Started }

fn handle(e: ApiEvent) -> &'static str {
    match e {
        ApiEvent::Started => "ok",
    }
}

#[test]
fn test_handle() { assert_eq!(handle(ApiEvent::Started), "ok"); }


