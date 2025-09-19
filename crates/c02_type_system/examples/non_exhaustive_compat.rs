#[non_exhaustive]
enum ApiEvent {
    Started,
}

fn handle(e: ApiEvent) -> &'static str {
    match e {
        ApiEvent::Started => "ok",
    }
}

fn main() { println!("{}", handle(ApiEvent::Started)); }


