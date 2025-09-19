#[derive(Debug)]
enum Msg {
    Ping,
    SetName(String),
    Data { id: u32, payload: Option<Vec<u8>> },
}

fn handle(msg: Msg) -> String {
    match msg {
        Msg::Ping => "pong".into(),
        Msg::SetName(name) if !name.is_empty() => format!("name={}", name),
        Msg::Data { id, payload: Some(p) } if !p.is_empty() => format!("id={},len={}", id, p.len()),
        Msg::Data { id, payload: None } => format!("id={},none", id),
        _ => "ignored".into(),
    }
}

fn main() {
    println!("{}", handle(Msg::Ping));
    println!("{}", handle(Msg::SetName(String::from("Alice"))));
    println!("{}", handle(Msg::Data { id: 1, payload: Some(vec![1,2,3]) }));
}


