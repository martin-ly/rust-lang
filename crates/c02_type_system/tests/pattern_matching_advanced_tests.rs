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

#[test]
fn test_handle_variants() {
    assert_eq!(handle(Msg::Ping), "pong");
    assert_eq!(handle(Msg::SetName(String::from(""))), "ignored");
    assert_eq!(handle(Msg::SetName(String::from("Bob"))), "name=Bob");
    assert_eq!(handle(Msg::Data { id: 7, payload: None }), "id=7,none");
    assert_eq!(handle(Msg::Data { id: 1, payload: Some(vec![0,1]) }), "id=1,len=2");
}


