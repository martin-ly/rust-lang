#[allow(dead_code)]
enum Msg { Ping, Pong, Data(i32) }

fn handle(m: Msg) -> &'static str {
    match m {
        Msg::Ping => "ping",
        Msg::Pong => "pong",
        Msg::Data(x) if x > 0 => "pos",
        Msg::Data(_) => "nonpos",
    }
}

fn describe(bytes: &[u8]) -> String {
    match bytes {
        head @ [0x7F, b'E', b'L', b'F', ..] => format!("ELF: {} bytes", head.len()),
        other => format!("raw: {} bytes", other.len()),
    }
}

fn touch_first(v: &mut Vec<i32>) {
    match v.as_mut_slice() {
        [x, ..] => *x += 1,
        [] => {}
    }
}

#[allow(dead_code)]
struct Config { host: String, port: u16, tls: bool }

fn port_enabled(c: &Config) -> bool {
    match c {
        Config { port, .. } if *port != 0 => true,
        _ => false,
    }
}

fn main() {
    assert_eq!(handle(Msg::Ping), "ping");
    assert_eq!(handle(Msg::Data(5)), "pos");
    assert_eq!(handle(Msg::Data(0)), "nonpos");

    let elf = [0x7F, b'E', b'L', b'F', 1, 2];
    assert!(describe(&elf).starts_with("ELF:"));

    let mut v = vec![1,2,3];
    touch_first(&mut v);
    assert_eq!(v[0], 2);

    let c = Config { host: "h".into(), port: 8080, tls: true };
    assert!(port_enabled(&c));
}


