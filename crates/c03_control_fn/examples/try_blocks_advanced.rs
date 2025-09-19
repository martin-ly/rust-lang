#[derive(Debug, PartialEq)]
#[allow(dead_code)]
enum AppErr { Parse, Io }

fn parse_num(s: &str) -> Result<i32, AppErr> {
    s.parse::<i32>().map_err(|_| AppErr::Parse)
}

fn sum2(a: Result<i32, &'static str>, b: Result<i32, &'static str>) -> Result<i32, &'static str> {
    a.and_then(|x| b.map(|y| x + y))
}

fn add_from_str(x: &str, y: &str) -> Result<i32, AppErr> {
    parse_num(x).and_then(|a| parse_num(y).map(|b| a + b))
}

fn head_plus_parsed(rest: &[&str]) -> Option<i32> {
    rest.get(0).and_then(|s| s.parse::<i32>().ok())
}

fn main() {
    assert_eq!(sum2(Ok(2), Ok(3)).unwrap(), 5);
    assert_eq!(add_from_str("2", "3").unwrap(), 5);
    assert_eq!(add_from_str("x", "3"), Err(AppErr::Parse));
    assert_eq!(head_plus_parsed(&["7"]), Some(7));
    assert_eq!(head_plus_parsed(&[]), None);
}


