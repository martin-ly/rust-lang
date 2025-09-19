fn parse(input: Option<Result<&str, &'static str>>) -> &'static str {
    if let Some(Ok(s)) = input {
        if s.is_empty() { "empty" } else { "ok" }
    } else if let Some(Err(_)) = input {
        "err"
    } else {
        "none"
    }
}

fn drain_until_neg(mut v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::new();
    while let Some(x) = v.pop() {
        if x < 0 { break; }
        out.push(x);
    }
    out
}

fn main() {
    assert_eq!(parse(Some(Ok(""))), "empty");
    assert_eq!(parse(Some(Ok("x"))), "ok");
    assert_eq!(parse(Some(Err("e"))), "err");
    assert_eq!(parse(None), "none");

    assert_eq!(drain_until_neg(vec![1,2,3,-1,9]), vec![3,2,1]);
}


