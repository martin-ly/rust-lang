fn read_number(s: &str) -> Result<i32, String> {
    let num: i32 = s.trim().parse().map_err(|_| "parse".to_string())?;
    Ok(num)
}

fn opt_chain(x: Option<i32>) -> Option<i32> {
    let y = Some(1)?;
    Some(x? + y)
}

fn sum3(a: Result<i32, &'static str>, b: Result<i32, &'static str>) -> Result<i32, &'static str> {
    Ok(a? + b?)
}

fn main() {
    assert_eq!(read_number(" 42 ").unwrap(), 42);
    assert!(read_number("x").is_err());

    assert_eq!(opt_chain(Some(2)), Some(3));
    assert_eq!(opt_chain(None), None);

    assert_eq!(sum3(Ok(2), Ok(3)).unwrap(), 5);
}


