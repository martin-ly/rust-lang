fn get_port(s: &str) -> Result<u16, String> {
    let Some(rest) = s.strip_prefix("port=") else { return Err("missing".into()); };
    let Ok(n) = rest.parse::<u16>() else { return Err("nan".into()); };
    Ok(n)
}

fn collect_even(nums: &[i32]) -> Vec<i32> {
    let mut out = Vec::new();
    for &n in nums {
        let true = n % 2 == 0 else { continue };
        out.push(n);
    }
    out
}

fn main() {
    assert_eq!(get_port("port=8080").unwrap(), 8080);
    assert!(get_port("p=1").is_err());
    assert_eq!(collect_even(&[1,2,4,5,6]), vec![2,4,6]);
}


