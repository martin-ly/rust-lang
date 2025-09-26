fn demo_if_iflet_chain(input: Option<Result<i32, &'static str>>) -> i32 {
    if let Some(Ok(x)) = input {
        x
    } else if let Some(Err(_e)) = input {
        0
    } else {
        -1
    }
}

fn parse_port(s: &str) -> Result<u16, String> {
    let Some(rest) = s.strip_prefix("port=") else {
        return Err("缺少前缀 port=".into());
    };
    let Ok(num) = rest.parse::<u16>() else {
        return Err("端口不是 u16 数字".into());
    };
    Ok(num)
}

fn find_first_even(nums: &[i32]) -> Option<i32> {
    'outer: {
        for &n in nums {
            if n % 2 != 0 { continue; }
            break 'outer Some(n);
        }
        None
    }
}

fn index_of(nums: &[i32], target: i32) -> Option<usize> {
    for (i, &n) in nums.iter().enumerate() {
        if n == target { return Some(i); }
    }
    None
}

fn never_returns() -> ! {
    panic!("永不返回");
}

fn pick(a: Option<i32>) -> i32 {
    a.unwrap_or_else(|| never_returns())
}

fn main() {
    assert_eq!(demo_if_iflet_chain(Some(Ok(7))), 7);
    assert_eq!(demo_if_iflet_chain(Some(Err("e"))), 0);
    assert_eq!(demo_if_iflet_chain(None), -1);

    assert_eq!(parse_port("port=8080").unwrap(), 8080);
    assert!(parse_port("p=1").is_err());

    assert_eq!(find_first_even(&[1,3,5,6,7]), Some(6));
    assert_eq!(index_of(&[10,20,30], 20), Some(1));

    let _ = std::panic::catch_unwind(|| pick(None));
}
