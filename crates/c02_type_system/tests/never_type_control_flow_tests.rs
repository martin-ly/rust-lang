fn diverge() -> ! { panic!("never returns") }

fn choose(flag: bool) -> i32 {
    if flag { 1 } else { diverge() }
}

#[test]
fn test_choose_true() {
    assert_eq!(choose(true), 1);
}


