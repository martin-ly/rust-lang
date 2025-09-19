fn elided_rule_1(x: &i32) -> &i32 { x }
fn explicit_same<'a>(x: &'a i32) -> &'a i32 { x }

fn first_word<'a>(s: &'a str) -> &'a str {
    match s.find(' ') { Some(i) => &s[..i], None => s }
}

fn apply_for_all_lifetimes<F>(f: F) -> usize
where
    F: for<'a> Fn(&'a str) -> usize,
{
    let a = String::from("hello");
    let b = String::from("world");
    f(&a) + f(&b)
}

#[test]
fn test_lifetime_elision_and_explicit() {
    let v = 7;
    assert_eq!(*elided_rule_1(&v), 7);
    assert_eq!(*explicit_same(&v), 7);
}

#[test]
fn test_first_word() {
    assert_eq!(first_word("abc def"), "abc");
    assert_eq!(first_word("nodef"), "nodef");
}

#[test]
fn test_hrtb_apply() {
    let n = apply_for_all_lifetimes(|x| x.len());
    assert_eq!(n, "hello".len() + "world".len());
}


