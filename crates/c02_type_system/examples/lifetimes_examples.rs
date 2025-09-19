//! 生命周期进阶示例：省略规则/显式标注/HRTB/'static

fn elided_rule_1(x: &i32) -> &i32 { x }

fn explicit_same<'a>(x: &'a i32) -> &'a i32 { x }

struct Holder<'a> { r: &'a str }

impl<'a> Holder<'a> {
    fn get(&self) -> &str { self.r }
}

// 返回引用必须源自传入引用或更长活期；以下返回入参的子切片。
fn first_word<'a>(s: &'a str) -> &'a str {
    match s.find(' ') { Some(i) => &s[..i], None => s }
}

// HRTB：对任意 'a 都可接受的函数/闭包
fn apply_for_all_lifetimes<F>(f: F) -> usize
where
    F: for<'a> Fn(&'a str) -> usize,
{
    let a = String::from("hello");
    let b = String::from("world");
    f(&a) + f(&b)
}

fn main() {
    let v = 10;
    let _ = elided_rule_1(&v);
    let _ = explicit_same(&v);

    let s = String::from("rust ninety");
    let h = Holder { r: &s };
    println!("holder: {}", h.get());

    println!("first word: {}", first_word(&s));

    let count = apply_for_all_lifetimes(|x| x.len());
    println!("count: {}", count);
}


