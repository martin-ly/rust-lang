#[derive(Debug)]
#[allow(dead_code)]
enum Token { Ident(String), Number(i64), Symbol(char) }

fn classify(tok: Token) -> String {
    match tok {
        name @ Token::Ident(_) => format!("ident: {:?}", name),
        n @ Token::Number(_) => format!("number: {:?}", n),
        Token::Symbol(c) if c.is_ascii_punctuation() => "punct".into(),
        Token::Symbol(_) => "symbol".into(),
    }
}

#[derive(Debug)]
#[allow(dead_code)]
struct Point { x: i32, y: i32 }

fn on_axis(p: Point) -> bool {
    match p {
        Point { x: 0, .. } | Point { y: 0, .. } => true,
        _ => false,
    }
}

#[allow(dead_code)]
fn head_tail(nums: &[i32]) -> Option<(i32, i32)> {
    match nums {
        [first, .., last] => Some((*first, *last)),
        [one] => Some((*one, *one)),
        _ => None,
    }
}

#[allow(dead_code)]
fn is_ok_even(x: Result<i32, ()>) -> bool {
    matches!(x, Ok(n) if n % 2 == 0)
}

fn main() {
    assert!(matches!(classify(Token::Ident("x".into())).as_str(), s if s.starts_with("ident:")));
    assert_eq!(classify(Token::Number(10)), "number: Number(10)");
    assert_eq!(classify(Token::Symbol(',')), "punct");

    assert!(on_axis(Point { x: 0, y: 5 }));
    assert!(!on_axis(Point { x: 1, y: 2 }));

    assert_eq!(head_tail(&[1,2,3,4]), Some((1,4)));
    assert_eq!(head_tail(&[9]), Some((9,9)));

    assert!(is_ok_even(Ok(4)));
    assert!(!is_ok_even(Ok(3)));
}


