#![feature(gen_blocks, yield_expr)]
fn foo() -> impl Iterator<Item = i32> {
    gen {
        yield 1;
        yield 2;
    }
}
fn main() {
    for x in foo() {
        println!("{}", x);
    }
}
