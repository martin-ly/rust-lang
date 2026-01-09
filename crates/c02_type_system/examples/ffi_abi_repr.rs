#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct Point { x: i32, y: i32 }

extern "C" fn add(p: Point) -> i32 { p.x + p.y }

fn main() {
    let p = Point { x: 1, y: 2 };
    println!("{}", add(p));
}
