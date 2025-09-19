#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct Point { x: i32, y: i32 }

extern "C" fn add(p: Point) -> i32 { p.x + p.y }

#[test]
fn test_add() {
    assert_eq!(add(Point { x: 3, y: 4 }), 7);
}


