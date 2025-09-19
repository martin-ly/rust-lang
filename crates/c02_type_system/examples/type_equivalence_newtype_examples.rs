use core::ops::Deref;

struct UserId(u64);           // newtype：与 u64 在类型上区分
type UserIdAlias = u64;       // type alias：与 u64 等价

impl Deref for UserId {
    type Target = u64;
    fn deref(&self) -> &Self::Target { &self.0 }
}

#[repr(transparent)]
struct TransparentU64(u64);   // 透明表示：FFI/ABI 兼容场景

fn takes_u64(x: u64) -> u64 { x + 1 }

fn main() {
    let id = UserId(10);
    let a: UserIdAlias = 10;
    let t = TransparentU64(10);

    // alias 等价于 u64，可直接传入
    println!("alias -> {}", takes_u64(a));

    // newtype 不是子类型，不能直接当 u64 传入；需解包或解引用
    println!("newtype -> {}", takes_u64(*id));

    // 透明表示不改变类型系统规则，依然需要显式取内部值
    println!("transparent -> {}", takes_u64(t.0));
}


