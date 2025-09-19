use core::ops::Deref;

struct UserId(u64);
type UserIdAlias = u64;

impl Deref for UserId {
    type Target = u64;
    fn deref(&self) -> &Self::Target { &self.0 }
}

#[repr(transparent)]
struct TransparentU64(u64);

fn takes_u64(x: u64) -> u64 { x + 1 }

#[test]
fn test_alias_equivalence() {
    let a: UserIdAlias = 5;
    assert_eq!(takes_u64(a), 6);
}

#[test]
fn test_newtype_not_subtype() {
    let id = UserId(7);
    assert_eq!(takes_u64(*id), 8);
}

#[test]
fn test_transparent_repr_still_distinct_type() {
    let t = TransparentU64(9);
    assert_eq!(takes_u64(t.0), 10);
}


