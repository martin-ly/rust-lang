
/*
1. 初始对象 (Initial Object)
定义:
    在一个范畴中，初对象是一个对象，从该对象可以唯一地发出态射到所有其他对象。
    换句话说，初对象是“发送者”，它可以通过唯一的态射映射到任何其他对象。
Rust中的类比:
    Option<T>类型的None变体可以被视为初对象。
    因为对于任何类型T，都可以通过None来表示一个缺失的值。
    None可以被视为从初对象发出的态射，表示没有值的状态。
*/
#[allow(dead_code)]
pub fn to_option<T>(_: T) -> Option<T> {
    None
}
