use    c02_type_system::primitive_types::compound_types::array::define::*;
#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;


fn main() {
    test_array();
    test_array_str();
    test_array_string();
    test_array_clone_str();
    test_array_clone_string();
    test_array_copy();
    test_array_clone();
}
