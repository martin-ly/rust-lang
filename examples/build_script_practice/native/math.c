// 一个简单的 C 函数，用于演示 build.rs 如何编译原生库并链接到 Rust。
// This simple C function demonstrates how build.rs compiles a native library
// and links it into the Rust crate.

int mylib_add(int a, int b) {
    return a + b;
}
