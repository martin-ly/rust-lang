//! Common 模块性能基准测试
//!
//! 测试项目中公共工具函数的性能，包括错误处理、类型操作和工具函数。

use common::CommonError;
use criterion::{Criterion, criterion_group, criterion_main};

/// 基准测试：错误创建与传播性能
/// 对应高频错误路径的优化验证
fn bench_error_creation(c: &mut Criterion) {
    c.bench_function("error_creation", |b| {
        b.iter(|| {
            let err = CommonError::Validation("验证失败：输入数据格式不正确".to_string());
            std::hint::black_box(err);
        });
    });
}

/// 基准测试：错误链构建性能
fn bench_error_chain(c: &mut Criterion) {
    c.bench_function("error_chain_building", |b| {
        b.iter(|| {
            let root = CommonError::Io("文件读取失败".to_string());
            let mid = CommonError::Validation(format!("数据解析失败: {}", root));
            let top = CommonError::Other(format!("请求处理失败: {}", mid));
            std::hint::black_box(top);
        });
    });
}

/// 基准测试：字符串截断工具函数
fn bench_string_truncation(c: &mut Criterion) {
    use common::utils::truncate_with_ellipsis;

    let long_string = "a".repeat(1000);
    c.bench_function("string_truncation", |b| {
        b.iter(|| {
            let result = truncate_with_ellipsis(&long_string, 50);
            std::hint::black_box(result);
        });
    });
}

/// 基准测试：字节格式化工具函数
fn bench_format_bytes(c: &mut Criterion) {
    use common::utils::format_bytes;

    c.bench_function("format_bytes", |b| {
        b.iter(|| {
            let _kb = format_bytes(1024);
            let _mb = format_bytes(1024 * 1024);
            let _gb = format_bytes(1024 * 1024 * 1024);
            let _tb = format_bytes(1024u64 * 1024 * 1024 * 1024);
            std::hint::black_box((_kb, _mb, _gb, _tb));
        });
    });
}

/// 基准测试：持续时间格式化
fn bench_format_duration(c: &mut Criterion) {
    use common::utils::format_duration;

    c.bench_function("format_duration", |b| {
        b.iter(|| {
            let _ns = format_duration(std::time::Duration::from_nanos(500));
            let _us = format_duration(std::time::Duration::from_micros(100));
            let _ms = format_duration(std::time::Duration::from_millis(250));
            let _s = format_duration(std::time::Duration::from_secs(90));
            std::hint::black_box((_ns, _us, _ms, _s));
        });
    });
}

/// 基准测试：Version 类型解析与比较
fn bench_version_operations(c: &mut Criterion) {
    use common::types::Version;

    c.bench_function("version_parse_and_compare", |b| {
        b.iter(|| {
            let v1 = Version::new(1, 2, 3);
            let _v2 = Version::new(1, 2, 4);
            let _eq = v1 == Version::new(1, 2, 3);
            std::hint::black_box(_eq);
        });
    });
}

/// 基准测试：分页结构体创建
fn bench_pagination_creation(c: &mut Criterion) {
    use common::types::{Paginated, Pagination};

    c.bench_function("pagination_creation", |b| {
        b.iter(|| {
            let items: Vec<i32> = (0..100).collect();
            let paginated = Paginated::new(items, 1000, Pagination::new(1, 20));
            std::hint::black_box(paginated);
        });
    });
}

criterion_group!(
    benches,
    bench_error_creation,
    bench_error_chain,
    bench_string_truncation,
    bench_format_bytes,
    bench_format_duration,
    bench_version_operations,
    bench_pagination_creation,
);
criterion_main!(benches);
