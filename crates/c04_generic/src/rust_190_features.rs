//! Rust 1.90 语言特性示例合集（中文详注）
//!
//! 本文件聚焦“1.90 可用的语言特性全集”的最小可编译示例，
//! 遵循：高可读命名、细致注释、边界清晰与零成本抽象。

#![allow(unused)]

// 1) 基础语法与所有权 -------------------------------------------------------
pub fn basics_and_ownership() -> i32 {
	let immutable_answer: i32 = 42;
	let mut counter: i32 = 0; // 最小可变域：仅在需要可变时使用 mut
	counter += 1;
	immutable_answer + counter
}

// 2) 借用与生命周期 -----------------------------------------------------------
// 生命周期通常可省略，这里展示显式写法以教学。
pub fn first<'a>(x: &'a str, _y: &'a str) -> &'a str {
	x
}

// 3) 泛型与 Trait 约束 --------------------------------------------------------
pub fn max_of_two<T>(a: T, b: T) -> T
where
	T: Ord,
{
	if a >= b { a } else { b }
}

// 4) 关联类型与 GATs ----------------------------------------------------------
// 经典迭代器关联类型示例
pub trait SimpleIterator {
	type Item;
	fn next_item(&mut self) -> Option<Self::Item>;
}

pub struct Counter {
	current: u32,
	end: u32,
}

impl Counter {
	pub fn new(end: u32) -> Self { Self { current: 0, end } }
}

impl SimpleIterator for Counter {
	type Item = u32;
	fn next_item(&mut self) -> Option<Self::Item> {
		if self.current < self.end {
			let v = self.current;
			self.current += 1;
			Some(v)
		} else {
			None
		}
	}
}

// 5) 常量泛型（固定容量容器） --------------------------------------------------
pub struct RingBuffer<T, const N: usize> {
	data: [Option<T>; N],
	head: usize,
	tail: usize,
	size: usize,
}

impl<T, const N: usize> RingBuffer<T, N> {
	pub fn new() -> Self {
		Self { data: array_init::array_init(|_| None), head: 0, tail: 0, size: 0 }
	}
	pub fn push(&mut self, value: T) -> Result<(), T> {
		if self.size == N { return Err(value); }
		self.data[self.tail] = Some(value);
		self.tail = (self.tail + 1) % N;
		self.size += 1;
		Ok(())
	}
	pub fn pop(&mut self) -> Option<T> {
		if self.size == 0 { return None; }
		let v = self.data[self.head].take();
		self.head = (self.head + 1) % N;
		self.size -= 1;
		v
	}
}

// 6) 模式匹配与解构 -----------------------------------------------------------
#[derive(Debug, PartialEq, Eq)]
pub enum Shape {
	Circle { radius: u32 },
	Rect { w: u32, h: u32 },
}

pub fn area(s: &Shape) -> u32 {
	match s {
		Shape::Circle { radius } => (3 * radius * radius), // 粗略演示
		Shape::Rect { w, h } => w * h,
	}
}

// 7) 错误处理：Result 与 anyhow/thiserror -------------------------------------
#[derive(thiserror::Error, Debug)]
pub enum AppError {
	#[error("invalid input: {0}")]
	InvalidInput(String),
}

pub fn parse_positive(input: &str) -> Result<u32, AppError> {
	let v: i64 = input.parse().map_err(|_| AppError::InvalidInput(input.into()))?;
	if v < 0 { return Err(AppError::InvalidInput(input.into())); }
	Ok(v as u32)
}

pub fn fallible_flow(input: &str) -> anyhow::Result<u32> {
	let v = parse_positive(input)?;
	Ok(v + 1)
}

// 7.1) 分层错误建模：thiserror + From + anyhow 上下文 -----------------------------
#[derive(thiserror::Error, Debug)]
pub enum IoLayerError {
	#[error("io failed: {0}")]
	Io(#[from] std::io::Error),
}

#[derive(thiserror::Error, Debug)]
pub enum ConfigLayerError {
	#[error("invalid config: {0}")]
	Invalid(String),
	#[error(transparent)]
	Io(#[from] IoLayerError),
}

pub fn read_config_len(path: &str) -> anyhow::Result<usize> {
	use std::fs;
	let s = fs::read_to_string(path).map_err(IoLayerError::from)?;
	if s.trim().is_empty() { return Err(ConfigLayerError::Invalid("empty".into()).into()); }
	Ok(s.len())
}

// 8) 并发：Send/Sync 及 rayon（数据并行） -------------------------------------
pub fn parallel_square_sum(values: &[i64]) -> i64 {
	use rayon::prelude::*;
	values.par_iter().map(|v| v * v).sum()
}

// 9) 迭代器与 itertools --------------------------------------------------------
pub fn sum_of_pairs<I>(iter: I) -> i32
where
	I: IntoIterator<Item = (i32, i32)>,
{
	use itertools::Itertools;
	iter
		.into_iter()
		.map(|(a, b)| a + b)
		.filter(|s| *s > 0)
		.sum()
}

// 9.1) 迭代器高级组合：无装箱 RPITIT 管道与装箱对比 ------------------------------
pub trait Pipeline {
	fn pipeline(&self) -> impl Iterator<Item = i32>;
}

pub struct Data(Vec<i32>);

impl Data {
	pub fn new(v: Vec<i32>) -> Self { Self(v) }
}

impl Pipeline for Data {
	fn pipeline(&self) -> impl Iterator<Item = i32> {
		self.0.iter().copied().map(|x| x * 2).filter(|x| x % 3 == 0)
	}
}

pub fn boxed_pipeline(v: &[i32]) -> Box<dyn Iterator<Item = i32> + '_> {
	Box::new(v.iter().copied().map(|x| x * 2).filter(|x| x % 3 == 0))
}

// 10) 并发共享状态：Arc<Mutex<T>> 与 Arc<RwLock<T>> ------------------------------
pub mod shared_state_demo {
	use std::sync::{Arc, Mutex, RwLock};
	use std::thread;

	pub fn mutex_counter(num_threads: usize, iters: usize) -> i32 {
		let counter = Arc::new(Mutex::new(0i32));
		let mut handles = Vec::new();
		for _ in 0..num_threads {
			let c = Arc::clone(&counter);
			handles.push(thread::spawn(move || {
				for _ in 0..iters {
					let mut guard = c.lock().unwrap();
					*guard += 1;
				}
			}));
		}
		for h in handles { h.join().unwrap(); }
		*counter.lock().unwrap()
	}

	pub fn rwlock_accumulate(readers: usize, writers: usize, write_iters: usize) -> i32 {
		let value = Arc::new(RwLock::new(0i32));
		let mut handles = Vec::new();
		for _ in 0..writers {
			let v = Arc::clone(&value);
			handles.push(thread::spawn(move || {
				for _ in 0..write_iters {
					*v.write().unwrap() += 1;
				}
			}));
		}
		for _ in 0..readers {
			let v = Arc::clone(&value);
			handles.push(thread::spawn(move || {
				let _ = *v.read().unwrap(); // 模拟读多
			}));
		}
		for h in handles { h.join().unwrap(); }
		*value.read().unwrap()
	}
}

// 11) Unsafe/FFI 最小闭环 -------------------------------------------------------
#[repr(C)]
pub struct CPoint { pub x: i32, pub y: i32 }

pub fn distance_sq_safe(p: *const CPoint) -> Option<i32> {
	if p.is_null() { return None; }
	unsafe {
		let r = &*p;
		Some(r.x * r.x + r.y * r.y)
	}
}

// 提供安全封装层：从 Rust 所有权创建原始指针并在本函数生命周期内使用
pub fn distance_sq_owned(p: &CPoint) -> i32 {
	let ptr: *const CPoint = p as *const CPoint;
	distance_sq_safe(ptr).unwrap()
}

// 10) 属性与 cfg ----------------------------------------------------------------
#[inline]
pub fn add_inline(a: i32, b: i32) -> i32 { a + b }

// 10.4) 模块可见性与路径组织 ------------------------------------------------------
// 展示 pub, pub(crate), pub(super) 与重导出
pub mod visibility_demo {
	pub(crate) mod inner {
		pub(super) fn add(a: i32, b: i32) -> i32 { a + b }
		pub const NAME: &str = "inner";
	}

	pub fn parent_sum() -> i32 { inner::add(2, 3) }

	// 门面：对外暴露稳定命名
	pub use inner::NAME as INNER_NAME;
}

// 10.4.1) API 门面化：内部版本重命名到稳定公共 API -------------------------------
mod api_internal_v1 {
	#[derive(Debug, Clone, PartialEq)]
	pub struct User { pub id: u64, pub name: String }

	impl User {
		pub fn display(&self) -> String { format!("{}: {}", self.id, self.name) }
	}
}

mod api_internal_v2 {
	#[derive(Debug, Clone, PartialEq)]
	pub struct User { pub id: u64, pub username: String }

	impl User {
		pub fn display(&self) -> String { format!("{}: {}", self.id, self.username) }
	}
}

// 对外稳定 API：根据策略选择导出版本（示例选 v2）
pub mod api { pub use super::api_internal_v2::*; }

// 10.5) GATs：带生命周期的关联类型迭代器 -----------------------------------------
// 10.5) GATs：带生命周期的关联类型迭代器 -----------------------------------------
// 场景：在 trait 中定义一个依赖输入借用生命周期的关联类型
pub trait BufLines {
	// 关联类型依赖 'a：消费者获得与输入同寿命的迭代器
	type Lines<'a>: Iterator<Item = &'a str>
	where
		Self: 'a;

	fn lines(&self) -> Self::Lines<'_>;
}

pub struct TextBuf(String);

impl TextBuf {
	pub fn new(s: &str) -> Self { Self(s.to_owned()) }
}

impl BufLines for TextBuf {
	type Lines<'a> = std::str::Split<'a, char> where Self: 'a;

	fn lines(&self) -> Self::Lines<'_> {
		self.0.split('\n')
	}
}

// 10.6) 关联类型的 where 约束示例 ----------------------------------------------
pub trait Serializer {
	type Output;
	fn serialize<T>(&self, value: &T) -> Self::Output
	where
		T: serde::Serialize;
}

pub struct JsonSerializer;

impl Serializer for JsonSerializer {
	type Output = String;

	fn serialize<T>(&self, value: &T) -> Self::Output
	where
		T: serde::Serialize,
	{
		serde_json::to_string(value).expect("json serialize")
	}
}

// 11) 关联常量、关联常量默认值与常量泛型结合 -----------------------------------
pub trait HasThreshold {
	const THRESHOLD: i32 = 10; // 关联常量可有默认值

	fn is_large(&self) -> bool;
}

impl HasThreshold for i32 {
	fn is_large(&self) -> bool { *self >= Self::THRESHOLD }
}

pub struct FixedArray<T, const N: usize> {
	pub data: [T; N],
}

impl<const N: usize> HasThreshold for FixedArray<i32, N> {
	// 覆盖默认阈值
	const THRESHOLD: i32 = (N as i32) * 2;

	fn is_large(&self) -> bool { (self.data.iter().sum::<i32>()) >= Self::THRESHOLD }
}

// 12) RPITIT：在 trait 方法返回位置使用 impl Trait（稳定） ------------------------
pub trait NumberSource {
	// 返回位置 impl Trait：实现方可自由选择具体迭代器类型
	fn numbers(&self, start: i32, count: usize) -> impl Iterator<Item = i32>;
}

pub struct RangeSource;

impl NumberSource for RangeSource {
	fn numbers(&self, start: i32, count: usize) -> impl Iterator<Item = i32> {
		(start..).take(count)
	}
}

// 13) HRTB：for<'a> 对闭包/函数指针进行高阶生命周期约束 ---------------------------
pub fn apply_to_slices<F>(f: F) -> usize
where
	F: for<'a> Fn(&'a [u8]) -> usize,
{
	let a: [u8; 3] = [1, 2, 3];
	let b: [u8; 2] = [9, 9];
	// f 必须适用于任意生命周期的切片
	f(&a) + f(&b)
}

// 14) Trait 上行转换（trait object upcasting） -----------------------------------
// 子 trait 扩展父 trait，可将 &dyn SubTrait 上行转换为 &dyn SuperTrait
pub trait Logger {
	fn log(&self) -> String;
}

pub trait AdvancedLogger: Logger {
	fn detail(&self) -> String;
}

pub struct ConsoleLogger;

impl Logger for ConsoleLogger {
	fn log(&self) -> String { "log".into() }
}

impl AdvancedLogger for ConsoleLogger {
	fn detail(&self) -> String { "detail".into() }
}

// 上行转换：Box 与 Arc
pub fn upcast_box(adv: Box<dyn AdvancedLogger>) -> Box<dyn Logger> { adv }

pub fn upcast_arc(adv: std::sync::Arc<dyn AdvancedLogger>) -> std::sync::Arc<dyn Logger> {
	adv
}

// 15) 声明宏与常见派生（derive） -------------------------------------------------
#[derive(Debug, Clone, PartialEq)]
pub struct Point { pub x: i32, pub y: i32 }

// 一个简单的声明宏：生成 Vec
#[macro_export]
macro_rules! make_vec {
	( $( $x:expr ),* $(,)? ) => {
		vec![ $( $x ),* ]
	};
}

// 15.1) 宏批量实现：为多种数值类型批量实现同一 trait ---------------------------
pub trait ToI64 { fn to_i64(self) -> i64; }

#[macro_export]
macro_rules! impl_to_i64_for {
	( $( $t:ty ),+ $(,)? ) => {
		$( impl ToI64 for $t { fn to_i64(self) -> i64 { self as i64 } } )+
	};
}

impl_to_i64_for!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);

// 15.2) 过程宏集成示例 -----------------------------------------------------------
use proc_macro_derive::{Display, WithId};

#[derive(Debug, Clone, Display, WithId)]
pub struct User {
    pub id: u64,
    pub name: String,
}

// 16) async + 泛型 + 返回位置 impl Future ---------------------------------------
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

pub fn async_add_generic<T>(a: T, b: T) -> impl Future<Output = i32>
where
	T: Into<i32>,
{
	async move { a.into() + b.into() }
}

fn noop_clone(_: *const ()) -> RawWaker { RawWaker::new(std::ptr::null(), &NOOP_VTABLE) }
fn noop(_: *const ()) {}
fn noop_wake(_: *const ()) {}
static NOOP_VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop_wake, noop_wake, noop);

fn create_noop_waker() -> Waker { unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &NOOP_VTABLE)) } }

pub fn block_on<F>(future: F) -> F::Output
where
	F: Future,
{
	let mut fut = Box::pin(future);
	let waker = create_noop_waker();
	let mut cx = Context::from_waker(&waker);
	loop {
		match Pin::as_mut(&mut fut).poll(&mut cx) {
			Poll::Ready(val) => break val,
			Poll::Pending => std::thread::yield_now(), // 纯演示用的最小轮询
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_basics_and_ownership() {
		assert_eq!(basics_and_ownership(), 43);
	}

	#[test]
	fn test_first_lifetime() {
		let a = String::from("x");
		let b = String::from("y");
		let r = first(&a, &b);
		assert_eq!(r, "x");
	}

	#[test]
	fn test_max_of_two() {
		assert_eq!(max_of_two(3, 5), 5);
		assert_eq!(max_of_two("a", "b"), "b");
	}

	#[test]
	fn test_counter_iterator() {
		let mut c = Counter::new(3);
		assert_eq!(c.next_item(), Some(0));
		assert_eq!(c.next_item(), Some(1));
		assert_eq!(c.next_item(), Some(2));
		assert_eq!(c.next_item(), None);
	}

	#[test]
	fn test_ring_buffer_const_generics() {
		let mut rb: RingBuffer<i32, 2> = RingBuffer::new();
		assert!(rb.push(1).is_ok());
		assert!(rb.push(2).is_ok());
		assert!(rb.push(3).is_err());
		assert_eq!(rb.pop(), Some(1));
		assert_eq!(rb.pop(), Some(2));
		assert_eq!(rb.pop(), None);
	}

	#[test]
	fn test_area_match() {
		assert_eq!(area(&Shape::Rect { w: 3, h: 4 }), 12);
	}

	#[test]
	fn test_error_flow() {
		assert_eq!(parse_positive("10").unwrap(), 10);
		assert!(parse_positive("-1").is_err());
		assert_eq!(fallible_flow("10").unwrap(), 11);
	}

	#[test]
	fn test_error_modeling_layers() {
		let not_exist = read_config_len("__no_such_file__");
		assert!(not_exist.is_err());
	}

	#[test]
	fn test_parallel_square_sum() {
		let v = vec![1, 2, 3, 4];
		assert_eq!(parallel_square_sum(&v), 30);
	}

	#[test]
	fn test_sum_of_pairs() {
		let v = vec![(1, 2), (-5, 1), (3, 3)];
		assert_eq!(sum_of_pairs(v), 9);
	}

	#[test]
	fn test_iter_pipelines() {
		let d = Data::new(vec![1, 2, 3, 4, 5, 6]);
		let a: Vec<i32> = d.pipeline().collect();
		let b: Vec<i32> = boxed_pipeline(&[1, 2, 3, 4, 5, 6]).collect();
		assert_eq!(a, b);
	}

	#[test]
	fn test_shared_state_mutex_rwlock() {
		let total = shared_state_demo::mutex_counter(8, 1000);
		assert_eq!(total, 8000);
		let w = 1000;
		let sum = shared_state_demo::rwlock_accumulate(16, 4, w);
		assert_eq!(sum, 4 * w as i32);
	}

	#[test]
	fn test_unsafe_ffi_minimal() {
		let p = CPoint { x: 3, y: 4 };
		assert_eq!(distance_sq_owned(&p), 25);
		let null_ptr: *const CPoint = std::ptr::null();
		assert!(distance_sq_safe(null_ptr).is_none());
	}

	#[test]
	fn test_associated_consts_and_const_generics() {
		assert!((12i32).is_large());
		let arr = FixedArray { data: [1, 2, 3, 4] };
		assert!(arr.is_large()); // 阈值为 N*2 = 8，和为 10
	}

	#[test]
	fn test_rpitit_trait_method_iterator() {
		let src = RangeSource;
		let sum: i32 = src.numbers(5, 4).sum();
		assert_eq!(sum, 5 + 6 + 7 + 8);
	}

	#[test]
	fn test_hrtbs_for_all_slices() {
		let total = apply_to_slices(|s| s.len());
		assert_eq!(total, 3 + 2);
	}

	#[test]
	fn test_trait_upcasting_refs() {
		let logger = ConsoleLogger;
		let adv: &dyn AdvancedLogger = &logger;
		let base: &dyn Logger = adv; // 上行转换到父 trait 对象
		assert_eq!(base.log(), "log");
		assert_eq!(adv.detail(), "detail");
	}

	#[test]
	fn test_trait_upcasting_box_arc() {
		use std::sync::Arc;
		let boxed: Box<dyn AdvancedLogger> = Box::new(ConsoleLogger);
		let up_box: Box<dyn Logger> = upcast_box(boxed);
		assert_eq!(up_box.log(), "log");

		let arc_adv: Arc<dyn AdvancedLogger> = Arc::new(ConsoleLogger);
		let arc_base: Arc<dyn Logger> = upcast_arc(arc_adv);
		assert_eq!(arc_base.log(), "log");
	}

	#[test]
	fn test_visibility_and_reexport() {
		assert_eq!(visibility_demo::parent_sum(), 5);
		assert_eq!(visibility_demo::INNER_NAME, "inner");
	}

	#[test]
	fn test_gats_buflines() {
		let buf = TextBuf::new("a\nb\nc");
		let collected: Vec<&str> = buf.lines().collect();
		assert_eq!(collected, vec!["a", "b", "c"]);
	}

	#[test]
	fn test_associated_type_where_serializer() {
		#[derive(serde::Serialize)]
		struct Demo { id: u8 }
		let s = JsonSerializer;
		let out = s.serialize(&Demo { id: 7 });
		assert!(out.contains("\"id\":7"));
	}

	#[test]
	fn test_macro_and_derive() {
		let p = Point { x: 1, y: 2 };
		let v = make_vec![p.clone(), Point { x: 3, y: 4 }];
		assert_eq!(v.len(), 2);
		assert_eq!(format!("{:?}", v[0]), "Point { x: 1, y: 2 }");
	}

	#[test]
	fn test_macro_bulk_impl_trait() {
		use super::ToI64;
		assert_eq!(5i32.to_i64(), 5);
		assert_eq!(255u8.to_i64(), 255);
	}

	#[test]
	fn test_proc_macro_derive() {
		let user = User { id: 42, name: "Alice".to_string() };
		assert_eq!(user.display(), "User");
		assert!(user.id() > 0); // 哈希值应该大于 0
	}

	#[test]
	fn test_async_generic_and_block_on() {
		let fut = async_add_generic(2u8, 3u8);
		let sum = block_on(fut);
		assert_eq!(sum, 5);
	}
}

