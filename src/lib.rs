//! # orx-concurrent-ordered-bag
//!
//! [![orx-concurrent-ordered-bag crate](https://img.shields.io/crates/v/orx-concurrent-ordered-bag.svg)](https://crates.io/crates/orx-concurrent-ordered-bag)
//! [![orx-concurrent-ordered-bag documentation](https://docs.rs/orx-concurrent-ordered-bag/badge.svg)](https://docs.rs/orx-concurrent-ordered-bag)
//!
//! An efficient, convenient and lightweight grow-only concurrent data structure allowing high performance and ordered concurrent collection.
//!
//! * **convenient**: `ConcurrentOrderedBag` can safely be shared among threads simply as a shared reference. It is a [`PinnedConcurrentCol`](https://crates.io/crates/orx-pinned-concurrent-col) with a special concurrent state implementation. Underlying [`PinnedVec`](https://crates.io/crates/orx-pinned-vec) and concurrent bag can be converted back and forth to each other. The main goal of this collection is to enable efficient parallel operations with very simple implementations.
//! * **efficient**: `ConcurrentOrderedBag` is a lock free structure suitable for concurrent, copy-free and high performance growth while enabling to collect the results in the desired order.
//!
//! ## Safety Requirements
//!
//! Unlike [`ConcurrentBag`](https://crates.io/crates/orx-concurrent-bag) and [`ConcurrentVec`](https://crates.io/crates/orx-concurrent-vec), collection into a `CollectionOrderedBag` is through `unsafe` setter methods which are flexible in allowing to write at any position of the bag at any order. In order to use the bag safely, the caller is expected to satisfy the following two safety requirements:
//! * Each position is written exactly once, so that there exists no race condition.
//! * At the point where `into_inner` is called to get the underlying vector of collected elements, the bag must not contain any gaps.
//!   * Let `m` be the maximum index of the position that we write an element to.
//!   * The bag assumes that the length of the vector is equal to `m + 1`.
//!   * Then, it expects that exactly `m + 1` elements are written to the bag.
//!   * If the first condition was also satisfied; then, this condition is sufficient to conclude that the bag has no gaps and can be unwrapped.
//!
//! Satisfying these two conditions is easy in certain situations and harder in others. A good idea in complicated cases is to pair `ConcurrentOrderedBag` with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter) to greatly mitigate complexity and safety risks, please see the parallel map example below.
//!
//! ## Examples
//!
//! ### Manual Example
//!
//! In the following example, we split computation among two threads: the first thread processes inputs with even indices, and the second with odd indices. This fulfills the safety requirements mentioned above.
//!
//! ```rust
//! use orx_concurrent_ordered_bag::*;
//!
//! let n = 1024;
//!
//! let evens_odds = ConcurrentOrderedBag::new();
//!
//! // just take a reference and share among threads
//! let bag = &evens_odds;
//!
//! std::thread::scope(|s| {
//!     s.spawn(move || {
//!         for i in (0..n).filter(|x| x % 2 == 0) {
//!             unsafe { bag.set_value(i, i as i32) };
//!         }
//!     });
//!
//!     s.spawn(move || {
//!         for i in (0..n).filter(|x| x % 2 == 1) {
//!             unsafe { bag.set_value(i, -(i as i32)) };
//!         }
//!     });
//! });
//!
//! let vec = unsafe { evens_odds.into_inner().unwrap_only_if_counts_match() };
//! assert_eq!(vec.len(), n);
//! for i in 0..n {
//!     if i % 2 == 0 {
//!         assert_eq!(vec[i], i as i32);
//!     } else {
//!         assert_eq!(vec[i], -(i as i32));
//!     }
//! }
//! ```
//!
//! Note that as long as no-gap and write-only-once guarantees are satisfied, `ConcurrentOrderedBag` is very flexible in the order of writes. Consider the following example. We spawn a thread just two write to the end of the collection. Then we spawn a bunch of other threads to fill the beginning of the collection. This just works without any locks or waits.
//!
//! ```rust
//! use orx_concurrent_ordered_bag::*;
//!
//! let n = 1024;
//! let num_additional_threads = 4;
//!
//! let bag = ConcurrentOrderedBag::new();
//! let con_bag = &bag;
//!
//! std::thread::scope(|s| {
//!     s.spawn(move || {
//!         // start writing to the end
//!         unsafe { con_bag.set_value(n - 1, 42) };
//!     });
//!
//!     for thread in 0..num_additional_threads {
//!         s.spawn(move || {
//!             // then fill the rest concurrently from the beginning
//!             for i in (0..(n - 1)).filter(|i| i % num_additional_threads == thread) {
//!                 unsafe { con_bag.set_value(i, i as i32) };
//!             }
//!         });
//!     }
//! });
//!
//! let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
//! assert_eq!(vec.len(), n);
//! for i in 0..(n - 1) {
//!     assert_eq!(vec[i], i as i32);
//! }
//! assert_eq!(vec[n - 1], 42);
//! ```
//!
//! These examples represent cases where the work can be trivially split among threads while providing the safety requirements. In a general case, it requires special care to fulfill the safety requirements. This complexity and safety risks can significantly be avoided by pairing the `ConcurrentOrderedBag` with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter) on the input side.
//!
//! ### Parallel Map with `ConcurrentIter`
//!
//! Parallel map operation is one of the cases where we care about the order of the collected elements, and hence, a `ConcurrentBag` would not do. On the other hand, a very simple yet efficient implementation can be achieved with `ConcurrentOrderedBag` and `ConcurrentIter`.
//!
//! ```rust
//! use orx_concurrent_ordered_bag::*;
//! use orx_concurrent_iter::*;
//!
//! fn parallel_map<In, Out, Map, Inputs>(
//!     num_threads: usize,
//!     inputs: Inputs,
//!     map: &Map,
//! ) -> ConcurrentOrderedBag<Out>
//! where
//!     Inputs: ConcurrentIter<Item = In>,
//!     Map: Fn(In) -> Out + Send + Sync,
//!     Out: Send + Sync,
//! {
//!     let outputs = ConcurrentOrderedBag::new();
//!     let inputs = &inputs;
//!     let out = &outputs;
//!     std::thread::scope(|s| {
//!         for _ in 0..num_threads {
//!             s.spawn(|| {
//!                 while let Some(next) = inputs.next_id_and_value() {
//!                     unsafe { out.set_value(next.idx, map(next.value)) };
//!                 }
//!             });
//!         }
//!     });
//!     outputs
//! }
//!
//! let len = 2465;
//! let input: Vec<_> = (0..len).map(|x| x.to_string()).collect();
//!
//! let bag = parallel_map(4, input.into_con_iter(), &|x| x.to_string().len());
//!
//! let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
//! assert_eq!(output.len(), len);
//! for (i, value) in output.iter().enumerate() {
//!     assert_eq!(value, &i.to_string().len());
//! }
//! ```
//!
//! As you may see, no manual work or care is required to satisfy the safety requirements. Each element of the iterator is processed and written exactly once, just as it would in a sequential implementation.
//!
//! ### Parallel Map with `ConcurrentIter`
//!
//! A further performance improvement to the parallel map implementation above is to distribute the tasks among the threads in chunks. The aim of this approach is to avoid false sharing, you may see further details [here](https://docs.rs/orx-concurrent-bag/latest/orx_concurrent_bag/#section-performance-notes). This can be achieved by pairing an [`ConcurrentIter`](https://docs.rs/orx-concurrent-iter/latest/orx_concurrent_iter/trait.ConcurrentIter.html) rather than a ConcurrentIter with the `set_values` method of the `ConcurrentOrderedBag`.
//!
//! ```rust
//! use orx_concurrent_ordered_bag::*;
//! use orx_concurrent_iter::*;
//!
//! fn parallel_map<In, Out, Map, Inputs>(
//!     num_threads: usize,
//!     inputs: Inputs,
//!     map: &Map,
//!     chunk_size: usize,
//! ) -> ConcurrentOrderedBag<Out>
//! where
//!     Inputs: ConcurrentIter<Item = In>,
//!     Map: Fn(In) -> Out + Send + Sync,
//!     Out: Send + Sync,
//! {
//!     let outputs = ConcurrentOrderedBag::new();
//!     let inputs = &inputs;
//!     let out = &outputs;
//!     std::thread::scope(|s| {
//!         for _ in 0..num_threads {
//!             s.spawn(|| {
//!                 while let Some(next) = inputs.next_chunk(chunk_size) {
//!                     unsafe { out.set_values(next.begin_idx, next.values.map(map)) };
//!                 }
//!             });
//!         }
//!     });
//!     outputs
//! }
//!
//! let len = 2465;
//! let input: Vec<_> = (0..len).map(|x| x.to_string()).collect();
//! let bag = parallel_map(4, input.into_con_iter(), &|x| x.to_string().len(), 64);
//!
//! let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
//! for (i, value) in output.iter().enumerate() {
//!     assert_eq!(value, &i.to_string().len());
//! }
//! ```
//!
//! ## Concurrent State and Properties
//!
//! The concurrent state is modeled simply by an atomic capacity. Combination of this state and `PinnedConcurrentCol` leads to the following properties:
//! * Writing to a position of the collection does not block other writes, multiple writes can happen concurrently.
//! * Caller is required to guarantee that each position is written exactly once.
//! * ⟹ caller is responsible to avoid write & write race conditions.
//! * Only one growth can happen at a given time.
//! * Reading is only possible after converting the bag into the underlying `PinnedVec`.
//! * ⟹ no read & write race condition exists.
//!
//! ## Concurrent Friend Collections
//!
//! ||[`ConcurrentBag`](https://crates.io/crates/orx-concurrent-bag)|[`ConcurrentVec`](https://crates.io/crates/orx-concurrent-vec)|[`ConcurrentOrderedBag`](https://crates.io/crates/orx-concurrent-ordered-bag)|
//! |---|---|---|---|
//! | Write | Guarantees that each element is written exactly once via `push` or `extend` methods | Guarantees that each element is written exactly once via `push` or `extend` methods | Different in two ways. First, a position can be written multiple times. Second, an arbitrary element of the bag can be written at any time at any order using `set_value` and `set_values` methods. This provides a great flexibility while moving the safety responsibility to the caller; hence, the set methods are `unsafe`. |
//! | Read | Mainly, a write-only collection. Concurrent reading of already pushed elements is through `unsafe` `get` and `iter` methods. The caller is required to avoid race conditions. | A write-and-read collection. Already pushed elements can safely be read through `get` and `iter` methods. | Not supported currently. Due to the flexible but unsafe nature of write operations, it is difficult to provide required safety guarantees as a caller. |
//! | Ordering of Elements | Since write operations are through adding elements to the end of the pinned vector via `push` and `extend`, two multi-threaded executions of a code that collects elements into the bag might result in the elements being collected in different orders. | Since write operations are through adding elements to the end of the pinned vector via `push` and `extend`, two multi-threaded executions of a code that collects elements into the bag might result in the elements being collected in different orders. | This is the main goal of this collection, allowing to collect elements concurrently and in the correct order. Although this does not seem trivial; it can be achieved almost trivially when `ConcurrentOrderedBag` is used together with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter). |
//! | `into_inner` | Once the concurrent collection is completed, the bag can safely and cheaply be converted to its underlying `PinnedVec<T>`. | Once the concurrent collection is completed, the vec can safely be converted to its underlying `PinnedVec<ConcurrentOption<T>>`. Notice that elements are wrapped with a `ConcurrentOption` in order to provide thread safe concurrent read & write operations. | Growing through flexible setters allowing to write to any position, `ConcurrentOrderedBag` has the risk of containing gaps. `into_inner` call provides some useful metrics such as whether the number of elements pushed elements match the  maximum index of the vector; however, it cannot guarantee that the bag is gap-free. The caller is required to take responsibility to unwrap to get the underlying `PinnedVec<T>` through an `unsafe` call. |
//! |||||
//!
//! ## License
//!
//! This library is licensed under MIT license. See LICENSE for details.

#![warn(
    missing_docs,
    clippy::unwrap_in_result,
    clippy::unwrap_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::float_cmp,
    clippy::float_cmp_const,
    clippy::missing_panics_doc,
    clippy::todo
)]

mod bag;
mod failures;
mod new;
mod state;

/// Common relevant traits, structs, enums.
pub mod prelude;

pub use bag::ConcurrentOrderedBag;
pub use failures::{IntoInnerResult, MayFail};

pub use orx_fixed_vec::FixedVec;
pub use orx_pinned_vec::{
    ConcurrentPinnedVec, IntoConcurrentPinnedVec, PinnedVec, PinnedVecGrowthError,
};
pub use orx_split_vec::{Doubling, Linear, SplitVec};
