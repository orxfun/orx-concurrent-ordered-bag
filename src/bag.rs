use crate::{failures::IntoInnerResult, state::ConcurrentOrderedBagState};
use core::cmp::Ordering;
use orx_pinned_concurrent_col::PinnedConcurrentCol;
use orx_pinned_vec::{ConcurrentPinnedVec, IntoConcurrentPinnedVec};
use orx_split_vec::{Doubling, SplitVec};

/// An efficient, convenient and lightweight grow-only concurrent data structure allowing high performance and ordered concurrent collection.
///
/// * **convenient**: `ConcurrentBag` can safely be shared among threads simply as a shared reference. It is a [`PinnedConcurrentCol`](https://crates.io/crates/orx-pinned-concurrent-col) with a special concurrent state implementation. Underlying [`PinnedVec`](https://crates.io/crates/orx-pinned-vec) and concurrent bag can be converted back and forth to each other. Further, as you may see in the parallel map example, it enables efficient parallel methods with possibly the most convenient and simple implementation.
/// * **efficient**: `ConcurrentBag` is a lock free structure making use of a few atomic primitives, this leads to high performance concurrent growth while enabling to collect the results in the desired order.
///
/// ## Safety Requirements
///
/// As the comparison reveals, `ConcurrentBag` is much safer to use than `ConcurrentOrderedBag`, which could be the first choice if the order of collected elements does not matter. On the other hand, required safety guarantees fortunately are not too difficult to satisfy. ConcurrentOrderedBag can safely be used provided that the following two conditions are satisfied:
/// * Each position is written exactly once, so that there exists no race condition.
/// * At the point where `into_inner` is called (not necessarily always), the bag must not contain any gaps.
///   * Let `m` be the maximum index of the position that we write an element to.
///   * The bag assumes that the length of the vector is equal to `m + 1`.
///   * Then, it expects that exactly `m + 1` elements are written to the bag.
///   * If the first condition was satisfied; then, this condition is sufficient to conclude that the bag can be converted to the underlying vector of `m + 1` elements.
///
/// ## Examples
///
/// Safety guarantees to push to the bag with a shared reference makes it easy to share the bag among threads. However, the caller is required to make sure that the collection does not contain gaps and each position is written exactly once.
///
/// ### Manual Example
///
/// In the following example, we split computation among two threads: the first thread processes inputs with even indices, and the second with odd indices. This provides the required guarantee mentioned above.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
///
/// let n = 1024;
///
/// let evens_odds = ConcurrentOrderedBag::new();
///
/// // just take a reference and share among threads
/// let bag = &evens_odds;
///
/// std::thread::scope(|s| {
///     s.spawn(move || {
///         for i in (0..n).filter(|x| x % 2 == 0) {
///             unsafe { bag.set_value(i, i as i32) };
///         }
///     });
///
///     s.spawn(move || {
///         for i in (0..n).filter(|x| x % 2 == 1) {
///             unsafe { bag.set_value(i, -(i as i32)) };
///         }
///     });
/// });
///
/// let vec = unsafe { evens_odds.into_inner().unwrap_only_if_counts_match() };
/// assert_eq!(vec.len(), n);
/// for i in 0..n {
///     if i % 2 == 0 {
///         assert_eq!(vec[i], i as i32);
///     } else {
///         assert_eq!(vec[i], -(i as i32));
///     }
/// }
/// ```
///
/// Note that as long as no-gap and write-only-once guarantees are satisfied, `ConcurrentOrderedBag` is very flexible in the order of writes. They can simply happen in arbitrary order. Consider the following instance for instance. We spawn a thread just two write to the end of the collection, and then spawn a bunch of other threads to fill the beginning of the collection. This just works without any locks or waits.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
///
/// let n = 1024;
/// let num_additional_threads = 4;
///
/// let bag = ConcurrentOrderedBag::new();
/// let con_bag = &bag;
///
/// std::thread::scope(|s| {
///     s.spawn(move || {
///         // start writing to the end
///         unsafe { con_bag.set_value(n - 1, 42) };
///     });
///
///     for thread in 0..num_additional_threads {
///         s.spawn(move || {
///             // then fill the rest concurrently from the beginning
///             for i in (0..(n - 1)).filter(|i| i % num_additional_threads == thread) {
///                 unsafe { con_bag.set_value(i, i as i32) };
///             }
///         });
///     }
/// });
///
/// let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
/// assert_eq!(vec.len(), n);
/// for i in 0..(n - 1) {
///     assert_eq!(vec[i], i as i32);
/// }
/// assert_eq!(vec[n - 1], 42);
/// ```
///
/// These examples represent cases where the work can be trivially split among threads while providing the safety requirements. However, it requires special care and correctness. This complexity can significantly be avoided by pairing the `ConcurrentOrderedBag` with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter) on the input side.
///
/// ### Parallel Map with `ConcurrentIter`
///
/// Parallel map operation is one of the cases where we would care about the order of the collected elements, and hence, `ConcurrentBag` would not suffice. On the other hand, an efficient implementation can be achieved with `ConcurrentOrderedBag` and `ConcurrentIter`. Further, it might **possibly be the most convenient parallel map** implementation that is almost identical to a single-threaded map implementation.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
/// use orx_concurrent_iter::*;
/// use orx_iterable::*;
///
/// fn parallel_map<In, Out, Map, Inputs>(
///     num_threads: usize,
///     inputs: Inputs,
///     map: &Map,
/// ) -> ConcurrentOrderedBag<Out>
/// where
///     Inputs: ConcurrentIter<Item = In>,
///     Map: Fn(In) -> Out + Send + Sync,
///     Out: Send + Sync,
/// {
///     let outputs = ConcurrentOrderedBag::new();
///     let inputs = &inputs.enumerate();
///     let out = &outputs;
///     std::thread::scope(|s| {
///         for _ in 0..num_threads {
///             s.spawn(|| {
///                 while let Some((idx, value)) = inputs.next() {
///                     unsafe { out.set_value(idx, map(value)) };
///                 }
///             });
///         }
///     });
///     outputs
/// }
///
/// let len = 2465;
/// let vec: Vec<_> = (0..len).map(|x| x.to_string()).collect();
///
/// let bag = parallel_map(4, vec.into_con_iter(), &|x| x.to_string().len());
/// let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
///
/// assert_eq!(output.len(), len);
/// for (i, value) in output.iter().enumerate() {
///     assert_eq!(value, &i.to_string().len());
/// }
/// ```
///
/// As you may see, we are not required to share the work manually, we simply use a `while let Some` loop. The work is pulled by threads from the iterator. This both leads to an efficient implementation especially in cases of heterogeneous work loads of each task and automatically provides the safety requirements.
///
///
/// ### Parallel Map with `ConcurrentIter`
///
/// A further performance improvement to the parallel map implementation above is to distribute the tasks among the threads in chunks. The aim of this approach is to avoid false sharing, you may see further details [here](https://docs.rs/orx-concurrent-bag/latest/orx_concurrent_bag/#section-performance-notes). This can be achieved by pairing an [`ConcurrentIter`](https://docs.rs/orx-concurrent-iter/latest/orx_concurrent_iter/trait.ConcurrentIter.html) rather than a ConcurrentIter with the `set_values` method of the `ConcurrentOrderedBag`.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
/// use orx_concurrent_iter::*;
/// use orx_iterable::*;
///
/// fn parallel_map<In, Out, Map, Inputs>(
///     num_threads: usize,
///     inputs: Inputs,
///     map: &Map,
///     chunk_size: usize,
/// ) -> ConcurrentOrderedBag<Out>
/// where
///     Inputs: ConcurrentIter<Item = In>,
///     Map: Fn(In) -> Out + Send + Sync,
///     Out: Send + Sync,
/// {
///     let outputs = ConcurrentOrderedBag::new();
///     let inputs = &inputs;
///     let out = &outputs;
///     std::thread::scope(|s| {
///         for _ in 0..num_threads {
///             s.spawn(|| {
///                 let mut chunks_puller = inputs.chunk_puller(chunk_size);
///                 while let Some((begin_idx, values)) = chunks_puller.pull_with_idx() {
///                     unsafe { out.set_values(begin_idx, values.map(map)) };
///                 }
///             });
///         }
///     });
///     outputs
/// }
///
/// let len = 2465;
/// let vec: Vec<_> = (0..len).map(|x| x.to_string()).collect();
/// let bag = parallel_map(4, vec.into_con_iter(), &|x| x.to_string().len(), 64);
/// let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
/// for (i, value) in output.iter().enumerate() {
///     assert_eq!(value, &i.to_string().len());
/// }
/// ```
///
/// ### Construction
///
/// `ConcurrentOrderedBag` can be constructed by wrapping any pinned vector; i.e., `ConcurrentOrderedBag<T>` implements `From<P: PinnedVec<T>>`. Likewise, a concurrent vector can be unwrapped without any allocation to the underlying pinned vector with `into_inner` method, provided that the safety requirements are satisfied.
///
/// Further, there exist `with_` methods to directly construct the concurrent bag with common pinned vector implementations.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
///
/// // default pinned vector -> SplitVec<T, Doubling>
/// let bag: ConcurrentOrderedBag<char> = ConcurrentOrderedBag::new();
/// let bag: ConcurrentOrderedBag<char> = Default::default();
/// let bag: ConcurrentOrderedBag<char> = ConcurrentOrderedBag::with_doubling_growth();
/// let bag: ConcurrentOrderedBag<char, SplitVec<char, Doubling>> = ConcurrentOrderedBag::with_doubling_growth();
///
/// let bag: ConcurrentOrderedBag<char> = SplitVec::new().into();
/// let bag: ConcurrentOrderedBag<char, SplitVec<char, Doubling>> = SplitVec::new().into();
///
/// // SplitVec with [Linear](https://docs.rs/orx-split-vec/latest/orx_split_vec/struct.Linear.html) growth
/// // each fragment will have capacity 2^10 = 1024
/// // and the split vector can grow up to 32 fragments
/// let bag: ConcurrentOrderedBag<char, SplitVec<char, Linear>> = ConcurrentOrderedBag::with_linear_growth(10, 32);
/// let bag: ConcurrentOrderedBag<char, SplitVec<char, Linear>> = SplitVec::with_linear_growth_and_fragments_capacity(10, 32).into();
///
/// // [FixedVec](https://docs.rs/orx-fixed-vec/latest/orx_fixed_vec/) with fixed capacity.
/// // Fixed vector cannot grow; hence, pushing the 1025-th element to this bag will cause a panic!
/// let bag: ConcurrentOrderedBag<char, FixedVec<char>> = ConcurrentOrderedBag::with_fixed_capacity(1024);
/// let bag: ConcurrentOrderedBag<char, FixedVec<char>> = FixedVec::new(1024).into();
/// ```
///
/// Of course, the pinned vector to be wrapped does not need to be empty.
///
/// ```rust
/// use orx_concurrent_ordered_bag::*;
///
/// let split_vec: SplitVec<i32> = (0..1024).collect();
/// let bag: ConcurrentOrderedBag<_> = split_vec.into();
/// ```
///
/// ## Concurrent State and Properties
///
/// The concurrent state is modeled simply by an atomic capacity. Combination of this state and `PinnedConcurrentCol` leads to the following properties:
/// * Writing to a position of the collection does not block other writes, multiple writes can happen concurrently.
/// * Caller is required to guarantee that each position is written exactly once.
/// * ⟹ caller is responsible to avoid write & write race conditions.
/// * Only one growth can happen at a given time.
/// * Reading is only possible after converting the bag into the underlying `PinnedVec`.
/// * ⟹ no read & write race condition exists.
pub struct ConcurrentOrderedBag<T, P = SplitVec<T, Doubling>>
where
    P: IntoConcurrentPinnedVec<T>,
{
    core: PinnedConcurrentCol<T, P::ConPinnedVec, ConcurrentOrderedBagState>,
}

impl<T, P> ConcurrentOrderedBag<T, P>
where
    P: IntoConcurrentPinnedVec<T>,
{
    /// Converts the bag into [`IntoInnerResult`] which might then unwrapped to access the underlying pinned vector.
    pub fn into_inner(self) -> IntoInnerResult<P> {
        let len = self.core.state().len();
        let num_pushed = self.core.state().num_pushed();
        match len.cmp(&num_pushed) {
            Ordering::Equal => IntoInnerResult::LenMatchesNumPushes {
                len,
                vec: unsafe { self.core.into_inner(len) }.into(),
            },
            Ordering::Greater => IntoInnerResult::GreaterLenThanNumPushes {
                len,
                num_pushed,
                vec: unsafe { self.core.into_inner(len) }.into(),
            },
            Ordering::Less => IntoInnerResult::LessLenThanNumPushes {
                len,
                num_pushed,
                vec: unsafe { self.core.into_inner(len) }.into(),
            },
        }
    }

    /// ***O(1)*** Returns the length of the bag.
    ///
    /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
    ///
    /// # Examples
    ///
    /// ```rust
    /// use orx_concurrent_ordered_bag::ConcurrentOrderedBag;
    ///
    /// let bag = ConcurrentOrderedBag::new();
    ///
    /// unsafe { bag.set_value(2, 'c') };
    /// assert_eq!(3, bag.len());
    ///
    /// unsafe { bag.set_values(0, ['a', 'b']) };
    /// assert_eq!(3, bag.len());
    ///
    /// let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
    /// assert_eq!(vec, &['a', 'b', 'c']);
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.core.state().len()
    }

    /// Returns whether or not the bag is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use orx_concurrent_ordered_bag::ConcurrentOrderedBag;
    ///
    /// let mut bag = ConcurrentOrderedBag::new();
    ///
    /// assert!(bag.is_empty());
    ///
    /// unsafe { bag.set_values(0, ['a', 'b']) };
    /// assert!(!bag.is_empty());
    ///
    /// bag.clear();
    /// assert!(bag.is_empty());
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Sets the `idx`-th element of the collection to the given `value`.
    ///
    /// # Safety
    ///
    /// In a concurrent program, the caller is responsible to make sure that each position is written exactly and only once.
    pub unsafe fn set_value(&self, idx: usize, value: T) {
        unsafe { self.core.write(idx, value) };
    }

    /// Sets the elements in the range of `begin_idx..values.len()` positions of the collection to the given `values`.
    ///
    /// # Safety
    ///
    /// In a concurrent program, the caller is responsible to make sure that each position is written exactly and only once.
    pub unsafe fn set_values<IntoIter, Iter>(&self, begin_idx: usize, values: IntoIter)
    where
        IntoIter: IntoIterator<Item = T, IntoIter = Iter>,
        Iter: Iterator<Item = T> + ExactSizeIterator,
    {
        let values = values.into_iter();
        let num_items = values.len();
        unsafe { self.set_n_values(begin_idx, num_items, values) }
    }

    /// Sets the elements in the range of `begin_idx..(begin_idx + num_items)` positions of the collection to the given `values`.
    ///
    /// # Safety
    ///
    /// In a concurrent program, the caller is responsible to make sure that each position is written exactly and only once.
    ///
    /// Furthermore, `values` iterator must be capable of yielding at least (ideally, exactly) `num_items` elements.
    pub unsafe fn set_n_values<IntoIter>(
        &self,
        begin_idx: usize,
        num_items: usize,
        values: IntoIter,
    ) where
        IntoIter: IntoIterator<Item = T>,
    {
        unsafe { self.core.write_n_items(begin_idx, num_items, values) }
    }

    /// Reserves and returns an iterator of mutable slices for `num_items` positions starting from the `begin_idx`-th position.
    ///
    /// The caller is responsible for filling all `num_items` positions in the returned iterator of slices with values to avoid gaps.
    ///
    /// # Safety
    ///
    /// This method makes sure that the values are written to positions owned by the underlying pinned vector.
    /// Furthermore, it makes sure that the growth of the vector happens thread-safely whenever necessary.
    ///
    /// On the other hand, it is unsafe due to the possibility of a race condition.
    /// Multiple threads can try to write to the same position at the same time.
    /// The wrapper is responsible for preventing this.
    ///
    /// Furthermore, the caller is responsible to write all positions of the acquired slices to make sure that the collection is gap free.
    ///
    /// Note that although both methods are unsafe, it is much easier to achieve required safety guarantees with `set_values` or `set_n_values`;
    /// hence, they must be preferred unless there is a good reason to acquire mutable slices.
    /// One such example case is to copy results directly into the output's slices, which could be more performant in a very critical scenario.
    pub unsafe fn n_items_buffer_as_mut_slices(
        &self,
        begin_idx: usize,
        num_items: usize,
    ) -> <P::ConPinnedVec as ConcurrentPinnedVec<T>>::SliceMutIter<'_> {
        unsafe { self.core.n_items_buffer_as_mut_slices(begin_idx, num_items) }
    }

    /// Clears the concurrent bag.
    pub fn clear(&mut self) {
        unsafe { self.core.clear(self.core.state().len()) };
    }
}

// HELPERS

impl<T, P> ConcurrentOrderedBag<T, P>
where
    P: IntoConcurrentPinnedVec<T>,
{
    pub(crate) fn new_from_pinned(pinned_vec: P) -> Self {
        let core = PinnedConcurrentCol::new_from_pinned(pinned_vec);
        Self { core }
    }
}

// TRAITS

unsafe impl<T: Sync, P: IntoConcurrentPinnedVec<T>> Sync for ConcurrentOrderedBag<T, P> {}

unsafe impl<T: Send, P: IntoConcurrentPinnedVec<T>> Send for ConcurrentOrderedBag<T, P> {}
