# orx-concurrent-ordered-bag

[![orx-concurrent-ordered-bag crate](https://img.shields.io/crates/v/orx-concurrent-ordered-bag.svg)](https://crates.io/crates/orx-concurrent-ordered-bag)
[![orx-concurrent-ordered-bag crate](https://img.shields.io/crates/d/orx-concurrent-ordered-bag.svg)](https://crates.io/crates/orx-concurrent-ordered-bag)
[![orx-concurrent-ordered-bag documentation](https://docs.rs/orx-concurrent-ordered-bag/badge.svg)](https://docs.rs/orx-concurrent-ordered-bag)

An efficient, convenient and lightweight grow-only concurrent data structure allowing high performance and ordered concurrent collection.

A [`ConcurrentOrderedBag`](https://docs.rs/orx-concurrent-ordered-bag/latest/orx_concurrent_ordered_bag/struct.ConcurrentOrderedBag.html) can safely be shared among threads simply as a shared reference. It is a lock free structure enabling efficient and copy free concurrent collection of elements.
* It is a [`PinnedConcurrentCol`](https://crates.io/crates/orx-pinned-concurrent-col)  with a concurrent state definition specialized for efficient and ordered collection of elements, while requiring the caller to satisfy certain safety requirements discussed in the next section.
* It is built upon the pinned element guarantees of the underlying [`PinnedVec`](https://crates.io/crates/orx-pinned-vec) storage.

## Safety Requirements

Unlike [`ConcurrentBag`](https://crates.io/crates/orx-concurrent-bag) and [`ConcurrentVec`](https://crates.io/crates/orx-concurrent-vec), adding elements to a CollectionOrderedBag is through `unsafe` setter methods.

These setter methods are extremely are flexible in allowing to write at any position of the bag at any order. The index can safely be out of bounds, which will be handled by the bag by concurrently extending the capacity.

In order to use the bag safely, the caller is expected to satisfy the following **two safety requirements**:
* Each position is written exactly once **⟹ no write & write race condition exists**
* At the point where [`into_inner`](https://docs.rs/orx-concurrent-ordered-bag/latest/orx_concurrent_ordered_bag/struct.ConcurrentOrderedBag.html#method.into_inner) is called to get the underlying vector of collected elements, the bag must not contain any gaps **⟹ no uninitialized data**
  * Let **m** be the maximum index of the position that we wrote an element to.
  * The bag assumes that the length of the vector is equal to `m + 1`, and expects that exactly `m + 1` elements are written to the bag.
  * If the first condition was also satisfied; then, this condition is sufficient to conclude that the bag has no gaps and can be unwrapped.
  * Note that **into_inner** returns [`IntoInnerResult`](https://docs.rs/orx-concurrent-ordered-bag/latest/orx_concurrent_ordered_bag/prelude/enum.IntoInnerResult.html) providing additional useful information about the state of the bag. However, the caller is still required to make the final unsafe call to unwrap the underlying vector.

Although these two conditions that the caller is required to satisfy sound challenging in general, they are trivially satisfied in certain situations. For instance, when paired up with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter), the conditions are often readily satisfied. Please see the parallel map example below.

## Examples

### Manual Example

In the following example, we split computation among two threads: the first thread processes inputs with even indices, and the second with odd indices. This separation of tasks make it easier to satisfy the safety requirements mentioned above.

```rust
use orx_concurrent_ordered_bag::*;

let n = 1024;

let evens_odds = ConcurrentOrderedBag::new();

// just take a reference and share among threads
let bag = &evens_odds;

std::thread::scope(|s| {
    s.spawn(move || {
        for i in (0..n).filter(|x| x % 2 == 0) {
            unsafe { bag.set_value(i, i as i32) };
        }
    });

    s.spawn(move || {
        for i in (0..n).filter(|x| x % 2 == 1) {
            unsafe { bag.set_value(i, -(i as i32)) };
        }
    });
});

let vec = unsafe { evens_odds.into_inner().unwrap_only_if_counts_match() };
assert_eq!(vec.len(), n);

// although concurrently collected, the vec is ordered
for i in 0..n {
    if i % 2 == 0 {
        assert_eq!(vec[i], i as i32);
    } else {
        assert_eq!(vec[i], -(i as i32));
    }
}
```

Note that as long as no-gap and write-only-once guarantees are satisfied, **ConcurrentOrderedBag** is very flexible in the order of writes.

Consider the following extreme example. We spawn a thread just to push the last element of the collection. Then we spawn a bunch of other threads to fill the beginning of the collection. This just works without any locks since the two conditions are satisfied.

```rust
use orx_concurrent_ordered_bag::*;

let n = 1024;
let num_additional_threads = 4;

let bag = ConcurrentOrderedBag::new();
let con_bag = &bag;

std::thread::scope(|s| {
    s.spawn(move || {
        // start writing to the end
        unsafe { con_bag.set_value(n - 1, 42) };
    });

    for thread in 0..num_additional_threads {
        s.spawn(move || {
            // then fill the rest concurrently from the beginning
            for i in (0..(n - 1)).filter(|i| i % num_additional_threads == thread) {
                unsafe { con_bag.set_value(i, i as i32) };
            }
        });
    }
});

let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
assert_eq!(vec.len(), n);
for i in 0..(n - 1) {
    assert_eq!(vec[i], i as i32);
}
assert_eq!(vec[n - 1], 42);
```

### Parallel Map with `ConcurrentIter`

Parallel map operation is one of the cases where we care about the order of the collected elements, and hence, a **ConcurrentBag** with safe growth methods would not do.

On the other hand, a very simple yet efficient implementation can be achieved with **ConcurrentOrderedBag** and **ConcurrentIter** combination.

```rust
use orx_concurrent_ordered_bag::*;
use orx_concurrent_iter::*;
use orx_iterable::Collection;

fn parallel_map<In, Out, Map, Inputs>(
    num_threads: usize,
    inputs: Inputs,
    map: &Map,
) -> ConcurrentOrderedBag<Out>
where
    Inputs: ConcurrentIter<Item = In>,
    Map: Fn(In) -> Out + Send + Sync,
    Out: Send + Sync,
{
    let inputs = inputs.enumerate();
    let outputs = ConcurrentOrderedBag::new();
    std::thread::scope(|s| {
        for _ in 0..num_threads {
            s.spawn(|| {
                while let Some((idx, value)) = inputs.next() {
                    unsafe { outputs.set_value(idx, map(value)) };
                }
            });
        }
    });
    outputs
}

let len = 2465;
let input: Vec<_> = (0..len).map(|x| x.to_string()).collect();

let bag = parallel_map(4, input.into_con_iter(), &|x| x.to_string().len());

let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
assert_eq!(output.len(), len);

for (i, value) in output.iter().enumerate() {
    assert_eq!(value, &i.to_string().len());
}
```

As you may see, no manual work or care is required to satisfy the safety requirements. Each element of the iterator is processed and written exactly once, just as it would in a sequential implementation.

### Parallel Map with `ConcurrentIter` in Chunks

A further and significant performance improvement to the parallel map implementation above is to distribute the tasks among the threads in chunks. The aim of this approach is to avoid false sharing, you may see further details [here](https://docs.rs/orx-concurrent-bag/latest/orx_concurrent_bag/#section-performance-notes). This can be achieved by using [`next_chunk`](https://docs.rs/orx-concurrent-iter/latest/orx_concurrent_iter/trait.ConcurrentIter.html#tymethod.next_chunk) method of the ConcurrentIter with [`set_values`](https://docs.rs/orx-concurrent-ordered-bag/latest/orx_concurrent_ordered_bag/struct.ConcurrentOrderedBag.html#method.set_values) method of the ConcurrentOrderedBag.

```rust
use orx_concurrent_ordered_bag::*;
use orx_concurrent_iter::*;
use orx_iterable::Collection;

fn parallel_map<In, Out, Map, Inputs>(
    num_threads: usize,
    inputs: Inputs,
    map: &Map,
    chunk_size: usize,
) -> ConcurrentOrderedBag<Out>
where
    Inputs: ConcurrentIter<Item = In>,
    Map: Fn(In) -> Out + Send + Sync,
    Out: Send + Sync,
{
    let outputs = ConcurrentOrderedBag::new();
    std::thread::scope(|s| {
        for _ in 0..num_threads {
            s.spawn(|| {
                let mut chunks_puller = inputs.chunk_puller(chunk_size);
                while let Some((begin_idx, values)) = chunks_puller.pull_with_idx() {
                    unsafe { outputs.set_values(begin_idx, values.map(map)) };
                }
            });
        }
    });
    outputs
}

let len = 2465;
let input: Vec<_> = (0..len).map(|x| x.to_string()).collect();
let bag = parallel_map(4, input.into_con_iter(), &|x| x.to_string().len(), 64);

let output = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
for (i, value) in output.iter().enumerate() {
    assert_eq!(value, &i.to_string().len());
}
```

## Concurrent State and Properties

The concurrent state is modeled simply by an atomic capacity. Combination of this state and `PinnedConcurrentCol` leads to the following properties:
* Writing to a position of the collection does not block other writes, multiple writes can happen concurrently.
* Caller is required to guarantee that each position is written exactly once.
* **⟹ caller is responsible to avoid write & write race conditions**
* Only one growth can happen at a given time.
* Reading is only possible after converting the bag into the underlying `PinnedVec`.
* **⟹ no read & write race condition exists**

## Comparison with Other Concurrent Collections with Pinned Elements

There are a few concurrent data structures that are built on pinned element guarantees of pinned vectors. They have different pros and cons which are summarized in the table below.

|                      | [`ConcurrentBag`](https://crates.io/crates/orx-concurrent-bag)                                                                                                                                                                                            | [`ConcurrentOrderedBag`](https://crates.io/crates/orx-concurrent-ordered-bag)                                                                                                                                                                                                                                                                                                                                                                        | [`ConcurrentVec`](https://crates.io/crates/orx-concurrent-vec)                                                                                                                                                                                            |
|----------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Write                | Guarantees that each element is written exactly once via **push** or **extend** methods.                                                                                                                                                                       | Different in two ways. First, a position can be written multiple times. Second, an arbitrary element of the bag can be written at any time at any order using **set_value** and **set_values** methods. This provides a great flexibility while moving the safety responsibility to the caller; hence, the set methods are **unsafe**.                                                                                                                     | Guarantees that each element is written exactly once via **push** or **extend** methods. Further, since it is a concurrent **grow, read & update** collection, it additionally allows to concurrently mutate already pushed elements.                                                                                                                                                                       |
| Read                 | A grow-only collection. Concurrent reading of elements is through **unsafe** **get** and **iter** methods. The caller is required to avoid race conditions.                                                                             | Not supported currently. Due to the flexible but unsafe nature of write operations, it is difficult to provide required safety guarantees as a caller.                                                                                                                                                                                                                                                                                               | A concurrent grow, read and update collection. Already pushed elements can safely be read through methods such as **get** and **iter** methods.                                                                                                                                                 |
| Ordering of Elements | Two multi-threaded executions of a program collecting elements into a bag might result in the elements being collected in different orders. | Allows to collect elements concurrently and in the correct or desired order. It is trivial to provide safety guarantees in certain situations; for instance, when used together with a [`ConcurrentIter`](https://crates.io/crates/orx-concurrent-iter).                                                                                                                                         | Two multi-threaded executions of a program collecting elements into a bag might result in the elements being collected in different orders. |
| `into_inner`         | At any time, the bag can safely and cheaply be converted to its underlying PinnedVec, and vice versa.                                                                                                                                   | Growing through flexible setters allowing to write to any position, ConcurrentOrderedBag has the risk of containing gaps. The caller is required to get the underlying PinnedVec through an **unsafe** into_inner call. | At any time, the bag can safely and cheaply be converted to its underlying PinnedVec, and vice versa. However, the pinned vector stores elements wrapped in a [`ConcurrentOption`](https://crates.io/crates/orx-concurrent-option).               |
|                      |                                                                                                          

## Contributing

Contributions are welcome! If you notice an error, have a question or think something could be improved, please open an [issue](https://github.com/orxfun/orx-concurrent-ordered-bag/issues/new) or create a PR.

## License

Dual-licensed under [Apache 2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT).
