use orx_concurrent_ordered_bag::*;
use orx_pinned_vec::IntoConcurrentPinnedVec;
use test_case::test_matrix;

const NUM_RERUNS: usize = 1;

#[cfg(not(miri))]
const LEN: [usize; 5] = [4, 124, 348, 1024, 2587];
#[cfg(miri)]
const LEN: [usize; 3] = [4, 124, 348];

#[test_matrix(
    [
        FixedVec::new(100000),
        SplitVec::with_doubling_growth_and_max_concurrent_capacity(),
        SplitVec::with_linear_growth_and_fragments_capacity(10, 64),
    ]
)]
fn dropped_as_bag<P: IntoConcurrentPinnedVec<String> + Clone>(pinned_vec: P) {
    for _ in 0..NUM_RERUNS {
        for len in LEN {
            let num_threads = 4;
            let num_items_per_thread = len / num_threads;

            let bag = fill_bag(pinned_vec.clone(), len);

            assert_eq!(bag.len(), num_threads * num_items_per_thread);
        }
    }
}

#[test_matrix(
    [
        FixedVec::new(100000),
        SplitVec::with_doubling_growth_and_max_concurrent_capacity(),
        SplitVec::with_linear_growth_and_fragments_capacity(10, 64),
    ]
)]
fn dropped_after_into_inner<P: IntoConcurrentPinnedVec<String> + Clone>(pinned_vec: P) {
    for _ in 0..NUM_RERUNS {
        for len in LEN {
            let num_threads = 4;
            let num_items_per_thread = len / num_threads;

            let bag = fill_bag(pinned_vec.clone(), len);

            let inner = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
            assert_eq!(inner.len(), num_threads * num_items_per_thread);
        }
    }
}

fn fill_bag<P: IntoConcurrentPinnedVec<String>>(
    pinned_vec: P,
    len: usize,
) -> ConcurrentOrderedBag<String, P> {
    let num_threads = 4;
    let num_items_per_thread = len / num_threads;

    let bag: ConcurrentOrderedBag<_, _> = pinned_vec.into();
    let con_bag = &bag;
    std::thread::scope(move |s| {
        for i in 0..num_threads {
            s.spawn(move || {
                let mut idx = i * num_items_per_thread;
                for value in 0..num_items_per_thread {
                    let new_value = format!("from-thread-{}", value);
                    unsafe { con_bag.set_value(idx, new_value) };
                    idx += 1;
                }
            });
        }
    });

    bag
}
