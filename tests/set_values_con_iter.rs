use orx_concurrent_iter::{ExactSizeConcurrentIter, IntoConcurrentIter, NextChunk};
use orx_concurrent_ordered_bag::*;
use orx_pinned_vec::PinnedVec;
use test_case::test_matrix;

const NUM_RERUNS: usize = 1;

#[test_matrix(
    [1, 2, 4, 8],
    [4, 124, 2587],
    [1, 4, 64]
)]
fn write_at_odd_even_batches(num_threads: usize, len: usize, chunk_size: usize) {
    for _ in 0..NUM_RERUNS {
        let vec: Vec<_> = (0..len).collect();
        let iter = vec.into_con_iter();
        let con_iter = &iter;

        let bag = ConcurrentOrderedBag::new();
        let con_bag = &bag;

        std::thread::scope(|s| {
            for _ in 0..num_threads {
                s.spawn(move || {
                    while let Some(next) = con_iter.next_exact_chunk(chunk_size) {
                        unsafe { con_bag.set_values(next.begin_idx(), next.values().map(process)) };
                    }
                });
            }
        });

        let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
        for (i, value) in vec.iter().enumerate() {
            let expected_value = process(i);
            assert_eq!(value, &expected_value);
        }
    }
}

#[test_matrix(
    [1, 2, 4, 8],
    [4, 124, 2587],
    [1, 4, 64]
)]
fn vec_into_con_iter_long_process(num_threads: usize, len: usize, chunk_size: usize) {
    for _ in 0..NUM_RERUNS {
        let vec: Vec<_> = (0..len).collect();
        let iter = vec.into_con_iter();
        let con_iter = &iter;

        let bag = ConcurrentOrderedBag::new();
        let con_bag = &bag;

        std::thread::scope(|s| {
            for _ in 0..num_threads {
                s.spawn(move || {
                    while let Some(next) = con_iter.next_exact_chunk(chunk_size) {
                        let idx = next.begin_idx();
                        let value = idx + 1;
                        let mut sum = 1f64;
                        for i in 0..(1024 * 16) {
                            let y = ((i + 1 + value) as f64).ln();
                            let z = y * 2.0 + i as f64;
                            sum += z;
                        }
                        assert!(sum > 0f64);

                        unsafe { con_bag.set_values(next.begin_idx(), next.values().map(process)) };
                    }
                });
            }
        });

        let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
        for (i, value) in vec.iter().enumerate() {
            let expected_value = process(i);
            assert_eq!(value, &expected_value);
        }
    }
}

fn process(number: usize) -> String {
    format!("from-thread-{}", number)
}
