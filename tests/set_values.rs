use orx_concurrent_ordered_bag::*;
use orx_pinned_vec::PinnedVec;
use test_case::test_matrix;

#[test_matrix(
    [1, 2, 4, 1024, 2587],
    [1, 4, 64, 128]
)]
fn write_at_odd_even_batches(num_batches: usize, batch_size: usize) {
    let bag = ConcurrentOrderedBag::new();
    let con_bag = &bag;

    std::thread::scope(|s| {
        s.spawn(move || {
            for b in (0..num_batches).filter(|x| x % 2 == 0) {
                let beg_idx = b * batch_size;
                let values = (0..batch_size).map(|_| b as i32);
                unsafe { con_bag.set_values(beg_idx, values) };
            }
        });

        s.spawn(move || {
            for b in (0..num_batches).filter(|x| x % 2 == 1) {
                let beg_idx = b * batch_size;
                let values = (0..batch_size).map(|_| -(b as i32));
                unsafe { con_bag.set_values(beg_idx, values) };
            }
        });
    });

    let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
    assert_eq!(vec.len(), num_batches * batch_size);
    for b in 0..num_batches {
        let expected_value = if b % 2 == 0 { b as i32 } else { -(b as i32) };
        let beg_idx = b * batch_size;
        let end_idx = beg_idx + batch_size;
        for i in beg_idx..end_idx {
            assert_eq!(vec[i], expected_value);
        }
    }
}

#[test_matrix(
    [1, 2, 4, 1024, 2587],
    [1, 4, 64, 128]
)]
fn non_uniform_batches(num_batches: usize, batch_size: usize) {
    let bag = ConcurrentOrderedBag::new();
    let con_bag = &bag;

    fn second_indices(n: usize) -> [usize; 3] {
        [n / 3, 2 * n / 2, n - 1]
    }

    std::thread::scope(|s| {
        s.spawn(move || {
            let specials = second_indices(num_batches);
            for b in (0..num_batches).filter(|x| !specials.contains(x)) {
                let beg_idx = b * batch_size;
                let values = (0..batch_size).map(|_| b as i32);
                unsafe { con_bag.set_values(beg_idx, values) };
            }
        });

        s.spawn(move || {
            let specials = second_indices(num_batches);
            for b in (0..num_batches).filter(|x| specials.contains(x)) {
                let beg_idx = b * batch_size;
                let values = (0..batch_size).map(|_| -(b as i32));
                unsafe { con_bag.set_values(beg_idx, values) };
            }
        });
    });

    let specials = second_indices(num_batches);
    let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
    assert_eq!(vec.len(), num_batches * batch_size);
    for b in 0..num_batches {
        let expected_value = if !specials.contains(&b) {
            b as i32
        } else {
            -(b as i32)
        };
        let beg_idx = b * batch_size;
        let end_idx = beg_idx + batch_size;
        for i in beg_idx..end_idx {
            assert_eq!(vec[i], expected_value);
        }
    }
}

#[test_matrix(
    [1, 2, 4, 8],
    [4, 124, 348, 1024, 2587]
)]
fn early_alloc_batch(num_additional_threads: usize, num_batches: usize) {
    let bag = ConcurrentOrderedBag::new();
    let con_bag = &bag;

    std::thread::scope(|s| {
        s.spawn(move || {
            unsafe { con_bag.set_values(num_batches - 1, std::iter::once(42)) };
        });

        for thread in 0..num_additional_threads {
            s.spawn(move || {
                for i in (0..(num_batches - 1)).filter(|i| i % num_additional_threads == thread) {
                    unsafe { con_bag.set_values(i, std::iter::once(i as i32)) };
                }
            });
        }
    });

    let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
    assert_eq!(vec.len(), num_batches);
    for i in 0..(num_batches - 1) {
        assert_eq!(vec[i], i as i32);
    }
    assert_eq!(vec[num_batches - 1], 42);
}
