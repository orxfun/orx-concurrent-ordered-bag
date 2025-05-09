use orx_concurrent_ordered_bag::*;
use orx_pinned_vec::PinnedVec;
use test_case::test_matrix;

#[cfg(not(miri))]
const N: [usize; 6] = [1, 2, 4, 1024, 2587, 42578];
#[cfg(miri)]
const N: [usize; 5] = [1, 2, 4, 124, 257];

#[test]
fn write_at_odd_even_indices() {
    for n in N {
        let bag = ConcurrentOrderedBag::new();
        let con_bag = &bag;

        std::thread::scope(|s| {
            s.spawn(move || {
                for i in (0..n).filter(|x| x % 2 == 0) {
                    unsafe { con_bag.set_value(i, i as i32) };
                }
            });

            s.spawn(move || {
                for i in (0..n).filter(|x| x % 2 == 1) {
                    unsafe { con_bag.set_value(i, -(i as i32)) };
                }
            });
        });

        let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
        for i in 0..n {
            if i % 2 == 0 {
                assert_eq!(vec[i], i as i32);
            } else {
                assert_eq!(vec[i], -(i as i32));
            }
        }
    }
}

#[test]
fn non_uniform() {
    for n in N {
        let bag = ConcurrentOrderedBag::new();
        let con_bag = &bag;

        fn second_indices(n: usize) -> [usize; 3] {
            [n / 3, 2 * n / 2, n - 1]
        }

        std::thread::scope(|s| {
            s.spawn(move || {
                let specials = second_indices(n);
                for i in (0..n).filter(|x| !specials.contains(x)) {
                    unsafe { con_bag.set_value(i, i as i32) };
                }
            });

            s.spawn(move || {
                let specials = second_indices(n);
                for i in (0..n).filter(|x| specials.contains(x)) {
                    unsafe { con_bag.set_value(i, 1000 + i as i32) };
                }
            });
        });

        let specials = second_indices(n);
        let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
        for i in 0..n {
            if specials.contains(&i) {
                assert_eq!(vec[i], 1000 + i as i32);
            } else {
                assert_eq!(vec[i], i as i32);
            }
        }
    }
}

#[cfg(not(miri))]
const LEN: [usize; 5] = [4, 124, 348, 1024, 2587];
#[cfg(miri)]
const LEN: [usize; 3] = [4, 124, 348];

#[test_matrix([1, 2, 4, 8])]
fn early_alloc(num_additional_threads: usize) {
    for len in LEN {
        let bag = ConcurrentOrderedBag::new();
        let con_bag = &bag;

        std::thread::scope(|s| {
            s.spawn(move || {
                unsafe { con_bag.set_value(len - 1, 42) };
            });

            for thread in 0..num_additional_threads {
                s.spawn(move || {
                    for i in (0..(len - 1)).filter(|i| i % num_additional_threads == thread) {
                        unsafe { con_bag.set_value(i, i as i32) };
                    }
                });
            }
        });

        let vec = unsafe { bag.into_inner().unwrap_only_if_counts_match() };
        assert_eq!(vec.len(), len);
        for i in 0..(len - 1) {
            assert_eq!(vec[i], i as i32);
        }
        assert_eq!(vec[len - 1], 42);
    }
}
