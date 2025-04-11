// TODO: to be tested with the new orx-concurrent-iter version

// use orx_concurrent_iter::{ConcurrentIter, IntoConcurrentIter, IterIntoConcurrentIter};
// use orx_concurrent_ordered_bag::*;
// use orx_iterable::*;
// use test_case::test_matrix;

// const NUM_RERUNS: usize = 1;

// #[test_matrix(
//     [1, 2, 4, 8],
//     [4, 124, 348, 1024, 2587]
// )]
// fn vec_into_con_iter(num_threads: usize, len: usize) {
//     for _ in 0..NUM_RERUNS {
//         let vec: Vec<_> = (0..len).collect();
//         let iter = vec.into_con_iter().enumerate();
//         let con_iter = &iter;

//         let bag = ConcurrentOrderedBag::new();
//         let con_bag = &bag;

//         std::thread::scope(|s| {
//             for _ in 0..num_threads {
//                 s.spawn(move || {
//                     while let Some((idx, value)) = con_iter.next() {
//                         unsafe { con_bag.set_value(idx, process(value)) };
//                     }
//                 });
//             }
//         });

//         let vec = unsafe { bag.into_inner().unwrap() };
//         for (i, value) in vec.iter().enumerate() {
//             let expected_value = process(i);
//             assert_eq!(value, &expected_value);
//         }
//     }
// }

// #[test_matrix(
//     [1, 2, 4, 8],
//     [4, 124, 348, 1024, 2587]
// )]
// fn iter_into_con_iter_long_yield(num_threads: usize, len: usize) {
//     for _ in 0..NUM_RERUNS {
//         let vec: Vec<_> = (0..len).collect();
//         let iter = vec
//             .iter()
//             .map(|x| {
//                 let mut sum = 1f64;
//                 for i in 0..(1024 * 16) {
//                     let y = ((i + 1) as f64).ln();
//                     let z = y * 2.0 + i as f64;
//                     sum += z;
//                 }
//                 assert!(sum > 0f64);
//                 x
//             })
//             .iter_into_con_iter()
//             .enumerate();
//         let con_iter = &iter;

//         let bag = ConcurrentOrderedBag::new();
//         let con_bag = &bag;

//         std::thread::scope(|s| {
//             for _ in 0..num_threads {
//                 s.spawn(move || {
//                     while let Some((idx, value)) = con_iter.next() {
//                         unsafe { con_bag.set_value(idx, process(*value)) };
//                     }
//                 });
//             }
//         });

//         let vec = unsafe { bag.into_inner().unwrap() };
//         for (i, value) in vec.iter().enumerate() {
//             let expected_value = process(i);
//             assert_eq!(value, &expected_value);
//         }
//     }
// }

// #[test_matrix(
//     [1, 2, 4, 8],
//     [4, 124, 348, 1024, 2587]
// )]
// fn vec_into_con_iter_long_process(num_threads: usize, len: usize) {
//     for _ in 0..NUM_RERUNS {
//         let vec: Vec<_> = (0..len).collect();
//         let iter = vec.into_con_iter().enumerate();
//         let con_iter = &iter;

//         let bag = ConcurrentOrderedBag::new();
//         let con_bag = &bag;

//         std::thread::scope(|s| {
//             for _ in 0..num_threads {
//                 s.spawn(move || {
//                     while let Some((idx, value)) = con_iter.next() {
//                         let mut sum = 1f64;
//                         for i in 0..(1024 * 16) {
//                             let y = ((i + 1 + value) as f64).ln();
//                             let z = y * 2.0 + i as f64;
//                             sum += z;
//                         }
//                         assert!(sum > 0f64);
//                         unsafe { con_bag.set_value(idx, process(value)) };
//                     }
//                 });
//             }
//         });

//         let vec = unsafe { bag.into_inner().unwrap() };
//         for (i, value) in vec.iter().enumerate() {
//             let expected_value = process(i);
//             assert_eq!(value, &expected_value);
//         }
//     }
// }

// fn process(number: usize) -> String {
//     format!("from-thread-{}", number)
// }
