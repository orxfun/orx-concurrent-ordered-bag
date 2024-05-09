use orx_concurrent_iter::{ExactSizeConcurrentIter, IntoConcurrentIter};
use orx_concurrent_ordered_bag::*;
use orx_pinned_vec::PinnedVec;
use test_case::test_matrix;

fn parallel_map<In, Out, Map, Inputs>(
    num_threads: usize,
    inputs: Inputs,
    map: &Map,
    chunk_size: usize,
) -> ConcurrentOrderedBag<Out>
where
    Inputs: ExactSizeConcurrentIter<Item = In>,
    Map: Fn(In) -> Out + Send + Sync,
    Out: Send + Sync,
{
    let outputs = ConcurrentOrderedBag::new();

    let inputs = &inputs;
    let out = &outputs;

    std::thread::scope(|s| {
        for _ in 0..num_threads {
            s.spawn(|| {
                while let Some(next) = inputs.next_chunk(chunk_size) {
                    unsafe { out.set_values(next.begin_idx, next.values.map(map)) };
                }
            });
        }
    });

    outputs
}

fn validate_output<P: PinnedVec<usize>>(output: ConcurrentOrderedBag<usize, P>, len: usize) {
    let output = unsafe { output.into_inner().unwrap_only_if_counts_match() };
    assert_eq!(output.len(), len);

    for (i, value) in output.iter().enumerate() {
        assert_eq!(value, &i.to_string().len().max(1));
    }
}

#[test_matrix(
    [1, 4, 8],
    [1, 4, 245, 1024],
    [1, 4, 64, 128]
)]
fn pll_map_range(num_threads: usize, len: usize, chunk_size: usize) {
    let range = 0..len;
    let output = parallel_map(
        num_threads,
        range.into_con_iter(),
        &|x| x.to_string().len().max(1),
        chunk_size,
    );
    validate_output(output, len)
}

#[test_matrix(
    [1, 4, 8],
    [1, 4, 245, 1024],
    [1, 4, 64, 128]
)]
fn pll_map_vec(num_threads: usize, len: usize, chunk_size: usize) {
    let vec: Vec<_> = (0..len).map(|x| x.to_string()).collect();
    let output = parallel_map(
        num_threads,
        vec.into_con_iter(),
        &|x| x.to_string().len().max(1),
        chunk_size,
    );
    validate_output(output, len)
}

#[test_matrix(
    [1, 4, 8],
    [1, 4, 245, 1024],
    [1, 4, 64, 128]
)]
fn pll_map_slice(num_threads: usize, len: usize, chunk_size: usize) {
    let vec: Vec<_> = (0..len).map(|x| x.to_string()).collect();
    let output = parallel_map(
        num_threads,
        vec.as_slice().into_con_iter(),
        &|x| x.to_string().len().max(1),
        chunk_size,
    );
    validate_output(output, len)
}
