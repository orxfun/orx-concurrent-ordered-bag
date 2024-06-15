use orx_pinned_concurrent_col::{ConcurrentState, PinnedConcurrentCol, WritePermit};
use orx_pinned_vec::PinnedVec;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub struct ConcurrentOrderedBagState {
    is_growing: AtomicBool,
    len: AtomicUsize,
    num_pushed: AtomicUsize,
}

impl ConcurrentState for ConcurrentOrderedBagState {
    fn zero_memory(&self) -> bool {
        false
    }

    fn new_for_pinned_vec<T, P: PinnedVec<T>>(pinned_vec: &P) -> Self {
        Self {
            is_growing: false.into(),
            len: pinned_vec.len().into(),
            num_pushed: pinned_vec.len().into(),
        }
    }

    fn write_permit<T, P, S>(&self, col: &PinnedConcurrentCol<T, P, S>, idx: usize) -> WritePermit
    where
        P: PinnedVec<T>,
        S: ConcurrentState,
    {
        match idx.cmp(&col.capacity()) {
            std::cmp::Ordering::Less => WritePermit::JustWrite,
            _ => {
                let was_growing = self.is_growing.fetch_or(true, Ordering::SeqCst);
                let can_grow = !was_growing;

                match can_grow {
                    true => {
                        let new_capacity = std::hint::black_box(col.capacity());
                        if idx < new_capacity {
                            self.is_growing.store(false, Ordering::SeqCst);
                            WritePermit::JustWrite
                        } else {
                            WritePermit::GrowThenWrite
                        }
                    }
                    false => WritePermit::Spin,
                }
            }
        }
    }
    #[inline(always)]
    fn release_growth_handle(&self) {
        let prior = self.is_growing.fetch_and(false, Ordering::SeqCst);
        assert!(prior);
    }

    fn update_after_write(&self, begin_idx: usize, end_idx: usize) {
        _ = self.len.fetch_max(end_idx, Ordering::AcqRel);
        self.num_pushed
            .fetch_add(end_idx - begin_idx, Ordering::AcqRel);
    }

    fn try_get_no_gap_len(&self) -> Option<usize> {
        match self.num_pushed().cmp(&self.len()) {
            std::cmp::Ordering::Equal => Some(self.len()),
            _ => None,
        }
    }
}

impl ConcurrentOrderedBagState {
    // get
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    pub fn num_pushed(&self) -> usize {
        self.num_pushed.load(Ordering::Relaxed)
    }
}
