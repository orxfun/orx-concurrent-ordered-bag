/// Result of [`crate::ConcurrentOrderedBag::into_inner`] call.
pub enum IntoInnerResult<P> {
    /// Length of the bag is equal to the number of elements pushed.
    ///
    /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
    LenMatchesNumPushes {
        /// Length of the bag.
        ///
        /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
        len: usize,
        /// Underlying pinned vector which can safely be `unwrapped` if the caller can guarantee that each element is written exactly once.
        /// Otherwise, the vector might still contain gaps.
        vec: MayFail<P>,
    },
    /// Number of pushes to the bag is greater than the length of the vector.
    /// This indicates that at least one position is never written; and hence, there exists at least `len - num_pushed` gaps.
    /// The caller is required to take the responsibility to unwrap.
    ///
    /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
    GreaterLenThanNumPushes {
        /// Length of the bag.
        ///
        /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
        len: usize,
        /// Number of times an element is written to the bag.
        num_pushed: usize,
        /// Underlying pinned vector has gaps.
        /// The caller is required to take the responsibility to unwrap.
        vec: MayFail<P>,
    },
    /// Number of pushes to the bag is greater than the length of the vector.
    /// This indicates that at least one position is written at least twice, which is a violation of the safety requirement.
    /// The caller is required to take the responsibility to unwrap.
    ///
    /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
    LessLenThanNumPushes {
        /// Length of the bag.
        ///
        /// *Length is assumed to be `m + 1`, where `m` is the index of the maximum position an element is written to.*
        len: usize,
        /// Number of times an element is written to the bag.
        num_pushed: usize,
        /// There has been multiple writes to the same position and there might still be gaps in the collection.
        /// The caller is required to take the responsibility to unwrap.
        vec: MayFail<P>,
    },
}

impl<P> IntoInnerResult<P> {
    /// Without checking the `IntoInnerResult` variant, directly unwraps and returns the underlying pinned vector.
    ///
    /// # Safety
    ///
    /// The underlying vector might be in an invalid condition if the safety requirements are not followed during concurrent growth:
    /// * Each position is written exactly once, so that there exists no race condition.
    /// * At the point where `into_inner` is called (not necessarily always), the bag must not contain any gaps.
    ///   * Let `m` be the maximum index of the position that we write an element to.
    ///   * The bag assumes that the length of the vector is equal to `m + 1`.
    ///   * Then, it expects that exactly `m + 1` elements are written to the bag.
    ///   * If the first condition was satisfied; then, this condition is sufficient to conclude that the bag can be converted to the underlying vector of `m + 1` elements.
    pub unsafe fn unwrap(self) -> P {
        match self {
            IntoInnerResult::LenMatchesNumPushes { len: _, vec } => unsafe { vec.unwrap() },
            IntoInnerResult::GreaterLenThanNumPushes {
                len: _,
                num_pushed: _,
                vec,
            } => unsafe { vec.unwrap() },
            IntoInnerResult::LessLenThanNumPushes {
                len: _,
                num_pushed: _,
                vec,
            } => unsafe { vec.unwrap() },
        }
    }

    /// Unwraps and returns the pinned vector if the result is of [`IntoInnerResult::LenMatchesNumPushes`] variant, panics otherwise.
    ///
    /// # Panics
    ///
    /// Panics if the result is not of the [`IntoInnerResult::LenMatchesNumPushes`] variant.
    ///
    /// # Safety
    ///
    /// The underlying vector might be in an invalid condition if the safety requirements are not followed during concurrent growth:
    /// * Each position is written exactly once, so that there exists no race condition.
    /// * At the point where `into_inner` is called (not necessarily always), the bag must not contain any gaps.
    ///   * Let `m` be the maximum index of the position that we write an element to.
    ///   * The bag assumes that the length of the vector is equal to `m + 1`.
    ///   * Then, it expects that exactly `m + 1` elements are written to the bag.
    ///   * If the first condition was satisfied; then, this condition is sufficient to conclude that the bag can be converted to the underlying vector of `m + 1` elements.
    #[allow(clippy::panic)]
    pub unsafe fn unwrap_only_if_counts_match(self) -> P {
        match self {
            IntoInnerResult::LenMatchesNumPushes { len: _, vec } => unsafe { vec.unwrap() },
            IntoInnerResult::GreaterLenThanNumPushes {
                len,
                num_pushed,
                vec: _,
            } => panic!(
                "OrderedConcurrentBag surely contains gaps: {} elements are pushed; however, maximum index is {}.",
                num_pushed, len
            ),
            IntoInnerResult::LessLenThanNumPushes {
                len,
                num_pushed,
                vec: _,
            } => panic!(
                "OrderedConcurrentBag surely contains gaps: {} elements are pushed; however, maximum index is {}.",
                num_pushed, len
            ),
        }
    }
}

/// A wrapped value which can only be unwrapped through an unsafe call, leaving the decision or responsibility to the caller.
pub struct MayFail<T>(T);

impl<T> MayFail<T> {
    /// Wraps the `value` as a `MayFail` value.
    pub fn new(value: T) -> Self {
        Self(value)
    }

    /// Unwraps and returns the underlying value.
    ///
    /// # Safety
    ///
    /// MayFail is a marker where the producer cannot make sure of safety of the underlying value, and leaves the decision to the caller to unsafely unwrap.
    pub unsafe fn unwrap(self) -> T {
        self.0
    }
}

impl<P> From<P> for MayFail<P> {
    fn from(value: P) -> Self {
        Self::new(value)
    }
}
