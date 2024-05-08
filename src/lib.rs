use std::{
    error::Error,
    fmt::{Display, Formatter},
    mem::MaybeUninit,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollectArrayError {
    NotEnoughItems,
    TooManyItems,
}

impl Display for CollectArrayError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotEnoughItems => write!(f, "not enough items to fill the array"),
            Self::TooManyItems => write!(f, "too many items to fit into the array"),
        }
    }
}

impl Error for CollectArrayError {}

pub trait IteratorExt: Iterator {
    /// # Errors
    /// - [`CollectArrayError::NotEnoughItems`] if the iterator has less items than the array
    /// - [`CollectArrayError::TooManyItems`] if the iterator has more items than the array
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_array_ext::{CollectArrayError, IteratorExt};
    ///
    /// let mut iter = vec![1, 2, 3].into_iter();
    /// let array = [1, 2, 3];
    /// assert_eq!(iter.try_collect_array::<3>(), Ok([1, 2, 3]));
    ///
    /// let mut iter = vec![1, 2].into_iter();
    /// let array = [1, 2, 3];
    /// assert_eq!(
    ///     iter.try_collect_array::<3>(),
    ///     Err(CollectArrayError::NotEnoughItems)
    /// );
    ///
    /// let mut iter = vec![1, 2, 3, 4].into_iter();
    /// let array = [1, 2, 3];
    /// assert_eq!(
    ///     iter.try_collect_array::<3>(),
    ///     Err(CollectArrayError::TooManyItems)
    /// );
    /// ```
    fn try_collect_array<const N: usize>(mut self) -> Result<[Self::Item; N], CollectArrayError>
    where
        Self: Sized,
    {
        let mut array: [MaybeUninit<Self::Item>; N] =
            unsafe { MaybeUninit::<[MaybeUninit<Self::Item>; N]>::uninit().assume_init() };

        for idx in 0..N {
            let Some(next) = self.next() else {
                for elem in array.iter_mut().take(idx) {
                    unsafe { elem.assume_init_drop() };
                }

                return Err(CollectArrayError::NotEnoughItems);
            };

            array[idx].write(next);
        }

        if self.next().is_some() {
            for elem in &mut array {
                unsafe { elem.assume_init_drop() };
            }

            return Err(CollectArrayError::TooManyItems);
        }

        // todo: do not use transmute_copy
        let result = unsafe { core::mem::transmute_copy(&array) };

        Ok(result)
    }
}

impl<T> IteratorExt for T where T: Iterator {}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    struct DropTracker<'a>(&'a Cell<i32>);

    impl<'a> Drop for DropTracker<'a> {
        fn drop(&mut self) {
            let get = self.0.get();
            self.0.set(get + 1);
        }
    }

    #[test]
    fn test_empty_iterator() {
        let empty_iter = std::iter::empty::<i32>();
        assert_eq!(empty_iter.try_collect_array::<0>(), Ok([]));

        let empty_iter = std::iter::empty::<i32>();
        assert_eq!(
            empty_iter.try_collect_array::<1>(),
            Err(CollectArrayError::NotEnoughItems)
        );
    }

    #[test]
    fn test_exact_size_iterator() {
        let iter = vec![1, 2, 3].into_iter();
        assert_eq!(iter.try_collect_array::<3>(), Ok([1, 2, 3]));
    }

    #[test]
    fn test_too_few_items() {
        let iter = vec![1, 2].into_iter();
        assert_eq!(
            iter.try_collect_array::<3>(),
            Err(CollectArrayError::NotEnoughItems)
        );
    }

    #[test]
    fn test_too_many_items() {
        let iter = vec![1, 2, 3, 4].into_iter();
        assert_eq!(
            iter.try_collect_array::<3>(),
            Err(CollectArrayError::TooManyItems)
        );
    }

    #[test]
    fn test_drop_on_not_enough_items() {
        let drop_counts = Cell::new(0);

        {
            let iter = vec![DropTracker(&drop_counts), DropTracker(&drop_counts)].into_iter();
            let _ = iter.try_collect_array::<3>();
        }
        assert_eq!(drop_counts.get(), 2);
    }

    #[test]
    fn test_drop_on_success() {
        let drop_counts = Cell::new(0);
        {
            let iter = vec![
                DropTracker(&drop_counts),
                DropTracker(&drop_counts),
                DropTracker(&drop_counts),
            ]
            .into_iter();
            let _drop_at_end = iter.try_collect_array::<3>();
            assert_eq!(drop_counts.get(), 0);
        }

        assert_eq!(drop_counts.get(), 3);
    }
    #[test]
    fn test_drop_on_too_many_items() {
        let drop_counts = Cell::new(0);
        {
            let iter = vec![
                DropTracker(&drop_counts),
                DropTracker(&drop_counts),
                DropTracker(&drop_counts),
                DropTracker(&drop_counts),
            ]
            .into_iter();
            let _drop_at_end = iter.try_collect_array::<3>();
            assert_eq!(drop_counts.get(), 4);
        }
        assert_eq!(drop_counts.get(), 4);
    }
}
