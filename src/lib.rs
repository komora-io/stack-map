use std::borrow::Borrow;
use std::mem::MaybeUninit;

/// `StackMap` is a constant-size, zero-allocation associative container
/// backed by an array. It can be used as a building block for various interesting
/// higher-level data structures.
#[derive(Debug)]
pub struct StackMap<K: Clone + Ord, V: Clone, const FANOUT: usize> {
    len: usize,
    inner: [MaybeUninit<(K, V)>; FANOUT],
}

impl<K: Clone + Ord, V: Clone, const FANOUT: usize> Drop for StackMap<K, V, FANOUT> {
    fn drop(&mut self) {
        for i in 0..self.len() {
            let ptr = self.inner[i].as_mut_ptr();
            unsafe {
                std::ptr::drop_in_place(ptr);
            }
        }
    }
}

impl<K: Clone + Ord, V: Clone, const FANOUT: usize> Clone for StackMap<K, V, FANOUT> {
    fn clone(&self) -> Self {
        let mut inner: [MaybeUninit<(K, V)>; FANOUT] =
            core::array::from_fn(|_i| MaybeUninit::uninit());

        for (i, item) in self.iter().cloned().enumerate() {
            inner[i].write(item);
        }

        StackMap {
            inner,
            len: self.len,
        }
    }
}

impl<K: Clone + Ord, V: Clone, const FANOUT: usize> Default for StackMap<K, V, FANOUT> {
    fn default() -> Self {
        StackMap {
            inner: core::array::from_fn(|_i| MaybeUninit::uninit()),
            len: 0,
        }
    }
}

impl<K: Clone + Ord, V: Clone, const FANOUT: usize> StackMap<K, V, FANOUT> {
    fn binary_search<Q>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner[..self.len()]
            .binary_search_by_key(&key, |slot| unsafe { slot.assume_init_ref().0.borrow() })
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(index) = self.binary_search(key) {
            Some(unsafe { &self.inner.get_unchecked(index).assume_init_ref().1 })
        } else {
            None
        }
    }

    /// Inserts an item and return the previous value if it exists.
    ///
    /// # Panics
    ///
    /// This method will panic if called with a new key-value pair when
    /// already full.
    ///
    /// The `StackMap` should be checked to ensure that it is not already
    /// full before calling this method. It is full when the `self.is_full()`
    /// method returns `true`, which happens when `self.len() == FANOUT`.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.binary_search(&key) {
            Ok(index) => {
                let slot = unsafe { &mut self.inner.get_unchecked_mut(index).assume_init_mut().1 };
                Some(std::mem::replace(slot, value))
            }
            Err(index) => {
                assert!(self.len() < FANOUT);

                unsafe {
                    if index < self.len() {
                        let src = self.inner.get_unchecked(index).as_ptr();
                        let dst = self.inner.get_unchecked_mut(index + 1).as_mut_ptr();

                        std::ptr::copy(src, dst, self.len() - index);
                    }

                    self.len += 1;

                    self.inner.get_unchecked_mut(index).write((key, value));
                }
                None
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(index) = self.binary_search(key) {
            unsafe {
                let ret = std::ptr::read(self.inner.get_unchecked(index).as_ptr()).1;

                if index + 1 < self.len() {
                    let src = self.inner.get_unchecked(index + 1).as_ptr();
                    let dst = self.inner.get_unchecked_mut(index).as_mut_ptr();

                    std::ptr::copy(src, dst, self.len() - index);
                }

                self.len -= 1;

                Some(ret)
            }
        } else {
            None
        }
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.binary_search(key).is_ok()
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &(K, V)> {
        self.inner[..self.len()]
            .iter()
            .map(|slot| unsafe { slot.assume_init_ref() })
    }

    /// Splits this `StackMap` into two. `self` will retain
    /// all key-value pairs before the provided split index.
    /// Returns the split key at the given split index and
    /// a new `StackMap` created out of all key-value pairs
    /// at or after the provided split index.
    pub fn split_off(&mut self, split_idx: usize) -> (K, Self) {
        assert!(split_idx < self.len());
        assert!(split_idx < FANOUT);

        let split_key = unsafe { self.inner[split_idx].assume_init_ref().0.clone() };

        let mut rhs = Self::default();

        for i in split_idx..self.len() {
            let src = self.inner[i].as_ptr();
            let dst = rhs.inner[i - split_idx].as_mut_ptr();
            unsafe {
                std::ptr::copy_nonoverlapping(src, dst, 1);
            }
        }

        rhs.len = self.len - split_idx;
        self.len = split_idx;

        (split_key, rhs)
    }

    /// Get a key-value pair based on its internal relative
    /// index in the backing array.
    pub fn get_index(&self, index: usize) -> Option<&(K, V)> {
        if index < self.len() {
            Some(unsafe { self.inner.get_unchecked(index).assume_init_ref() })
        } else {
            None
        }
    }

    /// Get the key-value pair that is less than or equal
    /// to the provided key. Useful for any least upper
    /// bound operation, such as MVCC lookups where the
    /// key is suffixed by a version or an internal b-tree
    /// index lookup where you are looking for the next
    /// node based on a node's low key.
    ///
    /// # Examples
    /// ```
    /// let mut map = stack_map::StackMap::<u8, u8, 64>::default();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    /// map.insert(3, 3);
    ///
    /// let lt = map.get_less_than_or_equal(&4).unwrap();
    /// let expected = &(3, 3);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than_or_equal(&3).unwrap();
    /// let expected = &(3, 3);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than_or_equal(&2).unwrap();
    /// let expected = &(2, 2);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than_or_equal(&1).unwrap();
    /// let expected = &(1, 1);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than_or_equal(&0);
    /// let expected = None;
    /// assert_eq!(expected, lt);
    /// ```
    pub fn get_less_than_or_equal<Q>(&self, key: &Q) -> Option<&(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        // binary search LUB
        let index = match self.binary_search(key) {
            Ok(i) => i,
            Err(0) => return None,
            Err(i) => i - 1,
        };

        self.get_index(index)
    }

    /// Gets a kv pair that has a key that is less than the provided key.
    ///
    /// # Examples
    /// ```
    /// let mut map = stack_map::StackMap::<u8, u8, 64>::default();
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    /// map.insert(3, 3);
    ///
    /// let lt = map.get_less_than(&4).unwrap();
    /// let expected = &(3, 3);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than(&3).unwrap();
    /// let expected = &(2, 2);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than(&2).unwrap();
    /// let expected = &(1, 1);
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than(&1);
    /// let expected = None;
    /// assert_eq!(expected, lt);
    ///
    /// let lt = map.get_less_than(&0);
    /// let expected = None;
    /// assert_eq!(expected, lt);
    /// ```
    pub fn get_less_than<Q>(&self, key: &Q) -> Option<&(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        // binary search LUB
        let index = match self.binary_search(key) {
            Ok(0) | Err(0) => return None,
            Ok(i) => i - 1,
            Err(i) => i - 1,
        };

        self.get_index(index)
    }

    pub const fn is_full(&self) -> bool {
        self.len == FANOUT
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}
