//! Low-level [`Registry`] data structure and related items.

use std::{cmp, collections, error, fmt, ops};

use super::NodeSpec;

/// A low-level data structure that maintains the list of active `node_id`s.
///
/// # Examples
///
/// ```rust
/// use scru64_node_id_server::registry::Registry;
///
/// let mut reg = Registry::default();
/// let a = reg.request(4, ..)?;
/// let b = reg.request(4, ..)?;
/// let c = reg.request(8, ..)?;
/// let d = reg.request(8, ..)?;
/// let e = reg.request(12, ..)?;
///
/// assert_eq!((a.node_id(), a.node_id_size()), (0x0, 4));
/// assert_eq!((b.node_id(), b.node_id_size()), (0x1, 4));
/// assert_eq!((c.node_id(), c.node_id_size()), (0x20, 8));
/// assert_eq!((d.node_id(), d.node_id_size()), (0x21, 8));
/// assert_eq!((e.node_id(), e.node_id_size()), (0x220, 12));
///
/// reg.select("42/8".parse()?).insert()?;
/// reg.select("42/8".parse()?).remove()?;
/// # Ok::<_, Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
#[serde(transparent)]
pub struct Registry {
    /// A sorted set of active `node_id`s.
    inner: collections::VecDeque<NodeIdWithSize>,
}

impl Registry {
    /// Issues a new `node_id` of the specified `node_id_size` within the given `node_id` range.
    ///
    /// This method returns the smallest `node_id` available within the range by performaing a
    /// linear search in the internal sorted list of active `node_id`s. Specifying an appropriate
    /// start bound of `node_id_range` allows skipping the occupied region and may substantially
    /// accelerate the linear search process.
    ///
    /// # Errors
    ///
    /// Returns `Err` if no space for a new `node_id` is available within the range.
    ///
    /// # Panics
    ///
    /// Panics if the `node_id_size` is zero or greater than 23.
    pub fn request(
        &mut self,
        node_id_size: u8,
        node_id_range: impl ops::RangeBounds<u32>,
    ) -> Result<NodeSpec, RequestError> {
        assert!(0 < node_id_size && node_id_size < 24);

        // express range in canonical half-open form (start..end)
        let range: ops::Range<u32> = match node_id_range.start_bound() {
            ops::Bound::Unbounded => 0,
            ops::Bound::Included(&start) => start,
            ops::Bound::Excluded(start) => start.saturating_add(1),
        }..match node_id_range.end_bound() {
            ops::Bound::Unbounded => u32::MAX,
            ops::Bound::Included(end) => end.saturating_add(1),
            ops::Bound::Excluded(&end) => end,
        }
        .min(1 << node_id_size);
        if range.start >= range.end {
            return Err(RequestError {
                kind: "empty range",
            });
        }

        // find index of start or, if not found, set cursor to immediately preceding position
        let mut cursor_pos = match range.start {
            0 => 0,
            start => {
                let needle = NodeIdWithSize::from_node_spec_lossy(
                    NodeSpec::with_node_id(start, node_id_size).unwrap(),
                );
                match self.inner.back() {
                    None => 0,
                    Some(last) if last <= &needle => self.inner.len() - 1, // hot path
                    Some(_) => match self.inner.binary_search(&needle) {
                        Ok(i) => i,
                        Err(0) => 0,
                        Err(i) => i - 1,
                    },
                }
            }
        };

        let mut cursor_val = range.start;
        for e in self.inner.range(cursor_pos..) {
            // compare leading `min` bits of `e` and `cursor_val`
            let min = node_id_size.min(e.node_id_size());
            let cursor_val_as_min = cursor_val >> (node_id_size - min);
            match e.node_id_as(min).cmp(&cursor_val_as_min) {
                cmp::Ordering::Less => {}
                cmp::Ordering::Equal => {
                    cursor_val = (cursor_val_as_min + 1) << (node_id_size - min);
                    if cursor_val >= range.end {
                        return Err(RequestError { kind: "no space" });
                    }
                }
                cmp::Ordering::Greater => break,
            }
            cursor_pos += 1;
        }

        match NodeSpec::with_node_id(cursor_val, node_id_size) {
            Ok(node_spec) => {
                self.inner
                    .insert(cursor_pos, NodeIdWithSize::from_node_spec_lossy(node_spec));
                Ok(node_spec)
            }
            Err(_) => unreachable!(),
        }
    }

    /// Searches the `needle` in the list, returning a handle to insert or remove the selected
    /// value without breaking the uniqueness and order of `node_id`s.
    pub fn select(&mut self, needle: NodeSpec) -> Selected {
        let value = NodeIdWithSize::from_node_spec_lossy(needle);
        Selected {
            value,
            position: self.inner.binary_search(&value),
            registry: self,
        }
    }

    /// Returns an iterator over currently active `node_id`s.
    pub fn iter(&self) -> impl Iterator<Item = NodeSpec> + '_ {
        self.inner.iter().map(|&n| n.into())
    }

    /// Tests if the specified `value` can be stored at `Ok(position)` or inserted before
    /// `Err(position)` without breaking the uniqueness and order of `node_id`s.
    ///
    /// `position` typically is a result of `VecDeque::binary_search()`.
    fn check_new_value(&self, value: NodeIdWithSize, position: Result<usize, usize>) -> bool {
        let (current, next) = match position {
            Ok(index) => (index, index + 1),
            Err(index) => (index, index),
        };

        if current > 0 {
            match value.cmp_as_min(&self.inner[current - 1]) {
                cmp::Ordering::Less => unreachable!(),
                cmp::Ordering::Equal => return false,
                cmp::Ordering::Greater => {}
            }
        }
        if next < self.inner.len() {
            match value.cmp_as_min(&self.inner[next]) {
                cmp::Ordering::Less => {}
                cmp::Ordering::Equal => return false,
                cmp::Ordering::Greater => unreachable!(),
            }
        }
        true
    }

    #[cfg(test)]
    fn verify_inner(&self) {
        let mut iter = self.inner.iter();
        if let Some(mut prev) = iter.next() {
            for curr in iter {
                assert!(prev < curr);
                assert!(prev.cmp_as_min(curr).is_lt());
                assert!(prev.node_id_as(23) < curr.node_id_as(23));
                prev = curr;
            }
        }
    }
}

/// A handle to insert or remove the selected value into/from [`Registry`] while maintaining the
/// uniqueness and order of `node_id`s.
///
/// This structure is primarily meant to cache a result of expensive binary search while holding
/// the reference to `Registry` so the result won't be invalidated by other operations.
#[derive(Debug)]
pub struct Selected<'r> {
    value: NodeIdWithSize,
    position: Result<usize, usize>,
    registry: &'r mut Registry,
}

impl Selected<'_> {
    /// Returns `true` if the selected value exists in the [`Registry`].
    pub fn exists(&self) -> bool {
        self.position.is_ok()
    }

    /// Returns `true` if the selected value can be inserted into the [`Registry`].
    pub fn is_insertable(&self) -> bool {
        match self.position {
            Ok(_) => false,
            Err(index) => self.registry.check_new_value(self.value, Err(index)),
        }
    }

    /// Tries to insert the selected value into the [`Registry`].
    ///
    /// # Errors
    ///
    /// Returns `Err` if the selected value cannot be inserted because doing so would result in
    /// conflict or overlap with other existing `node_id`s.
    pub fn insert(&mut self) -> Result<(), impl error::Error + Sync + Send> {
        if self.is_insertable() {
            let index = self.position.unwrap_err();
            self.registry.inner.insert(index, self.value);
            self.position = Ok(index);
            Ok(())
        } else {
            Err(crate::Error("could not insert node_id: would overlap"))
        }
    }

    /// Tries to remove the selected value from the [`Registry`].
    ///
    /// # Errors
    ///
    /// Returns `Err` if the selected value does not exist in the `Registry`.
    pub fn remove(&mut self) -> Result<(), impl error::Error + Sync + Send> {
        if let Ok(index) = self.position {
            self.registry.inner.remove(index).unwrap();
            self.position = Err(index);
            Ok(())
        } else {
            Err(crate::Error("could not remove node_id: not found"))
        }
    }

    /// Reinterprets the selected value as that of `new_node_id_size`, returning the reinterpreted
    /// value on success.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the selected value does not exist or cannot be transmuted because doing so
    /// would result in conflict or overlap with other existing `node_id`s.
    ///
    /// # Panics
    ///
    /// Panics if the `new_node_id_size` is zero or greater than 23.
    pub fn transmute(
        &mut self,
        new_node_id_size: u8,
    ) -> Result<NodeSpec, impl error::Error + Sync + Send> {
        assert!(0 < new_node_id_size && new_node_id_size < 24);
        if let Ok(index) = self.position {
            let new_spec =
                NodeSpec::with_node_id(self.value.node_id_as(new_node_id_size), new_node_id_size)
                    .unwrap();
            let new_id_with_size = NodeIdWithSize::from_node_spec_lossy(new_spec);
            if self.registry.check_new_value(new_id_with_size, Ok(index)) {
                self.registry.inner[index] = new_id_with_size;
                self.value = new_id_with_size;
                Ok(new_spec)
            } else {
                Err(crate::Error("could not transmute node_id: would overlap"))
            }
        } else {
            Err(crate::Error("could not transmute node_id: not found"))
        }
    }
}

/// A packed and sortable internal representation of `node_id` and `node_id_size` pair.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, serde::Serialize, serde::Deserialize,
)]
#[repr(transparent)]
#[serde(transparent)]
pub(crate) struct NodeIdWithSize {
    inner: u32,
}

impl NodeIdWithSize {
    pub fn from_node_spec_lossy(node_spec: NodeSpec) -> Self {
        let node_id = node_spec.node_id();
        let node_id_size = node_spec.node_id_size();
        let value = Self {
            inner: node_id << (32 - node_id_size) | u32::from(node_id_size),
        };
        #[cfg(test)]
        {
            assert_eq!(value.node_id(), node_id);
            assert_eq!(value.node_id_size(), node_id_size);
            let rotated = value
                .node_id_as(23)
                .rotate_right(23 - u32::from(node_id_size));
            assert_eq!(rotated, node_id);
        }
        value
    }

    fn node_id_size(self) -> u8 {
        (self.inner & 0xff) as u8
    }

    fn node_id(self) -> u32 {
        self.node_id_as(self.node_id_size())
    }

    fn node_id_as(self, node_id_size: u8) -> u32 {
        assert!(0 < node_id_size && node_id_size < 24);
        self.inner >> (32 - node_id_size)
    }

    fn cmp_as_min(&self, other: &Self) -> cmp::Ordering {
        let min = cmp::min(self.node_id_size(), other.node_id_size());
        self.node_id_as(min).cmp(&other.node_id_as(min))
    }
}

impl From<NodeIdWithSize> for NodeSpec {
    fn from(value: NodeIdWithSize) -> Self {
        NodeSpec::with_node_id(value.node_id(), value.node_id_size()).unwrap()
    }
}

/// An error reported by [`Registry::request`] on failure.
#[derive(Debug)]
pub struct RequestError {
    kind: &'static str,
}

impl fmt::Display for RequestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "could not issue node_id: {}", self.kind)
    }
}

impl error::Error for RequestError {}

#[cfg(test)]
mod tests {
    use std::ops;

    use super::Registry;

    #[test]
    fn basics() {
        const N: usize = 40_000;
        let mut reg = Registry::default();

        // request
        for _ in 0..N {
            let node_id_size = random_node_id_size(1..24);
            if let Ok(issued) = reg.request(node_id_size, ..) {
                assert!(issued.node_prev().is_none());
                assert_eq!(issued.node_id_size(), node_id_size);
            }
        }
        for _ in 0..N {
            let node_id_size = random_node_id_size(1..16);
            if let Ok(issued) = reg.request(node_id_size, ..) {
                assert!(issued.node_prev().is_none());
                assert_eq!(issued.node_id_size(), node_id_size);
            }
        }
        reg.verify_inner();

        let values = Vec::from_iter(reg.iter());

        // register and release
        for &e in values.iter() {
            let mut selected = reg.select(e);
            assert!(selected.exists());
            assert!(!selected.is_insertable());
            let result = selected.insert();
            assert!(result.is_err());
        }
        assert!(reg.iter().eq(values.iter().copied()));

        for &e in values.iter() {
            let mut selected = reg.select(e);
            assert!(selected.exists());
            assert!(!selected.is_insertable());
            let result = selected.remove();
            assert!(result.is_ok());
            assert!(!selected.exists());
            assert!(selected.is_insertable());
        }
        assert!(reg.iter().next().is_none());

        for &e in values.iter() {
            let mut selected = reg.select(e);
            assert!(!selected.exists());
            assert!(selected.is_insertable());
            let result = selected.remove();
            assert!(result.is_err());
        }
        assert!(reg.iter().next().is_none());

        for &e in values.iter() {
            let mut selected = reg.select(e);
            assert!(!selected.exists());
            assert!(selected.is_insertable());
            let result = selected.insert();
            assert!(result.is_ok());
            assert!(selected.exists());
            assert!(!selected.is_insertable());
        }
        assert!(reg.iter().eq(values.iter().copied()));
    }

    #[test]
    fn request_range_start() {
        let mut reg = Registry::default();

        assert_eq!(reg.request(8, 0x0..).unwrap().node_id(), 0x00);
        assert_eq!(reg.request(8, 0x0..).unwrap().node_id(), 0x01);
        assert_eq!(reg.request(8, 0x8..).unwrap().node_id(), 0x08);
        assert_eq!(reg.request(8, 0x8..).unwrap().node_id(), 0x09);
        assert_eq!(reg.request(8, 0x4..).unwrap().node_id(), 0x04);
        assert_eq!(reg.request(8, 0x4..).unwrap().node_id(), 0x05);

        assert_eq!(reg.request(12, 0x20..).unwrap().node_id(), 0x020);
        assert_eq!(reg.request(12, 0x20..).unwrap().node_id(), 0x021);
        assert_eq!(reg.request(12, 0x40..).unwrap().node_id(), 0x060);
        assert_eq!(reg.request(12, 0x40..).unwrap().node_id(), 0x061);
        assert_eq!(reg.request(12, 0x48..).unwrap().node_id(), 0x062);
        assert_eq!(reg.request(12, 0x48..).unwrap().node_id(), 0x063);
        assert_eq!(reg.request(12, 0xa0..).unwrap().node_id(), 0x0a0);
        assert_eq!(reg.request(12, 0xa0..).unwrap().node_id(), 0x0a1);

        assert_eq!(reg.request(8, 0x10..).unwrap().node_id(), 0x10);
        assert_eq!(reg.request(8, 0x10..).unwrap().node_id(), 0x11);
        assert_eq!(reg.request(4, 0x1..).unwrap().node_id(), 0x2);
        assert_eq!(reg.request(4, 0x0..).unwrap().node_id(), 0x3);

        assert_eq!(reg.request(12, 0x600..).unwrap().node_id(), 0x600);
        assert_eq!(reg.request(12, 0x600..).unwrap().node_id(), 0x601);
        assert_eq!(reg.request(12, 0x234..).unwrap().node_id(), 0x400);
        assert_eq!(reg.request(12, 0x234..).unwrap().node_id(), 0x401);

        assert_eq!(reg.request(4, 0x0..).unwrap().node_id(), 0x5);
        assert_eq!(reg.request(4, 0x0..).unwrap().node_id(), 0x7);
        assert_eq!(reg.request(8, 0x78..).unwrap().node_id(), 0x80);
        assert_eq!(reg.request(12, 0x808..).unwrap().node_id(), 0x810);

        reg.verify_inner();
    }

    #[test]
    fn transmute() {
        let mut reg = Registry::default();

        assert!(reg.select("0x02/8".parse().unwrap()).transmute(8).is_err());

        for i in 0..16 {
            reg.request(8, i..).unwrap();
            reg.request(12, i..).unwrap();
        }

        assert_eq!(
            reg.select("0x02/8".parse().unwrap()).transmute(8).unwrap(),
            "0x02/8".parse().unwrap()
        );
        assert_eq!(
            reg.select("0x02/8".parse().unwrap()).transmute(12).unwrap(),
            "0x020/12".parse().unwrap()
        );
        assert_eq!(
            reg.select("0x020/12".parse().unwrap())
                .transmute(8)
                .unwrap(),
            "0x02/8".parse().unwrap()
        );
        assert!(reg.select("0x02/8".parse().unwrap()).transmute(4).is_err());

        assert!(reg
            .select("0x010/12".parse().unwrap())
            .transmute(8)
            .is_err());
        assert!(reg
            .select("0x01f/12".parse().unwrap())
            .transmute(8)
            .is_err());

        reg.verify_inner();
    }

    fn random_node_id_size(range: ops::Range<u8>) -> u8 {
        let end = range.end - range.start - 1;
        let random = rand::random::<u32>() >> (32 - end);
        for i in 0..=end {
            if random < (1u32 << i) {
                return range.start + i;
            }
        }
        unreachable!();
    }
}
