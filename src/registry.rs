use std::{cmp, collections, ops};

use super::NodeSpec;

/// A structure that maintains the list of active `node_id`s by issuing new ones upon `request` and
/// removing existing ones upon `release`.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
#[serde(transparent)]
pub struct Registry {
    /// A sorted set of active `node_id`s.
    inner: collections::VecDeque<NodeSpecPacked>,
}

impl Registry {
    /// Issues a new `node_id` of the specified `node_id_size` within the given `node_id` range.
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
    ) -> Result<NodeSpec, crate::Error> {
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
            return Err(crate::Error("could not issue node_id: empty range"));
        }

        // find index of start or, if not found, set cursor to immediately preceding position
        let mut cursor_pos = match range.start {
            0 => 0,
            start => {
                let needle =
                    NodeSpecPacked::new(NodeSpec::with_node_id(start, node_id_size).unwrap());
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
                        return Err(crate::Error("could not issue node_id: no space"));
                    }
                }
                cmp::Ordering::Greater => break,
            }
            cursor_pos += 1;
        }

        match NodeSpec::with_node_id(cursor_val, node_id_size) {
            Ok(node_spec) => {
                self.inner
                    .insert(cursor_pos, NodeSpecPacked::new(node_spec));
                Ok(node_spec)
            }
            Err(_) => unreachable!(),
        }
    }

    /// Returns an iterator over currently active `node_id`s.
    pub fn iter(&self) -> impl Iterator<Item = NodeSpec> + '_ {
        self.inner.iter().map(|&n| n.into())
    }

    /// Searches the `needle` in the list, returning a handle to insert or remove the selected
    /// value without breaking the uniqueness and order of elements.
    pub fn select(&mut self, needle: NodeSpec) -> Selected {
        let value = NodeSpecPacked::new(needle);
        Selected {
            value,
            position: self.inner.binary_search(&value),
            registry: &mut self.inner,
        }
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

/// A handle to insert or remove the selected value into/from `Registry` while maintaining the
/// uniqueness and order of elements.
#[derive(Debug)]
pub struct Selected<'r> {
    value: NodeSpecPacked,
    position: Result<usize, usize>,
    registry: &'r mut collections::VecDeque<NodeSpecPacked>,
}

impl Selected<'_> {
    /// Returns `true` if the selected value exists in the `Registry`.
    pub fn exists(&self) -> bool {
        self.position.is_ok()
    }

    /// Returns `true` if the selected value can be inserted into the `Registry`.
    pub fn is_insertable(&self) -> bool {
        let index = match self.position {
            Ok(_) => return false,
            Err(index) => index,
        };

        if index > 0 {
            match self.value.cmp_as_min(&self.registry[index - 1]) {
                cmp::Ordering::Less => unreachable!(),
                cmp::Ordering::Equal => return false,
                cmp::Ordering::Greater => {}
            }
        }
        if index < self.registry.len() {
            match self.value.cmp_as_min(&self.registry[index]) {
                cmp::Ordering::Less => {}
                cmp::Ordering::Equal => return false,
                cmp::Ordering::Greater => unreachable!(),
            }
        }
        true
    }

    /// Tries to insert the selected value into the `Registry`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the selected value cannot be inserted because inserting it would result in
    /// conflict or overlap with other existing `node_id`s.
    pub fn insert(&mut self) -> Result<(), crate::Error> {
        if self.is_insertable() {
            let index = self.position.unwrap_err();
            self.registry.insert(index, self.value);
            self.position = Ok(index);
            Ok(())
        } else {
            Err(crate::Error("could not insert node_id: would overlap"))
        }
    }

    /// Tries to remove the selected value from the `Registry`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the selected value does not exist in the `Registry`.
    pub fn remove(&mut self) -> Result<(), crate::Error> {
        if let Ok(index) = self.position {
            self.registry.remove(index).unwrap();
            self.position = Err(index);
            Ok(())
        } else {
            Err(crate::Error("could not remove node_id: not found"))
        }
    }
}

/// A packed and sortable internal representation of `node_id` and `node_id_size`.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, serde::Serialize, serde::Deserialize,
)]
#[repr(transparent)]
#[serde(transparent)]
pub struct NodeSpecPacked {
    inner: u32,
}

impl NodeSpecPacked {
    pub fn new(node_spec: NodeSpec) -> Self {
        let node_id = node_spec.node_id();
        let node_id_size = node_spec.node_id_size();
        let packed = Self {
            inner: node_id << (32 - node_id_size) | u32::from(node_id_size),
        };
        #[cfg(test)]
        {
            assert_eq!(packed.node_id(), node_id);
            assert_eq!(packed.node_id_size(), node_id_size);
            let rotated = packed
                .node_id_as(23)
                .rotate_right(23 - u32::from(node_id_size));
            assert_eq!(rotated, node_id);
        }
        packed
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

impl From<NodeSpecPacked> for NodeSpec {
    fn from(value: NodeSpecPacked) -> Self {
        NodeSpec::with_node_id(value.node_id(), value.node_id_size()).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use std::ops;

    use super::Registry;

    #[test]
    fn basic() {
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
