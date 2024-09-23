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

        let (mut cursor_pos, mut cursor_val) = match range.start {
            0 => (0, 0),
            start => match NodeSpec::with_node_id(start, node_id_size) {
                // find index of start or, if not found, set cursor to immediately preceding entry
                Ok(node_spec) => match self.inner.binary_search(&NodeSpecPacked::new(node_spec)) {
                    Ok(i) => (i, range.start),
                    Err(0) => (0, range.start),
                    Err(i) => (i - 1, self.inner[i - 1].node_id_as(node_id_size)),
                },
                Err(_) => unreachable!(),
            },
        };

        for e in self.inner.range(cursor_pos..) {
            // compare leading `min` bits of `e` and `cursor_val`
            let min = node_id_size.min(e.node_id_size());
            match e.node_id_as(min).cmp(&(cursor_val >> (node_id_size - min))) {
                cmp::Ordering::Less => {}
                cmp::Ordering::Equal => {
                    cursor_val += 1 << (node_id_size - min);
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

    /// Inserts the specified `node_id` into the list of active `node_id`s.
    ///
    /// This function returns `Ok` if the specified `node_id` has been successfully inserted, no
    /// matter whether it was inserted by the current function call (indicated by `Ok(true)`) or it
    /// had been already inserted (indicated by `Ok(false)`).
    ///
    /// # Errors
    ///
    /// Returns `Err` if the specified `node_id` cannot be inserted because it is reserved by a
    /// "parent" `node_id` or is an intermediate `node_id` with "child" `node_id`s.
    pub fn register(&mut self, node_spec: NodeSpec) -> Result<bool, crate::Error> {
        let node_spec = NodeSpecPacked::new(node_spec);
        match self.binary_search(node_spec) {
            Ok(_) => Ok(false),
            Err(Availability::Ok(index)) => {
                self.inner.insert(index, node_spec);
                Ok(true)
            }
            Err(Availability::HasParent) => {
                Err(crate::Error("could not register node_id: parent exists"))
            }
            Err(Availability::HasChild) => {
                Err(crate::Error("could not register node_id: child exists"))
            }
        }
    }

    /// Removes the specified `node_id` from the list of active `node_id`s.
    ///
    /// This function returns `Ok` if the specified `node_id` has been successfully released and is
    /// available for subsequent `request`s, no matter whether it was released by the current
    /// function call (indicated by `Ok(true)`) or it had been already released (indicated by
    /// `Ok(false)`).
    ///
    /// # Errors
    ///
    /// Returns `Err` if the specified `node_id` cannot be released because it is reserved by a
    /// "parent" `node_id` or is an intermediate `node_id` with "child" `node_id`s.
    pub fn release(&mut self, node_spec: NodeSpec) -> Result<bool, crate::Error> {
        match self.binary_search(NodeSpecPacked::new(node_spec)) {
            Ok(index) => {
                self.inner.remove(index).unwrap();
                Ok(true)
            }
            Err(Availability::Ok(_)) => Ok(false),
            Err(Availability::HasParent) => {
                Err(crate::Error("could not release node_id: parent exists"))
            }
            Err(Availability::HasChild) => {
                Err(crate::Error("could not release node_id: child exists"))
            }
        }
    }

    /// Returns an iterator over currently active `node_id`s.
    pub fn iter(&self) -> impl Iterator<Item = NodeSpec> + '_ {
        self.inner.iter().map(|&n| n.into())
    }

    /// Searches the index of `needle` in the list, returning `Ok(index)` if found or otherwise
    /// `Err` that indicates whether the `needle` can be inserted into the list.
    fn binary_search(&mut self, needle: NodeSpecPacked) -> Result<usize, Availability> {
        match self.inner.binary_search(&needle) {
            Ok(index) => Ok(index),
            Err(index) => {
                if index > 0 {
                    let prev = self.inner[index - 1];
                    let min = needle.node_id_size().min(prev.node_id_size());
                    if needle.node_id_as(min) == prev.node_id_as(min) {
                        return Err(Availability::HasParent);
                    }
                    debug_assert!(needle.node_id_as(min) > prev.node_id_as(min));
                }
                if index < self.inner.len() {
                    let next = self.inner[index];
                    let min = needle.node_id_size().min(next.node_id_size());
                    if needle.node_id_as(min) == next.node_id_as(min) {
                        return Err(Availability::HasChild);
                    }
                    debug_assert!(needle.node_id_as(min) < next.node_id_as(min));
                }
                Err(Availability::Ok(index))
            }
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
        Self {
            inner: node_spec.node_id() << (32 - node_spec.node_id_size())
                | u32::from(node_spec.node_id_size()),
        }
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
}

impl From<NodeSpecPacked> for NodeSpec {
    fn from(value: NodeSpecPacked) -> Self {
        NodeSpec::with_node_id(value.node_id(), value.node_id_size()).unwrap()
    }
}

#[derive(Debug)]
enum Availability {
    Ok(usize),
    HasParent,
    HasChild,
}

#[cfg(test)]
mod tests {
    use std::ops;

    use scru64::generator::NodeSpec;

    use super::{NodeSpecPacked, Registry};

    #[test]
    fn basic() {
        const N: usize = 40_000;
        let mut reg = Registry::default();

        // request
        let mut vec_reg = Vec::new();
        for _ in 0..N {
            let node_id_size = random_node_id_size(1..24);
            if let Ok(issued) = reg.request(node_id_size, ..) {
                assert!(issued.node_prev().is_none());
                assert_eq!(issued.node_id_size(), node_id_size);
                vec_reg.push(pack_node_spec(issued));
            }
        }
        for _ in 0..N {
            let node_id_size = random_node_id_size(1..16);
            if let Ok(issued) = reg.request(node_id_size, ..) {
                assert!(issued.node_prev().is_none());
                assert_eq!(issued.node_id_size(), node_id_size);
                vec_reg.push(pack_node_spec(issued));
            }
        }

        {
            let len = vec_reg.len();
            vec_reg.sort();
            vec_reg.dedup();
            assert_eq!(vec_reg.len(), len);
        }

        assert_eq!(reg.inner, vec_reg);
        for window in vec_reg.windows(2) {
            let (prev, curr) = (window[0], window[1]);
            assert!(prev.node_id_as(23) < curr.node_id_as(23));
            assert!(prev.node_id() < curr.node_id_as(prev.node_id_size()));
            assert!(prev.node_id_as(curr.node_id_size()) < curr.node_id());
        }
        assert!(reg.iter().eq(vec_reg.into_iter().map(NodeSpec::from)));

        {
            let values = Vec::from_iter(reg.iter());

            // register
            for &e in values.iter() {
                let result = reg.register(e);
                assert!(matches!(result, Ok(false)));
            }
            assert!(reg.iter().eq(values.iter().copied()));

            let mut reg_clone = Registry::default();
            for &e in values.iter() {
                let result = reg_clone.register(e);
                assert!(matches!(result, Ok(true)));
            }
            assert!(reg.iter().eq(reg_clone.iter()));

            // release
            for &e in values.iter() {
                let result = reg.release(e);
                assert!(matches!(result, Ok(true)));
            }
            assert!(reg.iter().next().is_none());

            for &e in values.iter() {
                let result = reg.release(e);
                assert!(matches!(result, Ok(false)));
            }
            assert!(reg.iter().next().is_none());
        }
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

    fn pack_node_spec(node_spec: NodeSpec) -> NodeSpecPacked {
        let packed = NodeSpecPacked::new(node_spec);
        let node_id = node_spec.node_id();
        let node_id_size = node_spec.node_id_size();
        assert_eq!(packed.node_id(), node_id);
        assert_eq!(packed.node_id_size(), node_id_size);
        assert_eq!(
            packed
                .node_id_as(23)
                .rotate_right(23 - u32::from(node_id_size)),
            node_id
        );
        packed
    }
}
