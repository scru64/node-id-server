//! This crate includes functions to develop a SCRU64 `node_id` server that assigns
//! non-overlapping `node_id`s of various `node_id_size`s to distributed SCRU64
//! generators. Refer to [the examples directory] for concrete usage.
//!
//! See also [SCRU64 Specification](https://github.com/scru64/spec).
//!
//! [the examples directory]: https://github.com/scru64/node-id-server/tree/main/examples

use std::{collections, error, fmt, time};

use scru64::generator::NodeSpec;

pub mod registry;
use registry::{NodeIdWithSize, Registry};

/// The server engine.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Engine {
    registry: Registry,

    /// Cursors holding the latest `node_id` for each `node_id_size` used  to help `request` locate
    /// the next available `node_id` efficiently.
    cursors: [u32; 23],

    /// A scrambler used to give some random-ish flavor to the ordered and fully deterministic
    /// outputs of `Registry`.
    scrambler: Scrambler,

    /// A set of `node_id`s sorted by their respective expiry time.
    expiry_que: collections::VecDeque<(time::SystemTime, NodeIdWithSize)>,
}

impl Engine {
    /// Creates an instance with `node_id` scrambling enabled.
    ///
    /// Use [`Engine::default`] if scrambling is not necessary.
    pub fn with_scrambling(seed: u64) -> Self {
        Self {
            registry: Default::default(),
            cursors: Default::default(),
            scrambler: Scrambler::from_seed(seed),
            expiry_que: collections::VecDeque::new(),
        }
    }

    /// Issues a new `node_id` of the specified `node_id_size`.
    ///
    /// On success, this function returns the issued `node_id`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if no space for a new `node_id` is available.
    ///
    /// # Panics
    ///
    /// Panics if the `node_id_size` is zero or greater than 23.
    pub fn request(
        &mut self,
        node_id_size: u8,
    ) -> Result<NodeSpec, impl error::Error + Sync + Send> {
        match self.request_inner(node_id_size) {
            Ok(issued) => Ok(self.scrambler.scramble(issued)),
            Err(err) => Err(err),
        }
    }

    /// Issues a new `node_id` of the specified `node_id_size` that will expire after the specified
    /// `time_to_live`.
    ///
    /// On success, this function returns the issued `node_id` and its expiry time.
    ///
    /// # Errors
    ///
    /// Returns `Err` if no space for a new `node_id` is available.
    ///
    /// # Panics
    ///
    /// Panics if the `node_id_size` is zero or greater than 23.
    pub fn request_with_ttl(
        &mut self,
        node_id_size: u8,
        time_to_live: time::Duration,
    ) -> Result<(NodeSpec, time::SystemTime), impl error::Error + Sync + Send> {
        match self.request_inner(node_id_size) {
            Ok(issued) => {
                let expiry_time = self.register_ttl(issued, time_to_live);
                Ok((self.scrambler.scramble(issued), expiry_time))
            }
            Err(err) => Err(err),
        }
    }

    fn request_inner(&mut self, node_id_size: u8) -> Result<NodeSpec, crate::Error> {
        assert!(0 < node_id_size && node_id_size < 24);
        let cursor_index = usize::from(node_id_size) - 1;

        let cursor = self.cursors[cursor_index];
        let result = self.registry.request(node_id_size, cursor..).or_else(|_| {
            let old_len = self.expiry_que.len();

            // vacuum, but reuse an expired item if possible
            let now = time::SystemTime::now();
            while let Some(front) = self.expiry_que.front() {
                if front.0 < now {
                    let front = self.expiry_que.pop_front().unwrap();
                    let mut selected = self.registry.select(front.1.into());
                    match selected.transmute(node_id_size) {
                        Ok(reused) => return Ok(reused),
                        Err(_) => selected.remove().unwrap(),
                    }
                } else {
                    break;
                }
            }

            if self.expiry_que.len() < old_len {
                // vacuum might have released items in (cursor..)
                self.registry.request(node_id_size, ..)
            } else {
                // vacuum did not release anything
                self.registry.request(node_id_size, ..cursor)
            }
        });

        if let Ok(issued) = result {
            self.cursors[cursor_index] = issued.node_id();
            Ok(issued)
        } else {
            Err(crate::Error("could not issue node_id: no space"))
        }
    }

    /// Requests a specified `node_id`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the specified one is already taken.
    pub fn request_one(
        &mut self,
        node_spec: NodeSpec,
    ) -> Result<(), impl error::Error + Sync + Send> {
        let descrambled = self.scrambler.descramble(node_spec);
        self.request_one_inner(descrambled)
    }

    /// Requests a specified `node_id` that will expire after the specified `time_to_live`.
    ///
    /// On success, this function returns the expiry time.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the specified one is already taken.
    pub fn request_one_with_ttl(
        &mut self,
        node_spec: NodeSpec,
        time_to_live: time::Duration,
    ) -> Result<time::SystemTime, impl error::Error + Sync + Send> {
        let descrambled = self.scrambler.descramble(node_spec);
        self.request_one_inner(descrambled)
            .map(|_| self.register_ttl(descrambled, time_to_live))
    }

    fn request_one_inner(&mut self, descrambled: NodeSpec) -> Result<(), crate::Error> {
        let mut selected = self.registry.select(descrambled);
        match selected.insert() {
            Ok(_) => Ok(()), // newly registered
            Err(_) if selected.exists() => {
                let now = time::SystemTime::now();
                let needle = NodeIdWithSize::from_node_spec_lossy(descrambled);
                if let Some(pos) = self
                    .expiry_que
                    .iter()
                    .take_while(|e| e.0 < now)
                    .position(|e| e.1 == needle)
                {
                    debug_assert!({
                        let mut iter = self.expiry_que.range(pos..).fuse();
                        let _ = iter.next();
                        !iter.any(|e| e.1 == needle)
                    });
                    self.expiry_que.remove(pos).unwrap();
                    Ok(()) // existing one was expired
                } else {
                    Err(crate::Error("could not reserve node_id: already taken"))
                }
            }
            Err(_) => {
                let old_len = self.expiry_que.len();
                self.vacuum_conflicting(descrambled);

                // retry if something was removed
                if self.expiry_que.len() < old_len
                    && self.registry.select(descrambled).insert().is_ok()
                {
                    Ok(())
                } else {
                    Err(crate::Error("could not reserve node_id: would overlap"))
                }
            }
        }
    }

    fn register_ttl(
        &mut self,
        descrambled: NodeSpec,
        time_to_live: time::Duration,
    ) -> time::SystemTime {
        let expiry_time = time::SystemTime::now()
            .checked_add(time_to_live)
            .expect("time_to_live was so large that SystemTime overflowed");
        let entry = (
            expiry_time,
            NodeIdWithSize::from_node_spec_lossy(descrambled),
        );
        if self.expiry_que.back().is_some_and(|e| e < &entry) {
            self.expiry_que.push_back(entry); // shortcut for common pattern
        } else if let Err(index) = self.expiry_que.binary_search(&entry) {
            self.expiry_que.insert(index, entry);
        }
        expiry_time
    }

    /// Removes the specified `node_id` from the list of active `node_id`s.
    ///
    /// This function returns `Ok` if the specified `node_id` has been successfully released and is
    /// available for subsequent [`Engine::request`]s, no matter whether it was released by the
    /// current function call or it had been already released.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the specified `node_id` cannot be released because it is reserved by a
    /// "parent" `node_id` or is an intermediate `node_id` with "child" `node_id`s.
    pub fn release(&mut self, node_spec: NodeSpec) -> Result<(), impl error::Error + Sync + Send> {
        let descrambled = self.scrambler.descramble(node_spec);
        let mut selected = self.registry.select(descrambled);
        match selected.remove() {
            Ok(_) => {
                let needle = NodeIdWithSize::from_node_spec_lossy(descrambled);
                if let Some(pos) = self.expiry_que.iter().position(|e| e.1 == needle) {
                    debug_assert!({
                        let mut iter = self.expiry_que.range(pos..).fuse();
                        let _ = iter.next();
                        !iter.any(|e| e.1 == needle)
                    });
                    self.expiry_que.remove(pos).unwrap();
                }
                Ok(())
            }
            Err(_) if selected.is_insertable() => {
                debug_assert!({
                    let needle = NodeIdWithSize::from_node_spec_lossy(descrambled);
                    !self.expiry_que.iter().any(|e| e.1 == needle)
                });
                Ok(())
            }
            Err(_) => {
                let old_len = self.expiry_que.len();
                self.vacuum_conflicting(descrambled);

                // retry if something was removed
                if self.expiry_que.len() < old_len
                    && self.registry.select(descrambled).is_insertable()
                {
                    Ok(())
                } else {
                    Err(crate::Error("could not release node_id: would overlap"))
                }
            }
        }
    }

    /// Checks the expiry of existing `node_id`s and physically removes expired entries from the
    /// list.
    pub fn vacuum(&mut self) {
        let now = time::SystemTime::now();
        while let Some(front) = self.expiry_que.front() {
            if front.0 < now {
                let front = self.expiry_que.pop_front().unwrap();
                self.registry.select(front.1.into()).remove().unwrap();
            } else {
                break;
            }
        }
    }

    fn vacuum_conflicting(&mut self, descrambled: NodeSpec) {
        let now = time::SystemTime::now();
        let mut i = 0;
        while i < self.expiry_que.len() {
            if self.expiry_que[i].0 < now {
                let expired = self.expiry_que[i].1.into();
                if overlapping(expired, descrambled) {
                    self.registry.select(expired).remove().unwrap();
                    self.expiry_que.remove(i).unwrap();
                } else {
                    i += 1;
                }
            } else {
                break;
            }
        }
    }

    /// Returns an iterator over managed `node_id`s.
    ///
    /// The iterator may produce already expired `node_id`s. Call [`Engine::vacuum`] in advance to
    /// sweep expired entries.
    pub fn iter(&self) -> impl Iterator<Item = NodeSpec> + '_ {
        self.registry.iter().map(|e| self.scrambler.scramble(e))
    }
}

/// An XOR mask that symmetrically `scramble`s and `descramble`s `node_id`s.
///
/// Note that the `Default::default` constructor disables the scrambling.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct Scrambler {
    mask: u32,
}

impl Scrambler {
    fn scramble(&self, node_spec: NodeSpec) -> NodeSpec {
        self.xor(node_spec)
    }

    fn descramble(&self, node_spec: NodeSpec) -> NodeSpec {
        self.xor(node_spec)
    }

    fn xor(&self, node_spec: NodeSpec) -> NodeSpec {
        let mut node_id = node_spec.node_id();
        node_id <<= 32 - node_spec.node_id_size();
        node_id ^= self.mask;
        node_id >>= 32 - node_spec.node_id_size();
        NodeSpec::with_node_id(node_id, node_spec.node_id_size()).unwrap()
    }

    fn from_seed(seed: u64) -> Self {
        // PCG32
        const MUL: u64 = 6364136223846793005;
        const INC: u64 = 3608283273833198889;
        let s = INC.wrapping_add(seed).wrapping_mul(MUL).wrapping_add(INC);
        let xorshifted = (((s >> 18) ^ s) >> 27) as u32;
        let mask = xorshifted.rotate_right((s >> 59) as u32);
        Self { mask }
    }
}

/// A crate-local anonymous error type.
#[derive(Debug)]
struct Error(&'static str);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

impl error::Error for Error {}

/// Returns `true` if two `node_id`s are overlapping with each other.
///
/// # Examples
///
/// ```rust
/// use scru64_node_id_server::overlapping;
///
/// assert!(overlapping("0x8/4".parse()?, "0x84/8".parse()?));
/// assert!(!overlapping("0x8/4".parse()?, "0x088/12".parse()?));
/// # Ok::<_, Box<dyn std::error::Error>>(())
/// ```
pub fn overlapping(a: NodeSpec, b: NodeSpec) -> bool {
    let min = a.node_id_size().min(b.node_id_size());
    (a.node_id() >> (a.node_id_size() - min)) == (b.node_id() >> (b.node_id_size() - min))
}

#[cfg(test)]
mod tests {
    use std::{thread, time};

    use super::{overlapping, Engine, NodeSpec, Scrambler};

    #[test]
    fn basics() {
        let node_id_size = 16;
        let mut eng = Engine::default();

        for i in 0..(1 << node_id_size) {
            let node_spec = eng.request(node_id_size).unwrap();
            assert_eq!(node_spec.node_id(), i);
            assert_eq!(node_spec.node_id_size(), node_id_size);
        }

        for i in 1..24 {
            assert!(eng.request(i).is_err());
        }

        for i in 0..(1 << node_id_size) {
            let node_spec = NodeSpec::with_node_id(i, node_id_size).unwrap();
            assert!(eng.request_one(node_spec).is_err());
            assert!(eng.release(node_spec).is_ok());
            assert!(eng.release(node_spec).is_ok());
            assert!(eng.request_one(node_spec).is_ok());
            assert!(eng.request_one(node_spec).is_err());
        }
        assert!(eng.request(node_id_size).is_err());
    }

    #[test]
    fn with_scrambling() {
        let node_id_size = 16;
        let seed = rand::random();
        let scrambler = Scrambler::from_seed(seed);
        let mut eng = Engine::with_scrambling(seed);

        for i in 0..(1 << node_id_size) {
            let scrambled = eng.request(node_id_size).unwrap();
            let descrambled = scrambler.descramble(scrambled);
            assert_eq!(descrambled.node_id(), i);
            assert_eq!(descrambled.node_id_size(), node_id_size);
        }

        for i in 1..24 {
            assert!(eng.request(i).is_err());
        }

        for i in 0..(1 << node_id_size) {
            let descrambled = NodeSpec::with_node_id(i, node_id_size).unwrap();
            let scrambled = scrambler.scramble(descrambled);
            assert!(eng.request_one(scrambled).is_err());
            assert!(eng.release(scrambled).is_ok());
            assert!(eng.release(scrambled).is_ok());
            assert!(eng.request_one(scrambled).is_ok());
            assert!(eng.request_one(scrambled).is_err());
        }
        assert!(eng.request(node_id_size).is_err());
    }

    #[test]
    fn with_ttl() {
        let node_id_size = 8;
        let time_to_live = time::Duration::from_millis(64);
        let mut eng = Engine::default();

        for i in 0..(1 << node_id_size) {
            let (node_spec, _) = eng.request_with_ttl(node_id_size, time_to_live).unwrap();
            assert_eq!(node_spec.node_id(), i);
            assert_eq!(node_spec.node_id_size(), node_id_size);
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for _ in 0..(1 << node_id_size) {
            assert!(eng.request_with_ttl(node_id_size, time_to_live).is_ok());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for i in 0..(1 << node_id_size) {
            let node_spec = NodeSpec::with_node_id(i, node_id_size).unwrap();
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_ok());
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_err());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for _ in 0..(1 << (node_id_size - 4)) {
            assert!(eng.request_with_ttl(node_id_size - 4, time_to_live).is_ok());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for _ in 0..(1 << (node_id_size + 4)) {
            assert!(eng.request_with_ttl(node_id_size + 4, time_to_live).is_ok());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for i in 0..(1 << (node_id_size - 4)) {
            let node_spec = NodeSpec::with_node_id(i, node_id_size - 4).unwrap();
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_ok());
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_err());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        for i in 0..(1 << (node_id_size + 4)) {
            let node_spec = NodeSpec::with_node_id(i, node_id_size + 4).unwrap();
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_ok());
            assert!(eng.request_one_with_ttl(node_spec, time_to_live).is_err());
        }
        assert!(eng.request_with_ttl(node_id_size, time_to_live).is_err());
        thread::sleep(time_to_live);

        eng.vacuum();
        assert!(eng.iter().next().is_none());
    }

    #[test]
    fn fn_overlapping() {
        fn test_pair(a: &str, b: &str) -> bool {
            let (a, b) = (a.parse().unwrap(), b.parse().unwrap());
            let (x, y) = (overlapping(a, b), overlapping(b, a));
            assert_eq!(x, y);
            x
        }

        assert!(test_pair("0x2/4", "0x21/8"));
        assert!(test_pair("0x2/4", "0x22/8"));
        assert!(!test_pair("0x2/4", "0x13/8"));
        assert!(!test_pair("0x2/4", "0x44/8"));
    }
}
