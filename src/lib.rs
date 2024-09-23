//! This crate includes functions to develop a SCRU64 `node_id` server that assigns
//! non-overlapping `node_id`s of various `node_id_size`s to distributed SCRU64
//! generators. Refer to [the examples directory] for concrete usage.
//!
//! See also [SCRU64 Specification](https://github.com/scru64/spec).
//!
//! [the examples directory]: https://github.com/scru64/node-id-server/tree/main/examples

use std::{collections, error, fmt, time};

use scru64::generator::NodeSpec;

mod registry;
use registry::{NodeSpecPacked, Registry};

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
    expiry_que: collections::VecDeque<(time::SystemTime, NodeSpecPacked)>,
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

        let issued = self
            .registry
            .request(node_id_size, self.cursors[cursor_index]..)
            .or_else(|_| {
                self.vacuum();
                self.registry.request(node_id_size, ..)
            })?;

        self.cursors[cursor_index] = issued.node_id();
        Ok(issued)
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
        if self.registry.register(descrambled)? {
            Ok(()) // newly registered
        } else {
            let now = time::SystemTime::now();
            let needle = NodeSpecPacked::new(descrambled);
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
    }

    fn register_ttl(
        &mut self,
        descrambled: NodeSpec,
        time_to_live: time::Duration,
    ) -> time::SystemTime {
        let expiry_time = time::SystemTime::now()
            .checked_add(time_to_live)
            .expect("time_to_live was so large that SystemTime overflowed");
        let entry = (expiry_time, NodeSpecPacked::new(descrambled));
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
        match self.registry.release(descrambled) {
            Ok(_) => {
                let needle = NodeSpecPacked::new(descrambled);
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
            Err(err) => Err(err),
        }
    }

    /// Checks the expiry of existing `node_id`s and physically removes expired entries from the
    /// list.
    pub fn vacuum(&mut self) {
        let now = time::SystemTime::now();
        while let Some(front) = self.expiry_que.front() {
            if front.0 < now {
                let _ = self.registry.release(front.1.into());
                self.expiry_que.pop_front().unwrap();
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

/// A crate-local error type.
#[derive(Debug)]
struct Error(&'static str);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

impl error::Error for Error {}
