#[macro_use]
extern crate log;

pub mod node;

use self::node::Node;

use std::fmt::Debug;
use std::mem;

/// B-tree data structure. Stores key-value pairs in a self-balancing tree.
/// Provides the usual map operations.
/// The order of the tree is half of the maximum number of key-value pairs storable on each node.
pub struct BTree<K, V> {
    /// Root of the tree
    root: Node<K, V>,
    /// Order of the tree
    t: usize,
    /// Number of elements contained in the tree
    n: u32,
    /// Depth of the tree, including the root and leaf layers
    d: u32,
}

impl<K, V> BTree<K, V>
    where K: PartialEq + Eq + PartialOrd + Ord + Clone + Copy + Debug,
          V: PartialEq + Debug
{
    /// Creates a new `BTree` of order `t`.
    pub fn new(t: usize) -> Result<BTree<K, V>, &'static str> {
        if t < 2 {
            Err("The minimum degree of a btree must be >= 2.")
        } else {
            Ok(BTree {
                root: Node::new_root(t, true),
                t,
                n: 0,
                d: 1,
            })
        }
    }

    /// Returns the current number of elements contained in the tree
    pub fn size(&self) -> u32 {
        self.n
    }

    /// Whether the tree is empty or not
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// Whether the tree contains an entry for `key`
    pub fn contains(&self, key: &K) -> bool {
        self.n > 0 && self.root.search(key).is_some()
    }

    /// Returns the value associated with `key`, if a mapping exists.
    pub fn get(&self, key: &K) -> Option<&V> {
        if self.n > 0 {
            self.root.get(key)
        } else {
            None
        }
    }

    /// Inserts the key-value pair into the tree.
    /// Returns the previous value if the tree contained a mapping for `key`, `None` otherwise.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.root.is_full() {
            debug!("Splitting root.");
            let new_root = Node::new_root(self.t, false);
            let old_root = mem::replace(&mut self.root, new_root);
            Node::set_root_child_and_split(&mut self.root, old_root);
            self.d += 1;
        }
        match self.root.insert(key, value) {
            None => { self.n += 1;
                      None },
            some =>   some,
        }
    }

    /// Deletes the mapping for the provided `key`.
    /// Returns the previous value if the tree did contain a mapping, `None` otherwise.
    pub fn delete(&mut self, key: &K) -> Option<V> {
        match self.root.delete(&key) {
            (None, None)             =>   None,
            (some_v, None)           => { self.n -= 1;
                                          some_v },
            (some_v, Some(new_root)) => { self.n -= 1;
                                          self.d -= 1;
                                          self.root = new_root;
                                          some_v },
        }
    }

    /// Print up to `max_nodes` of the tree, by level order traversal.
    pub fn print(&self, max_nodes: u32) {
        println!("t: {}, n: {}, d: {}", self.t, self.n, self.d);
        Node::print_subtree(&self.root, max_nodes);
    }

    /// Walks the tree by level order traversal.
    /// The folding operation `program` has access to the current depth at each node.
    /// Returns the final accumulator value, or the first error encountered.
    pub fn walk<F, A, E>(&self, program: &F, accumulator: A) -> Result<A, E>
            where F: Fn(&Node<K, V>, u32, A) -> Result<A, E> {
        self.root.walk(program, accumulator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_tree() {
        let tree = BTree::<u32, String>::new(2).unwrap();
        assert!(tree.is_empty());
        assert!(!tree.root.is_full());
        assert_eq!(tree.d, 1);
        assert!(!tree.contains(&0));
    }

    #[test]
    fn new_tree_min_deg() {
        assert!(BTree::<u32, String>::new(0).is_err());
        assert!(BTree::<u32, String>::new(1).is_err());
        assert!(BTree::<u32, String>::new(2).is_ok());
        assert!(BTree::<u32, String>::new(10).is_ok());
        assert!(BTree::<u32, String>::new(8899000).is_ok());
    }

    #[test]
    fn insert_search() {
        let mut tree = BTree::<u32, String>::new(2).unwrap();
        let k = 10;
        assert!(!tree.contains(&k));
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 0);
        assert!(tree.insert(k, "abc".to_string()).is_none());
        assert!(tree.contains(&k));
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 1);
        assert!(tree.insert(k, "zyxabc".to_string()).is_some());
        assert!(tree.contains(&k));
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 1);
        assert!(tree.insert(4, "      ".to_string()).is_none());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 2);
        assert!(tree.insert(200001, "__bc".to_string()).is_none());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 3);
        assert!(tree.insert(204401, "abc".to_string()).is_none());
        assert_eq!(tree.d, 2);
        assert_eq!(tree.size(), 4);
    }
}
