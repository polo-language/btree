pub mod node;
pub mod iter;

use self::node::Node;
use self::iter::Iter;

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
where
    K: Ord,
{
    /// Creates a new `BTree` of order `t`.
    pub fn new(t: usize) -> BTree<K, V> {
        assert!(2 <= t);
        BTree {
            root: Node::new_root(t, true),
            t,
            n: 0,
            d: 1,
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
            let new_root = Node::new_root(self.t, false);
            let old_root = mem::replace(&mut self.root, new_root);
            Node::set_root_child_and_split(&mut self.root, old_root);
            self.d += 1;
        }
        match self.root.insert(key, value) {
            None => {
                self.n += 1;
                None
            }
            some => some,
        }
    }

    /// Deletes the mapping for the provided `key`.
    /// Returns the previous value if the tree did contain a mapping, `None` otherwise.
    pub fn delete(&mut self, key: &K) -> Option<V> {
        match self.root.delete(&key) {
            (None, None) => None,
            (some_v, None) => {
                self.n -= 1;
                some_v
            }
            (some_v, Some(new_root)) => {
                self.n -= 1;
                self.d -= 1;
                self.root = new_root;
                some_v
            }
        }
    }

    /// Removes all mappings.
    pub fn clear(&mut self) {
        *self = BTree::new(self.t);
    }

    /// Returns an iterator over entries in the BTree in ascending order
    pub fn iter(&self) -> Iter<K, V> {
        self.root.iter()
    }

    /// Walks the tree by level order traversal.
    /// The folding operation `program` has access to the current depth at each node.
    /// Returns the final accumulator value, or the first error encountered.
    pub fn walk<F, A, E>(&self, program: &F, accumulator: A) -> Result<A, E>
    where
        F: Fn(&Node<K, V>, u32, A) -> Result<A, E>,
    {
        self.root.walk(program, accumulator)
    }
}

impl<K, V> BTree<K, V>
where
    K: Ord + Debug
{
    /// Print up to `max_nodes` of the tree, by level order traversal.
    pub fn print(&self, max_nodes: u32) {
        println!("t: {}, n: {}, d: {}", self.t, self.n, self.d);
        Node::print_subtree(&self.root, max_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic;

    fn catch_unwind_silent<F: FnOnce() -> R + panic::UnwindSafe, R>(
        f: F,
    ) -> std::thread::Result<R> {
        let prev_hook = panic::take_hook();
        panic::set_hook(Box::new(|_| {}));
        let result = panic::catch_unwind(f);
        panic::set_hook(prev_hook);
        result
    }

    #[test]
    fn new_tree() {
        let tree = BTree::<u32, String>::new(2);
        assert!(tree.is_empty());
        assert!(!tree.root.is_full());
        assert_eq!(tree.d, 1);
        assert!(!tree.contains(&0));
    }

    #[test]
    fn new_tree_min_deg() {
        let result = catch_unwind_silent(|| BTree::<u32, String>::new(0));
        assert!(result.is_err());
        let result = catch_unwind_silent(|| BTree::<u32, String>::new(1));
        assert!(result.is_err());
        // These don't fail.
        BTree::<u32, String>::new(2);
        BTree::<u32, String>::new(10);
        BTree::<u32, String>::new(8899000);
    }

    #[test]
    fn insert_search() {
        let mut tree = BTree::<u32, String>::new(2);
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

    #[test]
    fn clear() {
        let mut tree = BTree::<u32, String>::new(2);
        assert!(tree.is_empty());
        for i in 0..100 {
            tree.insert(i, i.to_string());
        }
        assert!(!tree.is_empty());
        tree.clear();
        assert!(tree.is_empty());
    }
}
