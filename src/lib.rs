#[macro_use]
extern crate log;

pub mod node;

pub use self::node::Node;
pub use self::node::Key;

use std::mem;

pub struct BTree {
    root: Node,
    t: usize,
    n: u32,
    d: u32,
}

impl BTree {
    pub fn new(t: usize) -> Result<BTree, &'static str> {
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

    pub fn size(&self) -> u32 {
        self.n
    }

    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    pub fn search(&self, key: &Key) -> Option<(&Node, usize)> {
        if self.root.is_empty_root() {
            None
        } else {
            self.root.search(key)
        }
    }

    pub fn insert(&mut self, key: Key) -> Result<(), &'static str> {
        if self.root.is_full() {
            debug!("Splitting root.");
            let new_root = Node::new_root(self.t, false);
            let old_root = mem::replace(&mut self.root, new_root);
            Node::set_root_child_and_split(&mut self.root, old_root);
            self.d += 1;
        }
        self.root.insert_nonfull(key).map(|ok| {
                self.n += 1;
                ok
        })
    }

    pub fn print(&self, max_nodes: u32) {
        println!("t: {}, n: {}, d: {}", self.t, self.n, self.d);
        Node::print_rooted_at(&self.root, max_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_tree() {
        let tree = BTree::new(2).unwrap();
        assert!(tree.root.is_empty_root());
        assert!(!tree.root.is_full());
        assert_eq!(tree.d, 1);
        assert!(tree.search(&Key(0)).is_none());
    }

    #[test]
    fn new_tree_min_deg() {
        assert!(BTree::new(0).is_err());
        assert!(BTree::new(1).is_err());
        assert!(BTree::new(2).is_ok());
        assert!(BTree::new(10).is_ok());
        assert!(BTree::new(8899000).is_ok());
    }

    #[test]
    fn insert_search() {
        let mut tree = BTree::new(2).unwrap();
        let k = Key(10);
        assert!(tree.search(&k).is_none());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 0);
        assert!(tree.insert(k).is_ok());
        assert!(tree.search(&k).is_some());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 1);
        assert!(tree.insert(k).is_err());
        assert!(tree.search(&k).is_some());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 1);
        assert!(tree.insert(Key(4)).is_ok());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 2);
        assert!(tree.insert(Key(200001)).is_ok());
        assert_eq!(tree.d, 1);
        assert_eq!(tree.size(), 3);
        assert!(tree.insert(Key(204401)).is_ok());
        assert_eq!(tree.d, 2);
        assert_eq!(tree.size(), 4);
    }
}
