pub mod node;

pub use self::node::Node;
pub use self::node::Key;

use std::mem;

pub struct BTree {
    root: Node,
    t: usize,
    empty: bool,
}

impl BTree {
    pub fn new(t: usize) -> BTree {
        BTree {
            root: Node::new_root(t, true),
            t,
            empty: true,
        }
    }

    pub fn search(&self, key: &Key) -> Option<(&Node, usize)> {
        if self.empty {
            None
        } else {
            self.root.search(key)
        }
    }

    pub fn insert(&mut self, key: Key) -> Result<(), &'static str> {
        if self.root.is_full() {
            let new_root = Node::new_root(self.t, false);
            let old_root = mem::replace(&mut self.root, new_root);
            Node::set_root_child_and_split(&mut self.root, old_root);
        }
        self.root.insert_nonfull(key)
    }
}

