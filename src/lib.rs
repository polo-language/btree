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
    pub fn new(t: usize) -> BTree {
        BTree {
            root: Node::new_root(t, true),
            t,
            n: 0,
            d: 1,
        }
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

    pub fn print(&self) {
        println!("t: {}, n: {}, d: {}", self.t, self.n, self.d);
        Node::print_rooted_at(&self.root);
    }
}

