pub mod node;

pub use self::node::Node;
pub use self::node::Key;

pub struct BTree {
    root: Node,
    t: usize,
    empty: bool,
}

impl BTree {
    pub fn new(t: usize) -> BTree {
        BTree {
            root: Node::new(t),
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

}

