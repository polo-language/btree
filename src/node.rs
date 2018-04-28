use std::fmt;

static mut ID: u32 = 0;

pub struct Node {
    t: usize,
    n: usize,
    k: Vec<Key>,
    c: Vec<Node>,
    leaf: bool,
    root: bool,
    id: u32,
    // data: ...,
}

fn next_id() -> u32 {
    unsafe {
        let current = ID;
        ID += 1;
        current
    }
}

impl Node {
    pub fn new_root(t: usize, leaf: bool) -> Node {
        Node {
            t,
            n: 0,
            k: Vec::with_capacity(t),
            c: match leaf { true  => Vec::new(),
                            false => Vec::with_capacity(t + 1), },
            leaf,
            root: true,
            id: next_id(),
        }
    }

    pub fn set_root_child_and_split(new: &mut Node, mut old: Node) {
        assert!(new.root, "Illegal set of old root on non-root node.");
        new.c[0] = old;
        old.root = false;
        new.split_child(0);
    }

    pub fn is_empty_root(&self) -> bool {
        assert!(self.root, "Should not be checking if a non-root node is empty.");
        self.n == 0
    }

    pub fn search(&self, key: &Key) -> Option<(&Node, usize)> {
        let mut i = 0;
        debug!("Searching node {:?} for key {:?}", self, key);
        while i < self.n && key > &self.k[i] {
            i += 1;
        }
        if i < self.n && key == &self.k[i] {
            debug!("Search - found key {:?} at node {}", key, self.id);
            Some((&self, i))
        } else {
            if self.leaf {
                None
            } else {
                self.c[i].search(key)
            }
        }
    }

    pub fn is_full(&self) -> bool {
        self.n >= 2 * self.t - 1
    }

    pub fn insert_nonfull(&mut self, k: Key) -> Result<(), &'static str> {
        match self.k.binary_search(&k) {
            Ok(_)  => Err("Attempting to insert duplicate key."),
            Err(i) => {
                if self.leaf {
                    self.k.insert(i, k);
                    self.n += 1;
                    debug!("Inserted {:?} into leaf {:?}", k, self);
                    Ok(())
                } else {
                    let mut i = i + 1;
                    if self.c[i].is_full() {
                        self.split_child(i);
                        if k > self.k[i] {
                            i += 1;
                        }
                    }
                    self.c[i].insert_nonfull(k)
                }
            },
        }
    }

    fn split_child(&mut self, i: usize) {
        assert!(!self.leaf, "Cannot split child of a leaf");
        assert!(!self.is_full(), "Can not split child of full parent.");
        debug!("Splitting child.");

        let (new_k, new_c, parent_k) = self.update_split_child(i);
        let new_child = Node {
            t: self.t,
            n: self.t - 1,
            k: new_k,
            c: new_c,
            leaf: self.c[i].leaf,
            root: false,
            id: next_id(),
        };

        self.c.insert(i + 1, new_child);
        self.k.insert(i, parent_k);
        self.n += 1;
    }

    fn update_split_child(&mut self, i: usize) -> (Vec<Key>, Vec<Node>, Key) {
        let child: &mut Node = &mut self.c[i];
        assert!(child.is_full(), "Child to split must be full.");
        let new_c = match child.leaf {
            true  => Vec::new(),
            false => child.c.split_off(self.t + 1),
        };
        child.n = self.t - 1;

        let mut new_k = child.k.split_off(self.t);
        let parent_k = new_k.remove(0);
        (new_k, new_c, parent_k)
    }
}

impl fmt::Debug for Node {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "({}: {}/{} [{:?}..={:?}])", self.id, self.t, self.n, self.k[0], self.k[self.n-1])
        }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Key(pub u32);

