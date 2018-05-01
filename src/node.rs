use std::fmt;
use std::mem;

static mut ID: u32 = 0;

pub struct Node {
    t: usize,
    n: usize,
    k: Vec<Key>,
    v: Vec<Value>,
    c: Vec<Node>,
    leaf: bool,
    root: bool,
    id: u32,
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
            v: Vec::with_capacity(t),
            c: match leaf { true  => Vec::new(),
                            false => Vec::with_capacity(t + 1), },
            leaf,
            root: true,
            id: next_id(),
        }
    }

    pub fn set_root_child_and_split(new: &mut Node, mut old: Node) {
        assert!(new.root, "Illegal set of old root on non-root node.");
        assert_eq!(new.n, 0, "New root not empty.");
        old.root = false;
        new.c.push(old);
        // Note: old will be a leaf iff it was a leaf prior to being demoted from root.
        new.split_child(0);
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

    pub fn insert_nonfull(&mut self, k: Key, v: Value) -> Option<Value> {
        match self.k.binary_search(&k) {
            Ok(i)  => Some(mem::replace(&mut self.v[i], v)),
            Err(i) => {
                if self.leaf {
                    self.k.insert(i, k);
                    self.v.insert(i, v);
                    self.n += 1;
                    debug!("Inserted {:?} into {:?}", k, self);
                    None
                } else {
                    let mut i = i;
                    if self.c[i].is_full() {
                        self.split_child(i);
                        if k > self.k[i] {
                            i += 1;
                        }
                    }
                    self.c[i].insert_nonfull(k, v)
                }
            },
        }
    }

    fn split_child(&mut self, i: usize) {
        assert!(!self.leaf, "Cannot split child of a leaf");
        assert!(!self.is_full(), "Can not split child of full parent.");
        debug!("Splitting child {:?} of parent {:?}.", self.c[i], self);

        let (new_k, new_v, new_c, parent_k, parent_v) = self.update_split_child(i);
        let new_child = Node {
            t: self.t,
            n: self.t - 1,
            k: new_k,
            v: new_v,
            c: new_c,
            leaf: self.c[i].leaf,
            root: false,
            id: next_id(),
        };

        self.c.insert(i + 1, new_child);
        self.k.insert(i, parent_k);
        self.v.insert(i, parent_v);
        self.n += 1;
    }

    /// Handles all mutation of the child to be split.
    fn update_split_child(&mut self, i: usize) -> (Vec<Key>, Vec<Value>, Vec<Node>, Key, Value) {
        let child: &mut Node = &mut self.c[i];
        assert!(child.is_full(), "Child to split must be full.");
        let new_c = match child.leaf { true  => Vec::new(),
                                       false => child.c.split_off(self.t), };
        child.n = self.t - 1;

        let mut new_k = child.k.split_off(self.t - 1);
        let parent_k = new_k.remove(0);
        let mut new_v = child.v.split_off(self.t - 1);
        let parent_v = new_v.remove(0);
        (new_k, new_v, new_c, parent_k, parent_v)
    }

    pub fn print_rooted_at(n: &Node, max_nodes: u32) {
        println!("Printing subtree rooted at node {}{}:", n.id, if n.root { " which is the tree root" } else { "" });
        Node::print_recursive(vec![&n], Vec::new(), 0, max_nodes);
    }

    pub fn walk<F, A, E>(&self, program: &F, accumulator: A) -> Result<A, E>
            where F: Fn(&Node, u32, A) -> Result<A, E> {
        Node::walk_r(vec![self], program, accumulator, 0)
    }

    fn walk_r<F, A, E>(siblings: Vec<&Node>, program: &F, mut accumulator: A, height: u32) -> Result<A, E>
            where F: Fn(&Node, u32, A) -> Result<A, E> {
        let mut children = Vec::new();
        for sister in siblings {
            if !sister.leaf {
                let mut c_refs: Vec<&Node> = sister.c.iter().collect::<Vec<_>>();
                children.append(&mut c_refs);
            }
            match program(sister, height, accumulator) {
                Ok(new_acc) => accumulator = new_acc,
                err         => return err,
            }
        }
        if !children.is_empty() {
            children.reverse();
            Node::walk_r(children, program, accumulator, height + 1)
        } else {
            Ok(accumulator)
        }
    }

    fn print_recursive<'a>(mut siblings: Vec<&'a Node>, mut children: Vec<&'a Node>, mut so_far: u32, max_nodes: u32) {
        if let Some(me) = siblings.pop() {
            if so_far < max_nodes {
                print!("{:?}", me);
                so_far += 1;
                if !me.leaf {
                    let mut c_refs: Vec<&'a Node> = me.c.iter().collect::<Vec<_>>();
                    children.append(&mut c_refs);
                }
                if siblings.is_empty() {
                    print!("\n");
                    children.reverse();
                    Node::print_recursive(children, Vec::new(), so_far, max_nodes);
                } else {
                    print!(" -- ");
                    Node::print_recursive(siblings, children, so_far, max_nodes);
                }
            } else {
                print!("...\n...\n");
            }
        }
    }
}

impl fmt::Debug for Node {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            if self.n == 0 {
                write!(f, "({}: {}/{} empty{}{})", self.id, self.t, self.n, if self.leaf { " leaf" } else { "" }, if self.root { " ROOT" } else { "" })
            } else {
                write!(f, "({}: {}/{} [{:?}..={:?}]{}{})", self.id, self.t, self.n, self.k[0], self.k[self.n - 1], if self.leaf { " leaf" } else { "" }, if self.root { " ROOT" } else { "" })
            }
        }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Key(pub u32);

#[derive(PartialEq, Debug)]
pub struct Value(pub String);

#[cfg(test)]
mod tests {
    extern crate rand;

    use super::*;
    use ::BTree;
    use std::collections::HashSet;
    use node::tests::rand::distributions::{IndependentSample, Range};

    fn tree_t_n(t: usize, n: u32) -> BTree {
        let max = 1_000_000_000;
        if n > (0.8 * max as f64) as u32 {
            panic!("Choose a tree size smaller than {}.", (0.8 * max as f64) as u32);
        }
        let between = Range::new(0, max);
        let mut rng = rand::thread_rng();

        let mut tree = BTree::new(t).unwrap();
        let mut i = 0;
        while i < n {
            let v = between.ind_sample(&mut rng);
            let key = Key(v);
            if !tree.contains(&key) {
                tree.insert(key, Value(v.to_string()));
                i += 1;
            }
        }
        tree
    }

    #[test]
    fn new_root() {
        let mut n = Node::new_root(10, true);
        let k = Key(401);
        let v1 = Value("test1".to_string());
        let v2 = Value("test2".to_string());
        assert_eq!(n.n, 0);
        assert!(!n.is_full());
        assert!(n.search(&k).is_none());
        assert!(n.insert_nonfull(k, v1).is_none());
        assert!(n.search(&k).is_some());
        assert!(n.insert_nonfull(k, v2).is_some());
        assert!(n.search(&k).is_some());
    }

    #[test]
    fn only_one_root() {
        let count_roots = |n: &Node, _: u32, a: u32| -> Result<u32, ()> {
            Ok(a + if n.root { 1 } else { 0 })
        };
        
        let mut root = Node::new_root(10, false);
        let root2 = Node::new_root(10, true);
        assert!(root.root);
        assert!(root2.root);
        root.c.push(root2);
        assert_eq!(root.walk(&count_roots, 0).unwrap(), 2);

        assert_eq!(tree_t_n(2, 0).walk(&count_roots, 0).unwrap(), 1);
        assert_eq!(tree_t_n(2, 200).walk(&count_roots, 0).unwrap(), 1);
        assert_eq!(tree_t_n(3, 5).walk(&count_roots, 0).unwrap(), 1);
        assert_eq!(tree_t_n(2, 100000).walk(&count_roots, 0).unwrap(), 1);
        assert_eq!(tree_t_n(1001, 100000).walk(&count_roots, 0).unwrap(), 1);
    }

    #[test]
    fn all_leaves_same_height() {
        let record_height = |n: &Node, h: u32, mut a: HashSet<u32>| -> Result<HashSet<u32>, ()> {
            if n.leaf {
                a.insert(h);
            }
            Ok(a)
        };

        let mut root = Node::new_root(10, false);
        let mut l1 = Node::new_root(10, false);
        let l2 = Node::new_root(10, true);
        let r1 = Node::new_root(10, true);
        assert!(l2.leaf);
        assert!(r1.leaf);
        l1.c.push(l2);
        root.c.push(l1);
        root.c.push(r1);
        assert_eq!(root.walk(&record_height, HashSet::new()).unwrap().len(), 2);

        assert_eq!(tree_t_n(2, 0).walk(&record_height, HashSet::new()).unwrap().len(), 1);
        assert_eq!(tree_t_n(2, 200).walk(&record_height, HashSet::new()).unwrap().len(), 1);
        assert_eq!(tree_t_n(3, 5).walk(&record_height, HashSet::new()).unwrap().len(), 1);
        assert_eq!(tree_t_n(2, 100000).walk(&record_height, HashSet::new()).unwrap().len(), 1);
        assert_eq!(tree_t_n(1001, 100000).walk(&record_height, HashSet::new()).unwrap().len(), 1);
    }

    #[test]
    fn key_counts() {
        // Test that the key count invariants t-1 <= n <= 2t-1 always hold.
        let key_count = |n: &Node, _: u32, _: bool| -> Result<bool, usize> {
            if !n.root && (n.n < n.t - 1 || 2 * n.t - 1 < n.n) {
                Err(n.n)
            } else {
                Ok(true)
            }
        };

        assert!(tree_t_n(2, 0).walk(&key_count, true).is_ok());
        assert!(tree_t_n(2, 200).walk(&key_count, true).is_ok());
        assert!(tree_t_n(3, 5).walk(&key_count, true).is_ok());
        assert!(tree_t_n(2, 100000).walk(&key_count, true).is_ok());
        assert!(tree_t_n(1001, 100000).walk(&key_count, true).is_ok());
    }

    #[test]
    fn child_counts() {
        // Test that there is always exactly one more child than key for all internal nodes.
        let child_count = |n: &Node, _: u32, _: bool| -> Result<bool, String> {
            if n.leaf {
                if n.c.len() > 0 {
                    return Err(format!("Leaf {} has {} children.", n.id, n.c.len()))
                }
            } else if n.c.len() != n.k.len() + 1 {
                return Err(format!("Non-leaf {} has {} children and {} keys.", n.id, n.c.len(), n.k.len()))
            }
            Ok(true)
        };
        
        let mut root = Node::new_root(10, true);
        let root2 = Node::new_root(10, true);
        root.c.push(root2);
        assert!(root.walk(&child_count, true).is_err());

        assert!(tree_t_n(2, 0).walk(&child_count, true).is_ok());
        assert!(tree_t_n(2, 200).walk(&child_count, true).is_ok());
        assert!(tree_t_n(3, 5).walk(&child_count, true).is_ok());
        assert!(tree_t_n(2, 100000).walk(&child_count, true).is_ok());
        assert!(tree_t_n(1001, 100000).walk(&child_count, true).is_ok());
    }

    #[test]
    fn n_key_len() {
        // Test that n is always equal to k.len() and v.len()
        let n_key = |n: &Node, _: u32, _: bool| -> Result<bool, ()> {
            if n.n != n.k.len() || n.n != n.v.len() {
                Err(())
            } else {
                Ok(true)
            }
        };

        assert!(tree_t_n(2, 0).walk(&n_key, true).is_ok());
        assert!(tree_t_n(2, 200).walk(&n_key, true).is_ok());
        assert!(tree_t_n(3, 5).walk(&n_key, true).is_ok());
        assert!(tree_t_n(2, 100000).walk(&n_key, true).is_ok());
        assert!(tree_t_n(1001, 100000).walk(&n_key, true).is_ok());
    }
}
