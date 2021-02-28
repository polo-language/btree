use std::fmt;
use std::fmt::Debug;
use std::mem;

pub struct Node<K, V> {
    t: usize,
    n: usize,
    k: Vec<K>,
    v: Vec<V>,
    c: Vec<Node<K, V>>,
    leaf: bool,
    root: bool,
}

impl<K, V> Node<K, V>
    where K: PartialEq + Eq + PartialOrd + Ord + Clone + Copy + Debug,
          V: PartialEq + Debug
{
    pub fn new_root(t: usize, leaf: bool) -> Node<K, V> {
        Node {
            t,
            n: 0,
            k: Vec::with_capacity(t),
            v: Vec::with_capacity(t),
            c: match leaf { true  => Vec::new(),
                            false => Vec::with_capacity(t + 1), },
            leaf,
            root: true,
        }
    }

    pub fn set_root_child_and_split(new: &mut Node<K, V>, mut old: Node<K, V>) {
        assert!(new.root, "Illegal set of old root on non-root node.");
        assert_eq!(new.n, 0, "New root not empty.");
        old.root = false;
        new.c.push(old);
        // Note: old will be a leaf iff it was a leaf prior to being demoted from root.
        new.split_child(0);
    }

    pub fn search(&self, key: &K) -> Option<(&Node<K, V>, usize)> {
        let mut i = 0;
        debug!("Searching node {:?} for key {:?}", self, key);
        while i < self.n && key > &self.k[i] {
            i += 1;
        }
        if i < self.n && key == &self.k[i] {
            debug!("Search - found key {:?} at node {:?}", key, self);
            Some((&self, i))
        } else {
            if self.leaf {
                None
            } else {
                self.c[i].search(key)
            }
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        match self.search(key) {
            Some((ref n, i)) => n.v.get(i),
            None             => None,
        }
    }

    pub fn is_full(&self) -> bool {
        self.n >= 2 * self.t - 1
    }

    pub fn insert_nonfull(&mut self, k: K, v: V) -> Option<V> {
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
        };

        self.c.insert(i + 1, new_child);
        self.k.insert(i, parent_k);
        self.v.insert(i, parent_v);
        self.n += 1;
    }

    /// Handles all mutation of the child to be split.
    fn update_split_child(&mut self, i: usize) -> (Vec<K>, Vec<V>, Vec<Node<K, V>>, K, V) {
        let child = &mut self.c[i];
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

    /// self is always a tree root.
    /// Returns the new root node if it was replaced.
    pub fn delete(&mut self, key: &K) -> (Option<V>, Option<Node<K, V>>) {
        assert!(self.root, "Node::delete may only be called on a tree root.");
        if self.n == 1 && !self.leaf {
            if self.k[0] == *key {
                let (mid_k, mid_v) = self.c[0].delete_extreme(true); // Could alternately delete min of self.c[1].
                let right = self.c.remove(1);
                let mut left = self.c.remove(0);
                Node::merge(&mut left, (mid_k, mid_v), right);
                return (Some(self.v.remove(0)), Some(left))
            } else if self.c[0].n < self.t && self.c[1].n < self.t {
                self.merge_children(0);
                let opt_v = self.c[0].delete_r(key);
                return (opt_v, Some(self.c.remove(0)))
            }
        }
        (self.delete_r(key), None)
    }

    fn delete_r(&mut self, key: &K) -> Option<V> {
        if self.leaf {
            match self.k.binary_search(&key) {
                Ok(i)  => { self.n -= 1;
                            self.k.remove(i);
                            Some(self.v.remove(i)) },
                Err(_) =>   None,
            }
        } else {
            match self.k.binary_search(&key) {
                Ok(i) => {
                    // 0 <= i <= n - 1
                    if self.c[i].n >= self.t {
                        let (new_k, new_v) = self.c[i].delete_extreme(true);
                        mem::replace(&mut self.k[i], new_k);
                        Some(mem::replace(&mut self.v[i], new_v))
                    } else if self.c[i + 1].n >= self.t {
                        let (new_k, new_v) = self.c[i + 1].delete_extreme(false);
                        mem::replace(&mut self.k[i], new_k);
                        Some(mem::replace(&mut self.v[i], new_v))
                    } else {
                        self.merge_children(i);
                        self.c[i].delete_r(key)
                    }
                },
                Err(i) => {
                    // 0 <= i <= n
                    // key is in self.c[i] if we have it.
                    self.ensure_has_t_keys(i);
                    self.c[i].delete_r(key)
                },
            }
        }
    }

    /// Deletes and returns the highest/lowest key in the subtree rooted at self,
    /// which is always to be found in a leaf.
    fn delete_extreme(&mut self, is_max: bool) -> (K, V) {
        if self.leaf {
            self.n -= 1;
            if is_max {
                (self.k.pop().unwrap(), self.v.pop().unwrap())
            } else {
                (self.k.remove(0), self.v.remove(0))
            }
        } else {
            let i = if is_max { self.n } else { 0 };
            self.ensure_has_t_keys(i);
            self.c[i].delete_extreme(is_max)
        }
    }

    fn ensure_has_t_keys(&mut self, i: usize) {
        if self.c[i].n < self.t {
            if i > 0 && self.c[i - 1].n >= self.t {
                let child_k = self.c[i - 1].k.pop().unwrap();
                let child_v = self.c[i - 1].v.pop().unwrap();
                let child_c = self.c[i - 1].c.pop().unwrap();
                let k = mem::replace(&mut self.k[i], child_k);
                let v = mem::replace(&mut self.v[i], child_v);
                let c = mem::replace(&mut self.c[i], child_c);
                self.c[i].k.insert(0, k);
                self.c[i].v.insert(0, v);
                self.c[i].c.insert(0, c);
                self.c[i - 1].n -= 1;
                self.c[i].n += 1;
            } else if i < self.n && self.c[i + 1].n >= self.t {
                let child_k = self.c[i + 1].k.remove(0);
                let child_v = self.c[i + 1].v.remove(0);
                let child_c = self.c[i + 1].c.remove(0);
                let k = mem::replace(&mut self.k[i], child_k);
                let v = mem::replace(&mut self.v[i], child_v);
                let c = mem::replace(&mut self.c[i], child_c);
                self.k.push(k);
                self.v.push(v);
                self.c.push(c);
                self.c[i].n += 1;
                self.c[i + 1].n -= 1;
            } else {
                if i < self.n {
                    self.merge_children(i);
                } else if 0 < i {
                    self.merge_children(i - 1);
                }
            }
        }
    }

    fn merge_children(&mut self, left_i: usize) {
        let right_c = self.c.remove(left_i + 1);
        let k = self.k.remove(left_i);
        let v = self.v.remove(left_i);
        self.n -= 1;
        Node::merge(&mut self.c[left_i], (k, v), right_c);
    }

    /// Merges all content from right into left.
    fn merge(left: &mut Node<K, V>, mid: (K, V), mut right: Node<K, V>) {
        left.k.push(mid.0);
        for k in right.k.drain(..) {
            left.k.push(k);
        }
        left.v.push(mid.1);
        for v in right.v.drain(..) {
            left.v.push(v);
        }
        for c in right.c.drain(..) {
            left.c.push(c);
        }
        left.n += right.n;
        // right is dropped.
    }

    pub fn print_rooted_at(n: &Node<K, V>, max_nodes: u32) {
        println!("Printing subtree rooted at node {:?}{}:", n, if n.root { " which is the tree root" } else { "" });
        Node::print_recursive(vec![&n], Vec::new(), 0, max_nodes);
    }

    pub fn walk<F, A, E>(&self, program: &F, accumulator: A) -> Result<A, E>
            where F: Fn(&Node<K, V>, u32, A) -> Result<A, E> {
        Node::walk_r(vec![self], program, accumulator, 0)
    }

    fn walk_r<F, A, E>(siblings: Vec<&Node<K, V>>, program: &F, mut accumulator: A, height: u32) -> Result<A, E>
            where F: Fn(&Node<K, V>, u32, A) -> Result<A, E> {
        let mut children = Vec::new();
        for sister in siblings {
            if !sister.leaf {
                let mut c_refs: Vec<&Node<K, V>> = sister.c.iter().collect::<Vec<_>>();
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

    fn print_recursive<'a>(mut siblings: Vec<&'a Node<K, V>>, mut children: Vec<&'a Node<K, V>>, mut so_far: u32, max_nodes: u32) {
        if let Some(me) = siblings.pop() {
            if so_far < max_nodes {
                print!("{:?}", me);
                so_far += 1;
                if !me.leaf {
                    let mut c_refs: Vec<&'a Node<K, V>> = me.c.iter().collect::<Vec<_>>();
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

impl<K, V> fmt::Debug for Node<K, V>
    where K: PartialEq + Eq + PartialOrd + Ord + Clone + Copy + Debug,
          V: PartialEq + Debug
{
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            if self.n == 0 {
                write!(f, "({}/{} empty{}{})", self.t, self.n, if self.leaf { " leaf" } else { "" }, if self.root { " ROOT" } else { "" })
            } else {
                write!(f, "({}/{} [{:?}..={:?}]{}{})", self.t, self.n, self.k[0], self.k[self.n - 1], if self.leaf { " leaf" } else { "" }, if self.root { " ROOT" } else { "" })
            }
        }
}

#[cfg(test)]
mod tests {
    extern crate rand;

    const MAX_TREE_SIZE: u32 = 1_000_000_000;

    use super::*;
    use ::BTree;
    use std::collections::HashSet;
    use node::tests::rand::distributions::{Distribution, Uniform};

    /// Creates a tree of order t and fills it with n random unique integer keys
    /// and values equal to the keys' string values.
    fn tree_t_n(t: usize, n: u32) -> BTree<u32, String> {
        if n > (0.8 * MAX_TREE_SIZE as f64) as u32 {
            panic!("Choose a tree size smaller than {}.",
                    (0.8 * MAX_TREE_SIZE as f64) as u32);
        }
        let between = Uniform::new(0, MAX_TREE_SIZE);
        let mut rng = rand::thread_rng();

        let mut tree = BTree::new(t).unwrap();
        let mut i = 0;
        while i < n {
            let key = between.sample(&mut rng);
            if !tree.contains(&key) {
                tree.insert(key, key.to_string());
                i += 1;
            }
        }
        tree
    }

    #[test]
    fn new_root() {
        let mut n = Node::<u32, String>::new_root(10, true);
        let k = 401;
        let v1 = "test1".to_string();
        let v2 = "test2".to_string();
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
        let count_roots = |n: &Node<u32, String>, _: u32, a: u32| -> Result<u32, ()> {
            Ok(a + if n.root { 1 } else { 0 })
        };
        
        let mut root = Node::<u32, String>::new_root(10, false);
        let root2 = Node::<u32, String>::new_root(10, true);
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
        let record_height = |n: &Node<u32, String>, h: u32, mut a: HashSet<u32>| -> Result<HashSet<u32>, ()> {
            if n.leaf {
                a.insert(h);
            }
            Ok(a)
        };

        let mut root = Node::<u32, String>::new_root(10, false);
        let mut l1 = Node::<u32, String>::new_root(10, false);
        let l2 = Node::<u32, String>::new_root(10, true);
        let r1 = Node::<u32, String>::new_root(10, true);
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
        let key_count = |n: &Node<u32, String>, _: u32, _: bool| -> Result<bool, usize> {
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
        let child_count = |n: &Node<u32, String>, _: u32, _: bool| -> Result<bool, String> {
            if n.leaf {
                if n.c.len() > 0 {
                    return Err(format!("Leaf {:?} has {} children.", n, n.c.len()))
                }
            } else if n.c.len() != n.k.len() + 1 {
                return Err(format!("Non-leaf {:?} has {} children and {} keys.", n, n.c.len(), n.k.len()))
            }
            Ok(true)
        };
        
        let mut root = Node::<u32, String>::new_root(10, true);
        let root2 = Node::<u32, String>::new_root(10, true);
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
        let n_key = |n: &Node<u32, String>, _: u32, _: bool| -> Result<bool, ()> {
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

    #[test]
    fn retrieve() {
        let mut tree = BTree::<u32, String>::new(2).unwrap();
        let k = 6;
        assert!(!tree.contains(&k));
        assert!(tree.insert(k, "abc".to_string()).is_none());
        assert!(tree.contains(&k));
        let prev1 = tree.insert(k, "123;.&".to_string());
        assert!(prev1.is_some());
        assert_eq!(prev1.unwrap(), "abc".to_string());
        let prev2 = tree.insert(k, "   ___".to_string());
        assert!(prev2.is_some());
        assert_eq!(prev2.unwrap(), "123;.&".to_string());

        let mut tree = tree_t_n(5, 350);
        let k = 6;
        tree.insert(k, "abc".to_string());
        assert!(tree.contains(&k));
        let prev1 = tree.insert(k, "123;.&".to_string());
        assert!(prev1.is_some());
        assert_eq!(prev1.unwrap(), "abc".to_string());
        let prev2 = tree.insert(k, "   ___".to_string());
        assert!(prev2.is_some());
        assert_eq!(prev2.unwrap(), "123;.&".to_string());
    }

    #[test]
    fn get() {
        let mut tree = BTree::<u32, String>::new(2).unwrap();
        let k = 40091;
        assert!(!tree.contains(&k));
        assert!(tree.insert(k, "abc".to_string()).is_none());
        assert!(tree.contains(&k));
        let prev1 = tree.get(&k);
        assert!(prev1.is_some());
        assert_eq!(prev1.unwrap(), &"abc".to_string());
        assert!(tree.contains(&k));
        let k2 = 101;
        assert!(!tree.contains(&k2));
        assert!(tree.get(&k2).is_none());

        let mut tree = tree_t_n(5, 350);
        let k = 40091;
        tree.insert(k, "abc".to_string());
        assert!(tree.contains(&k));
        let prev1 = tree.get(&k);
        assert!(prev1.is_some());
        assert_eq!(prev1.unwrap(), &"abc".to_string());
        assert!(tree.contains(&k));
    }

    #[test]
    fn delete_from_root() {
        let mut tree = BTree::<u32, String>::new(2).unwrap();
        let k = 40091;
        let v = "abc".to_string();
        let v_copy = v.clone();
        let d = tree.delete(&k);
        assert!(d.is_none());
        assert!(tree.is_empty());
        tree.insert(k, v);
        assert!(!tree.is_empty());
        let d = tree.delete(&k);
        assert!(tree.is_empty());
        assert!(d.is_some());
        assert_eq!(d.unwrap(), v_copy);
        assert!(tree.delete(&k).is_none());
        let k = 6;
        let k2 = 9;
        let v = "test test  ".to_string();
        let v_copy = v.clone();
        let v2 = "test test  2".to_string();
        let v_copy2 = v2.clone();
        tree.insert(k, v);
        tree.insert(k2, v2);
        assert_eq!(tree.n, 2);
        let d = tree.delete(&k);
        assert!(d.is_some());
        assert_eq!(d.unwrap(), v_copy);
        assert!(tree.delete(&k).is_none());
        assert!(!tree.is_empty());
        let d2 = tree.delete(&k2);
        assert!(d2.is_some());
        assert_eq!(d2.unwrap(), v_copy2);
        assert!(tree.delete(&k2).is_none());
        assert!(tree.is_empty());
    }

    #[test]
    fn delete() {
        let mut tree = tree_t_n(5, 350);
        let k = 40091;
        let v = "abc".to_string();
        let v_copy = v.clone();
        tree.insert(k, v);
        let d1 = tree.delete(&k);
        assert!(d1.is_some());
        assert_eq!(d1.unwrap(), v_copy);
        assert!(tree.delete(&k).is_none());
    }
}
