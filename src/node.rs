pub struct Node {
    t: usize,
    n: usize,
    k: Vec<Key>,
    c: Vec<Node>,
    leaf: bool,
    // data: ...,
}

impl Node {

    pub fn new(t: usize) -> Node {
        Node {
            t,
            n: 0,
            k: Vec::with_capacity(t),
            c: Vec::with_capacity(t + 1),
            leaf: false,
        }
    }

    pub fn search(&self, key: &Key) -> Option<(&Node, usize)> {
        let mut i = 0;
        while i <= self.n && key >= &self.k[i] {
            i += 1;
        }
        if i <= self.n && key == &self.k[i] {
            Some((&self, i))
        } else {
            if self.leaf {
                None
            } else {
                self.c[i].search(key)
            }
        }
    }

    fn is_full(&self) -> bool {
        self.n >= 2 * self.t - 1
    }

    fn split_child(&mut self, i: usize) {
        assert!(!self.leaf, "Cannot split child of a leaf");
        assert!(!self.is_full(), "Can not split child of full parent.");

        let (new_k, new_c, parent_k) = self.update_split_child(i);
        let new_child = Node {
            t: self.t,
            n: self.t - 1,
            k: new_k,
            c: new_c,
            leaf: self.c[i].leaf,
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

#[derive(PartialEq, PartialOrd, Debug)]
pub struct Key(pub u32);

