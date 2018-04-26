pub struct Node {
    t: usize,
    n: usize,
    k: Vec<Key>,
    c: Vec<Option<Node>>,
    //leaf: bool,
    // data: ...,
}

impl Node {
    pub fn new(t: usize) -> Node {
        // Only for creating a new root.
        Node {
            t,
            n: 0,
            k: Vec::new(),
            c: Vec::new(),
            //leaf: false,
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
            match self.c[i] {
                Some(ref n) => n.search(key),
                None        => None, // self is a leaf
            }
        }
    }

}

#[derive(PartialEq, PartialOrd, Debug)]
pub struct Key(pub u32);

