use crate::node::Node;

pub struct Iter<'a, K, V> {
    stack: Vec<NodeBookmark<'a, K, V>>,
}

struct NodeBookmark<'a, K, V> {
    node: &'a Node<K, V>,
    state: State,
}

/// The last location visited on a given node.
enum State {
    Before,
    Child(usize),
    Entry(usize),
    Leaf(usize),
}

impl<K, V> Iter<'_, K, V>
where
    K: Ord,
{
    pub fn new(node: &'_ Node<K, V>) -> Iter<K, V> {
        Iter {
            stack: vec![NodeBookmark {
                node: node,
                state: State::Before, }
            ],
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.next_r()
    }
}
        
impl<'a, K, V> Iter<'a, K, V>
where
    K: Ord,
{
    fn next_r(&mut self) -> Option<<Iter<'a, K, V> as Iterator>::Item> {
        match self.stack.pop() {
            None => None,
            Some(bookmark) => {
                if bookmark.node.is_empty() {
                    None
                } else {
                    match bookmark.state {
                        State::Before => {
                            if bookmark.node.is_leaf() {
                                self.push_return_entry(bookmark, 0, State::Leaf(0))
                            } else {
                                self.descend(bookmark, 0)
                            }
                        },
                        State::Child(index) => {
                            if index < bookmark.node.len() {
                                self.push_return_entry(bookmark, index, State::Entry(index))
                            } else {
                                // Node at this level already popped. Repeat at the parent.
                                self.next_r()
                            }
                        },
                        State::Entry(previous_index) => {
                            let index = previous_index + 1;
                            if index <= bookmark.node.len() { // Note == also Ok for children vec.
                                self.descend(bookmark, index)
                            } else {
                                // Node at this level already popped. Repeat at the parent.
                                self.next_r()
                            }
                        },
                        State::Leaf(previous_index) => {
                            let index = previous_index + 1;
                            if index < bookmark.node.len() {
                                self.push_return_entry(bookmark, index, State::Leaf(index))
                            } else {
                                // Node at this level already popped. Repeat at the parent.
                                self.next_r()
                            }
                        },
                    }
                }
            }
        }
    }

    fn descend(
        &mut self,
        bookmark: NodeBookmark<'a, K, V>,
        index: usize
    ) -> Option<<Iter<'a, K, V> as Iterator>::Item> {
        assert!(index <= bookmark.node.len());
        let child = bookmark.node.child(index).unwrap();
        self.push_with_state(bookmark, State::Child(index));
        self.stack.push(NodeBookmark { node: &child, state: State::Before });
        self.next_r()
    }

    fn push_return_entry(
        &mut self,
        bookmark: NodeBookmark<'a, K, V>,
        index: usize,
        state: State
    ) -> Option<<Iter<'a, K, V> as Iterator>::Item> {
        let entry = bookmark.node.entry(index);
        self.push_with_state(bookmark, state);
        entry
    }

    fn push_with_state(&mut self, mut bookmark: NodeBookmark<'a, K, V>, state: State) {
        bookmark.state = state;
        self.stack.push(bookmark);
    }
}
