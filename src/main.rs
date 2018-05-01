extern crate btree;

#[macro_use]
extern crate log;
extern crate env_logger;

fn main() {
    env_logger::init();

    info!("Starting...");

    let mut tree = btree::BTree::new(4).unwrap();

    let search_key = btree::node::Key(5);
    print_search(&tree, &search_key);
    tree.insert(search_key, btree::node::Value("a string".to_string()));
    print_search(&tree, &search_key);

    insert_batch(&mut tree);

    tree.print(15);

    info!("Goodbye!");
}

fn print_search(tree: &btree::BTree, key: &btree::node::Key) {
    if tree.contains(key) {
        info!("Tree contains key {:?}.", key);
    } else {
        info!("{:?} not found.", key);
    }
}

fn insert_batch(tree: &mut btree::BTree) {
    for v in 0..100 {
        tree.insert(btree::node::Key(v), btree::node::Value(v.to_string()));
    }
}
