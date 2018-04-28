extern crate btree;

#[macro_use]
extern crate log;
extern crate env_logger;

//use btree::node::Key;

fn main() {
    env_logger::init();

    info!("Starting...");

    let mut tree = btree::BTree::new(2);

    let search_key = btree::node::Key(5);
    print_search(&tree, &search_key);
    match tree.insert(search_key) {
        Ok(_) => info!("Insert successful!"),
        Err(msg) => info!("Insert failed {}", msg),
    }
    print_search(&tree, &search_key);

    insert_batch(&mut tree);

    info!("Goodbye!");
}

fn print_search(tree: &btree::BTree, key: &btree::node::Key) {
    match tree.search(key) {
        Some((n, i)) => info!("{:?} found at index {} on node {:?}", key, i, n),
        None         => info!("{:?} not found.", key),
    }
}

fn insert_batch(tree: &mut btree::BTree) {
    for v in 0..100 {
        // TODO: Only handle the error.
        match tree.insert(btree::node::Key(v)) {
            Ok(_) => info!("Insert successful!"),
            Err(msg) => info!("Insert failed {}", msg),
        }
    }
}
