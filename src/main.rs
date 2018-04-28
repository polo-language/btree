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

    info!("Goodbye!");
}

fn print_search(tree: &btree::BTree, key: &btree::node::Key) {
    match tree.search(key) {
        Some((n, i)) => info!("{:?} found at index {} on node {:?}", key, i, n),
        None         => info!("{:?} not found.", key),
    }
}
