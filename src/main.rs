extern crate btree;

//use btree::node::Key;

fn main() {
    println!("Starting...");

    let mut tree = btree::BTree::new(2);

    let search_key = btree::node::Key(5);
    print_search(&tree, &search_key);
    match tree.insert(search_key) {
        Ok(_) => println!("Insert successful!"),
        Err(msg) => println!("Insert failed {}", msg),
    }
    print_search(&tree, &search_key);

    println!("Goodbye!");
}

fn print_search(tree: &btree::BTree, key: &btree::node::Key) {
    match tree.search(key) {
        Some((_, i)) => println!("{:?} found at index {}", key, i),
        None         => println!("{:?} not found.", key),
    }
}
