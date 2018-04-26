extern crate btree;

//use btree::node::Key;

fn main() {
    println!("Starting...");

    let tree = btree::BTree::new(2);

    let search_key = btree::node::Key(5);
    match tree.search(&search_key) {
        Some((_, i)) => println!("{:?} found at index {}", search_key, i),
        None         => println!("{:?} not found.", search_key),
    }

    println!("Goodbye!");
}

