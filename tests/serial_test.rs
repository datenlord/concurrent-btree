use btree::BLinkTree;

#[test]
fn test_serial_insert() {
    let tree = BLinkTree::new(100, (i32::MIN, i32::MIN), (i32::MAX, i32::MAX));
    // insert
    for i in 0..50000 {
        assert_eq!(None, tree.insert(i, i));
    }
    assert_eq!(50002, tree.len());
    for i in (50000..100000).rev() {
        assert_eq!(None, tree.insert(i, i));
    }
    assert_eq!(100002, tree.len());
    // get
    for i in 0..100000 {
        assert_eq!(Some(i), tree.get(&i));
    }
    // insert and get old value
    for i in 0..100000 {
        assert_eq!(Some(i), tree.insert(i, 100000 - i));
    }
    assert_eq!(100002, tree.len());
}

#[test]
fn test_serial_remove() {
    let tree = BLinkTree::new(100, (i32::MIN, i32::MIN), (i32::MAX, i32::MAX));
    // insert
    for i in 0..50000 {
        assert_eq!(None, tree.insert(i, i));
    }
    assert_eq!(50002, tree.len());
    for i in (50000..100000).rev() {
        assert_eq!(None, tree.insert(i, i));
    }
    assert_eq!(100002, tree.len());
    // get
    for i in 0..100000 {
        assert_eq!(Some(i), tree.get(&i));
    }
    // remove
    for i in 0..50000 {
        assert_eq!(Some(i), tree.remove(&i));
    }
    assert_eq!(50002, tree.len());
}
