use btree::BLinkTree;
use std::sync::Arc;
use std::thread;

#[test]
fn test_concurrent_insert() {
    let tree = Arc::new(BLinkTree::new(
        50,
        (i32::MIN, i32::MIN),
        (i32::MAX, i32::MAX),
    ));
    // create 10 threads
    let mut handles = vec![];
    for i in 1..11 {
        let thread_i = i;
        let tree_arc = Arc::clone(&tree);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(None, tree_arc.insert(i, i), "insert {} fails.", i);
            }
            // get
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(Some(i), tree_arc.get(&i), "get {} fails.", i);
            }
            // insert and get old value
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(
                    Some(i),
                    tree_arc.insert(i, 100001 - i),
                    "insert {} fails.",
                    i
                );
            }
        });
        handles.push(handle);
    }
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }
    assert_eq!(100002, tree.len());
}

#[test]
fn test_concurrent_remove() {
    let tree = Arc::new(BLinkTree::new(
        50,
        (i32::MIN, i32::MIN),
        (i32::MAX, i32::MAX),
    ));
    // create 10 threads
    let mut handles = vec![];
    for i in 1..11 {
        let thread_i = i;
        let tree_arc = Arc::clone(&tree);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(None, tree_arc.insert(i, i), "insert {} fails.", i);
            }
            // get
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(Some(i), tree_arc.get(&i), "get {} fails.", i);
            }
        });
        handles.push(handle);
    }
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }
    assert_eq!(100002, tree.len());

    handles = vec![];
    for i in 1..11 {
        let thread_i = i;
        let tree_arc = Arc::clone(&tree);
        let handle = thread::spawn(move || {
            // delete
            for i in 1..100001 {
                if i % 10 != 10 - thread_i {
                    continue;
                }
                assert_eq!(Some(i), tree_arc.remove(&i), "remove {} fails.", i);
            }
        });
        handles.push(handle);
    }
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }
    assert_eq!(2, tree.len());
}
