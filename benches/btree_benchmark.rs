use btree::BLinkTree;
use criterion::{criterion_group, criterion_main, Criterion};
use parking_lot::RwLock;
use std::collections::BTreeMap;
use std::sync::Arc;
use std::thread;

static THREAD_NUM: i32 = 20;

fn bench_btree_map(c: &mut Criterion) {
    let mut group = c.benchmark_group("BTreeMap");
    let b_tree_map = Arc::new(RwLock::new(BTreeMap::new()));

    // use 10 threads to insert, only bench 1 thread
    let mut handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_tree_map_arc = Arc::clone(&b_tree_map);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map_arc.write().insert(i, i);
            }
        });
        handles.push(handle);
    }
    // bench insert
    group.bench_function("Insert", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map.write().insert(i, i);
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    // use 10 threads to get, only bench 1 thread
    handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_tree_map_arc = Arc::clone(&b_tree_map);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map_arc.read().get(&i).unwrap();
            }
        });
        handles.push(handle);
    }
    // bench get
    group.bench_function("Get", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map.read().get(&i).unwrap();
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    // use 10 threads to remove, only bench 1 thread
    handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_tree_map_arc = Arc::clone(&b_tree_map);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map_arc.write().remove(&i);
            }
        });
        handles.push(handle);
    }
    // bench remove
    group.bench_function("Remove", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_tree_map.write().remove(&i);
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    group.finish();
}

fn bench_blink_tree(c: &mut Criterion) {
    let mut group = c.benchmark_group("BLinkTree");
    let b_link_tree = Arc::new(BLinkTree::new(
        6,
        (i32::MIN, i32::MIN),
        (i32::MAX, i32::MAX),
    ));

    // use 10 threads to insert, only bench 1 thread
    let mut handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_link_tree_arc = Arc::clone(&b_link_tree);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree_arc.insert(i, i);
            }
        });
        handles.push(handle);
    }
    // bench insert
    group.bench_function("Insert", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree.insert(i, i);
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    // use 10 threads to get, only bench 1 thread
    handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_link_tree_arc = Arc::clone(&b_link_tree);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree_arc.get(&i).unwrap();
            }
        });
        handles.push(handle);
    }
    // bench get
    group.bench_function("Get", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree.get(&i).unwrap();
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    // use 10 threads to remove, only bench 1 thread
    handles = vec![];
    for thread_i in 1..THREAD_NUM {
        let b_link_tree_arc = Arc::clone(&b_link_tree);
        let handle = thread::spawn(move || {
            // insert
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree_arc.remove(&i);
            }
        });
        handles.push(handle);
    }
    // bench remove
    group.bench_function("Remove", |b| {
        b.iter(|| {
            let thread_i = THREAD_NUM;
            for i in 1..100001 {
                if i % THREAD_NUM != THREAD_NUM - thread_i {
                    continue;
                }
                b_link_tree.remove(&i);
            }
        })
    });
    // wait all threads done
    for handle in handles {
        handle.join().unwrap();
    }

    group.finish();
}

criterion_group!(benches, bench_btree_map, bench_blink_tree,);
criterion_main!(benches);
