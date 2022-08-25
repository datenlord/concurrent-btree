use std::{
    collections::{btree_map::Values, VecDeque},
    mem::swap,
    ops::RangeBounds,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock, RwLockReadGuard, RwLockWriteGuard,
    },
};

pub struct BLinkTree<K: Ord + Clone, V: Clone> {
    half_maximum_entries: usize, // each node contains at most 2 * half_maximum_entries values
    root: RwLock<Arc<Node<K, V>>>, // root node of this b-tree
    leaf_nodes_head: Arc<Node<K, V>>, // the head(leftmost) node of leaf nodes
    size: AtomicUsize,           // number of values in this b-tree
}

struct Node<K: Ord + Clone, V: Clone> {
    is_leaf: bool, // leaf node or not (never change after node has been created)
    content: Arc<RwLock<NodeContent<K, V>>>, // contents of this node, protected by read write lock
}

/// These contents are protected by read write lock
struct NodeContent<K: Ord + Clone, V: Clone> {
    high_key: K, // high key, an upper bound on keys stored in the subtree with this node as the root
    link_pointer: Option<Arc<Node<K, V>>>, // pointer to the right twin node at the same level, null if this node is the rightmost
    keys: Vec<K>, // keys, at most 2 * half_maximum_entries keys in one node
    values: Vec<ValueCell<K, V>>, // values or pointers to the son nodes, length == keys.len() in the leaf nodes,length == keys.len() + 1 in the non-leaf nodes
}

enum ValueCell<K: Ord + Clone, V: Clone> {
    Node(Arc<Node<K, V>>), // non-leaf nodes store pointers to the son nodes
    Value(V),              // leadf nodes store values
}

enum SearchResult<K: Ord + Clone, V: Clone> {
    Found(V),
    GoDown(Arc<Node<K, V>>),
    GoRight(Arc<Node<K, V>>),
    Error(),
}

impl<K: Ord + Clone, V: Clone> BLinkTree<K, V> {
    pub fn new(
        half_maximum_entries: usize,
        mut min_pair: (K, V),
        mut max_pair: (K, V),
    ) -> BLinkTree<K, V> {
        // make sure key 0 is less than key 1
        if min_pair.0 > max_pair.0 {
            swap(&mut min_pair, &mut max_pair);
        }
        // construct two leaf nodes
        let leaf_nodes_tail = Arc::new(Node::new(
            true,
            max_pair.0.clone(),
            None,
            vec![max_pair.0.clone()],
            vec![ValueCell::Value(max_pair.1.clone())],
        ));
        let leaf_nodes_head = Arc::new(Node::new(
            true,
            min_pair.0.clone(),
            Some(Arc::clone(&leaf_nodes_tail)),
            vec![min_pair.0.clone()],
            vec![ValueCell::Value(min_pair.1.clone())],
        ));
        // construct tree
        BLinkTree {
            half_maximum_entries,
            root: RwLock::new(Arc::new(Node::new(
                false,
                max_pair.0.clone(),
                None,
                vec![min_pair.0.clone()],
                vec![
                    ValueCell::Node(Arc::clone(&leaf_nodes_head)),
                    ValueCell::Node(Arc::clone(&leaf_nodes_tail)),
                ],
            ))),
            leaf_nodes_head: Arc::clone(&leaf_nodes_head),
            size: AtomicUsize::new(2),
        }
    }

    /// Inserts a key-value pair into the map.
    /// If the map did not have this key present, None is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned. The key is not updated, though; this matters for types that can be == without being identical.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert_eq!(tree.insert(37, "a"), None);
    /// assert_eq!(tree.is_empty(), false);
    ///
    /// tree.insert(37, "b");
    /// assert_eq!(tree.insert(37, "c"), Some("b"));
    /// assert_eq!(tree.get(&37), Some(&"c"));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let mut path_stack = Vec::new();
        // init old node and current node
        let root_rg = self.root.read().unwrap();
        let mut current_node = Arc::clone(&root_rg);
        drop(root_rg);
        let mut old_node;
        // find from non-leaf node to leaf node
        while !current_node.is_leaf {
            old_node = Arc::clone(&current_node);
            let (search_result, old_node_rg) = old_node.scan_node_rg(&key);
            match search_result {
                SearchResult::GoDown(next) => {
                    path_stack.push(Arc::clone(&next));
                    current_node = Arc::clone(&next);
                    if old_node_rg.high_key < key {
                        drop(old_node_rg);
                        let mut old_node_wg = old_node.content.write().unwrap();
                        old_node_wg.high_key = key.clone();
                    }
                }
                SearchResult::GoRight(next) => current_node = Arc::clone(&next),
                _ => panic!("Fail to find the leaf node."),
            }
        }

        let mut k = key;
        let mut v: ValueCell<K, V> = ValueCell::Value(value);
        let mut current_node_content_arc = Arc::clone(&current_node.content);
        let mut current_node_wg = current_node_content_arc.write().unwrap();
        self.move_right();

        loop {
            // replace or insert value
            let insert_pos = current_node_wg.keys.binary_search(&k);
            if let Ok(pos) = insert_pos {
                current_node_wg.values.insert(pos, v);
                if let ValueCell::Value(value) = current_node_wg.values.remove(pos + 1) {
                    return Some(value);
                } else {
                    panic!("");
                }
            } else if let Err(pos) = insert_pos {
                if k > current_node_wg.high_key {
                    current_node_wg.high_key = k.clone();
                }
                current_node_wg.keys.insert(pos, k);
                match v {
                    // child node should at the right position because all keys in the child node are bigger than k
                    ValueCell::Node(_) => current_node_wg.values.insert(pos + 1, v),
                    // value should at the same position
                    ValueCell::Value(_) => current_node_wg.values.insert(pos, v),
                }
            }

            // propagating splits
            if current_node_wg.keys.len() < self.half_maximum_entries * 2 {
                break;
            } else {
                // rearrange
                let new_node_keys = current_node_wg.keys.split_off(self.half_maximum_entries);
                let new_node_values = current_node_wg.values.split_off(self.half_maximum_entries);
                let new_node_high_key = current_node_wg.high_key.clone();
                let new_node_link_pointer;
                match &current_node_wg.link_pointer {
                    Some(next) => new_node_link_pointer = Some(Arc::clone(next)),
                    None => new_node_link_pointer = None,
                }
                if current_node.is_leaf {
                    current_node_wg.high_key = current_node_wg.keys.last().unwrap().clone();
                } else {
                    // non-leaf node's last key will become high key
                    current_node_wg.high_key = current_node_wg.keys.pop().unwrap();
                }
                // link current node and new node
                let new_node = Arc::new(Node::new(
                    current_node.is_leaf,
                    new_node_high_key,
                    new_node_link_pointer,
                    new_node_keys,
                    new_node_values,
                ));
                current_node_wg.link_pointer = Some(Arc::clone(&new_node));
                // all keys in the new node are bigger than new k
                k = current_node_wg.keys.last().unwrap().clone();
                v = ValueCell::Node(Arc::clone(&new_node));
                // find parent node to insert
                if let Some(node) = path_stack.pop() {
                    current_node = node;
                } else {
                    return None;
                }
                current_node_content_arc = Arc::clone(&current_node.content);
                let next_node_wg = current_node_content_arc.write().unwrap();
                // self.move_right();
                drop(current_node_wg);
                current_node_wg = next_node_wg;
            }
        }

        self.size.fetch_add(1, Ordering::Relaxed);
        None
    }

    fn move_right(&self) {
        // loop {
        //     let search_result = current_node.scan_node_wg(&k, &current_node_wg);
        //     match search_result {
        //         SearchResult::GoRight(next) => {
        //             let old_node_wg = current_node_wg;
        //             current_node_wg = next.content.write().unwrap();
        //             drop(old_node_wg);
        //             current_node = Arc::clone(&next);
        //         }
        //         _ => break,
        //     }
        // }
    }

    fn find_leaf_node(&self, key: &K) -> Arc<Node<K, V>> {
        // init old node and current node
        let root_rg = self.root.read().unwrap();
        let mut current_node = Arc::clone(&root_rg);
        drop(root_rg);
        let mut old_node;
        // find from non-leaf node to leaf node
        while !current_node.is_leaf {
            old_node = Arc::clone(&current_node);
            let (search_result, _) = old_node.scan_node_rg(key);
            match search_result {
                SearchResult::GoDown(next) | SearchResult::GoRight(next) => {
                    current_node = Arc::clone(&next)
                }
                _ => panic!("Fail to find the leaf node."),
            }
        }
        return Arc::clone(&current_node);
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    /// The key may be any borrowed form of the map’s key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(1, "a");
    /// assert_eq!(tree.remove(&1), Some("a"));
    /// assert_eq!(tree.remove(&1), None);
    /// ```
    pub fn remove(&self, key: &K) -> Option<V> {
        // find until the leaf node contains the given key
        let mut current_node = self.find_leaf_node(key);
        loop {
            let mut current_node_wg = current_node.content.write().unwrap();
            let search_result = current_node.scan_node_wg(key, &current_node_wg);
            match search_result {
                SearchResult::GoDown(next) | SearchResult::GoRight(next) => {
                    drop(current_node_wg);
                    current_node = Arc::clone(&next);
                }
                _ => {
                    let result = current_node_wg.remove(key);
                    drop(current_node_wg);
                    if let Some(_) = result {
                        self.size.fetch_sub(1, Ordering::Relaxed);
                    }
                    return result;
                }
            }
        }
    }

    /// Returns a reference to the value corresponding to the key.
    /// The key may be any borrowed form of the map’s key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    ///  # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(1, "a");
    /// assert_eq!(tree.get(&1), Some(&"a"));
    /// assert_eq!(tree.get(&2), None);
    /// ```
    pub fn get(&self, key: &K) -> Option<V> {
        // find until the leaf node contains the given key
        let mut current_node = self.find_leaf_node(key);
        loop {
            let (search_result, _) = current_node.scan_node_rg(&key);
            match search_result {
                SearchResult::Found(value) => return Some(value),
                SearchResult::GoDown(next) | SearchResult::GoRight(next) => {
                    current_node = Arc::clone(&next);
                }
                SearchResult::Error() => panic!(""),
            }
        }
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the map. The simplest way is to use the range syntax min..max, thus range(min..max) will yield elements from min (inclusive) to max (exclusive). The range may also be entered as (Bound<T>, Bound<T>), so for example range((Excluded(4), Included(10))) will yield a left-exclusive, right-inclusive range from 4 to 10.
    ///  
    /// # Panics
    ///
    /// Panics if range start > end. Panics if range start == end and both bounds are Excluded.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ops::Bound::Included;
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(3, "a");
    /// tree.insert(5, "b");
    /// tree.insert(8, "c");
    /// let (keys, values) = tree.range((Included(4), Included(8)));
    /// for i in (0..keys.len()) {
    ///     println!("{:#?}: {:#?}", keys.get(i), values.get(i));
    /// }
    /// ```
    pub fn range<T, R>(&self, range: R) -> (Vec<Arc<K>>, Vec<Arc<V>>)
    where
        T: Ord + ?Sized,
        R: RangeBounds<T>,
    {
        (vec![], vec![])
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert_eq!(tree.len(), 2);
    /// tree.insert(1, "a");
    /// assert_eq!(tree.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.size.load(Ordering::Relaxed)
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let mut tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert!(!tree.is_empty());
    /// tree.remove(&i32::MIN);
    /// tree.remove(&i32::MAX);
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size.load(Ordering::Relaxed) == 0
    }
}

impl<K: Ord + Clone, V: Clone> Node<K, V> {
    pub(crate) fn new(
        is_leaf: bool,
        high_key: K,
        link_pointer: Option<Arc<Node<K, V>>>,
        keys: Vec<K>,
        children: Vec<ValueCell<K, V>>,
    ) -> Node<K, V> {
        if is_leaf {
            assert_eq!(keys.len(), children.len());
        } else {
            assert_eq!(keys.len() + 1, children.len());
        }
        return Node {
            is_leaf,
            content: Arc::new(RwLock::new(NodeContent::new(high_key, link_pointer, keys, children))),
        };
    }

    pub(crate) fn scan_node_rg(
        &self,
        key: &K,
    ) -> (SearchResult<K, V>, RwLockReadGuard<NodeContent<K, V>>) {
        let node_rg = self.content.read().unwrap();
        let key_pos = &node_rg.keys.binary_search(key);
        return if self.is_leaf {
            // find until position's key == key
            match key_pos {
                Ok(pos) => match node_rg.values.get(*pos).unwrap() {
                    ValueCell::Node(next) => {
                        (SearchResult::GoDown(Arc::clone(next)), node_rg)
                    }
                    ValueCell::Value(val) => (SearchResult::Found(val.clone()), node_rg),
                },
                Err(pos) => {
                    if *pos == node_rg.keys.len() && key > &node_rg.high_key {
                        match &node_rg.link_pointer {
                            Some(pointer) => {
                                (SearchResult::GoRight(Arc::clone(&pointer)), node_rg)
                            }
                            None => (SearchResult::Error(), node_rg),
                        }
                    } else {
                        (SearchResult::Error(), node_rg)
                    }
                }
            }
        } else {
            // find until position's key <= key
            match key_pos {
                Ok(pos) => match node_rg.values.get(*pos).unwrap() {
                    ValueCell::Node(next) => {
                        (SearchResult::GoDown(Arc::clone(next)), node_rg)
                    }
                    ValueCell::Value(val) => (SearchResult::Found(val.clone()), node_rg),
                },
                Err(pos) => {
                    if *pos == node_rg.keys.len() {
                        if key <= &node_rg.high_key {
                            match node_rg.values.get(*pos + 1).unwrap() {
                                ValueCell::Node(next) => {
                                    (SearchResult::GoDown(Arc::clone(next)), node_rg)
                                }
                                ValueCell::Value(val) => {
                                    (SearchResult::Found(val.clone()), node_rg)
                                }
                            }
                        } else {
                            match &node_rg.link_pointer {
                                Some(pointer) => {
                                    (SearchResult::GoRight(Arc::clone(&pointer)), node_rg)
                                }
                                None => (SearchResult::Error(), node_rg),
                            }
                        }
                    } else {
                        (SearchResult::Error(), node_rg)
                    }
                }
            }
        }
    }

    pub(crate) fn scan_node_wg(
        &self,
        key: &K,
        node_wg: &RwLockWriteGuard<NodeContent<K, V>>,
    ) -> SearchResult<K, V> {
        let key_pos = node_wg.keys.binary_search(key);
        return if self.is_leaf {
            // find until position's key == key
            match key_pos {
                Ok(pos) => match node_wg.values.get(pos).unwrap() {
                    ValueCell::Node(next) => {
                        SearchResult::GoDown(Arc::clone(next))
                    }
                    ValueCell::Value(val) => SearchResult::Found(val.clone()),
                },
                Err(pos) => {
                    if pos == node_wg.keys.len() && key > &node_wg.high_key {
                        match &node_wg.link_pointer {
                            Some(pointer) => {
                                SearchResult::GoRight(Arc::clone(&pointer))
                            }
                            None => SearchResult::Error(),
                        }
                    } else {
                        SearchResult::Error()
                    }
                }
            }
        } else {
            // find until position's key <= key
            match key_pos {
                Ok(pos) => match node_wg.values.get(pos).unwrap() {
                    ValueCell::Node(next) => {
                        SearchResult::GoDown(Arc::clone(next))
                    }
                    ValueCell::Value(val) => SearchResult::Found(val.clone()),
                },
                Err(pos) => {
                    if pos == node_wg.keys.len() {
                        if key <= &node_wg.high_key {
                            match node_wg.values.get(pos + 1).unwrap() {
                                ValueCell::Node(next) => {
                                    SearchResult::GoDown(Arc::clone(next))
                                }
                                ValueCell::Value(val) => {
                                    SearchResult::Found(val.clone())
                                }
                            }
                        } else {
                            match &node_wg.link_pointer {
                                Some(pointer) => {
                                    SearchResult::GoRight(Arc::clone(&pointer))
                                }
                                None => SearchResult::Error(),
                            }
                        }
                    } else {
                        SearchResult::Error()
                    }
                }
            }
        }
    }
}

impl<K: Ord + Clone, V: Clone> NodeContent<K, V> {
    pub(crate) fn new(
        high_key: K,
        link_pointer: Option<Arc<Node<K, V>>>,
        keys: Vec<K>,
        values: Vec<ValueCell<K, V>>,
    ) -> NodeContent<K, V> {
        return NodeContent {
            high_key,
            link_pointer,
            keys,
            values,
        };
    }

    pub(crate) fn remove(&mut self, key: &K) -> Option<V> {
        let key_pos = self.keys.binary_search(key);
        match key_pos {
            Ok(pos) => {
                self.keys.remove(pos);
                let cell = self.values.remove(pos);
                match cell {
                    ValueCell::Value(val) => return Some(val),
                    ValueCell::Node(_) => panic!("Nodes should not exist in leaf node."),
                }
            }
            Err(_) => return None,
        }
    }
}
