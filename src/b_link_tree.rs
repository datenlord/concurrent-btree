use log::warn;
use std::{
    mem::swap,
    ops::RangeBounds,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock, RwLockReadGuard, RwLockWriteGuard,
    },
};

/// An ordered map based on a [B-Link-Tree].
#[derive(Debug)]
pub struct BLinkTree<K: Ord + Clone, V: Clone> {
    // each node contains at most 2 * half_maximum_entries values
    half_maximum_entries: usize,
    // root node of this b-tree
    root: RwLock<Arc<Node<K, V>>>,
    // the head(leftmost) node of leaf nodes
    leaf_nodes_head: Arc<Node<K, V>>,
    // number of values in this b-tree
    size: AtomicUsize,
}

/// Tree node
#[derive(Debug)]
struct Node<K: Ord + Clone, V: Clone> {
    // leaf node or not (never change after node has been created)
    is_leaf: bool,
    // contents of this node, protected by read write lock
    content: Arc<RwLock<NodeContent<K, V>>>,
}

/// Tree node contents, should be protected by read write lock
#[derive(Debug)]
struct NodeContent<K: Ord + Clone, V: Clone> {
    // high key, an upper bound on keys stored in the subtree with this node as the root
    high_key: K,
    // pointer to the right sibling node at the same level, null if this node is the rightmost
    link_pointer: Option<Arc<Node<K, V>>>,
    // keys, at most 2 * half_maximum_entries keys in one node
    keys: Vec<K>,
    // non-leaf nodes: store son nodes, length == keys.len() + 1, son node values[i]' keys are smaller than keys[i]
    // leaf nodes: store values, length == keys.len()
    values: Vec<ValueCell<K, V>>,
}

/// Value cell, stores value or node pointer
#[derive(Debug)]
enum ValueCell<K: Ord + Clone, V: Clone> {
    // non-leaf node stores pointers to the son nodes
    Node(Arc<Node<K, V>>),
    // leaf node stores values
    Value(V),
}

/// Search status
enum SearchResult<K: Ord + Clone, V: Clone> {
    // target key has its corresponding value
    Found(V),
    // target key doesn't have its corresponding value
    NotFound(),
    // traverse to child node
    GoDown(Arc<Node<K, V>>),
    // traverse to right sibling node
    GoRight(Arc<Node<K, V>>),
    // current data structure is broken
    Error(),
}

impl<K: Ord + Clone, V: Clone> BLinkTree<K, V> {
    /// Makes a new `BLinkTree`, with two initial entries in it.
    /// Each node contains at most 2 * half_maximum_entries entries.
    ///
    /// # Panics
    ///
    /// Panics if the first key equals the second key.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert_eq!(2, tree.len());
    /// ```
    pub fn new(
        half_maximum_entries: usize,
        mut kv_pair1: (K, V),
        mut kv_pair2: (K, V),
    ) -> BLinkTree<K, V> {
        // make sure key 0 is less than key 1
        if kv_pair1.0 == kv_pair2.0 {
            panic!("Please give two different initial keys.");
        } else if kv_pair1.0 > kv_pair2.0 {
            swap(&mut kv_pair1, &mut kv_pair2);
        }
        // construct two leaf nodes
        let leaf_nodes_tail = Arc::new(Node::new(
            true,
            kv_pair2.0.clone(),
            None,
            vec![kv_pair2.0.clone()],
            vec![ValueCell::Value(kv_pair2.1)],
        ));
        let leaf_nodes_head = Arc::new(Node::new(
            true,
            kv_pair1.0.clone(),
            Some(Arc::clone(&leaf_nodes_tail)),
            vec![kv_pair1.0.clone()],
            vec![ValueCell::Value(kv_pair1.1)],
        ));
        // construct tree
        BLinkTree {
            half_maximum_entries,
            root: RwLock::new(Arc::new(Node::new(
                false,
                kv_pair2.0.clone(),
                None,
                vec![kv_pair2.0.clone()],
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
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert_eq!(None, tree.insert(1, "a"));
    /// assert_eq!(false, tree.is_empty());
    ///
    /// tree.insert(1, "b");
    /// assert_eq!(Some("b"), tree.insert(1, "c"));
    /// assert_eq!(Some("c"), tree.get(&1));
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
                    path_stack.push(Arc::clone(&old_node));
                    current_node = Arc::clone(&next);
                    if old_node_rg.high_key < key {
                        drop(old_node_rg);
                        let mut old_node_wg = old_node.content.write().unwrap();
                        old_node_wg.high_key = key.clone();
                    }
                }
                SearchResult::GoRight(next) => current_node = Arc::clone(&next),
                _ => {
                    warn!("Fail to find the leaf node. Skip this insert operation");
                    return None;
                }
            }
        }

        let mut k = key;
        let mut v: ValueCell<K, V> = ValueCell::Value(value);
        let mut current_node_content_arc = Arc::clone(&current_node.content);
        let mut current_node_content_ptr = Arc::as_ptr(&current_node_content_arc);
        let mut current_node_wg = unsafe { (*current_node_content_ptr).write().unwrap() };
        // move right
        loop {
            let search_result = current_node.scan_node_wg(&k, &current_node_wg);
            if let SearchResult::GoRight(next) = search_result {
                // first get next node's guard, then drop current node's guard
                current_node = next;
                current_node_content_arc = Arc::clone(&current_node.content);
                current_node_content_ptr = Arc::as_ptr(&current_node_content_arc);
                let old_node_wg = current_node_wg;
                // SAFETY: current_node_wg borrows current_node_content_arc, drop old_node_wg before previous current_node_content_arc is dropped
                current_node_wg = unsafe { (*current_node_content_ptr).write().unwrap() };
                drop(old_node_wg);
            } else {
                break;
            }
        }

        loop {
            // replace or insert value
            let insert_pos = current_node_wg.keys.binary_search(&k);
            if let Ok(pos) = insert_pos {
                current_node_wg.values.insert(pos, v);
                return if let ValueCell::Value(value) = current_node_wg.values.remove(pos + 1) {
                    Some(value)
                } else {
                    warn!("Add duplicate key in the non-leaf nodes. Stop backtracking caused by insert operation.");
                    None
                };
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
                drop(current_node_wg);
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
                let old_node_wg;
                if let Some(node) = path_stack.pop() {
                    current_node = node;
                    // first get next node's guard, then drop current node's guard
                    current_node_content_arc = Arc::clone(&current_node.content);
                    current_node_content_ptr = Arc::as_ptr(&current_node_content_arc);
                    old_node_wg = current_node_wg;
                    current_node_wg = unsafe { (*current_node_content_ptr).write().unwrap() };
                } else {
                    break;
                }
                // move right
                loop {
                    let search_result = current_node.scan_node_wg(&k, &current_node_wg);
                    if let SearchResult::GoRight(next) = search_result {
                        // first get next node's guard, then drop current node's guard
                        current_node = next;
                        current_node_content_arc = Arc::clone(&current_node.content);
                        current_node_content_ptr = Arc::as_ptr(&current_node_content_arc);
                        let old_node_wg = current_node_wg;
                        // SAFETY: current_node_wg borrows current_node_content_arc, drop old_node_wg before previous current_node_content_arc is dropped
                        current_node_wg = unsafe { (*current_node_content_ptr).write().unwrap() };
                        drop(old_node_wg);
                    } else {
                        break;
                    }
                }
                drop(old_node_wg);
            }
        }

        self.size.fetch_add(1, Ordering::Release);
        None
    }

    fn find_leaf_node(&self, key: &K) -> Option<Arc<Node<K, V>>> {
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
                _ => {
                    warn!("Fail to find the leaf node. Skip this operation");
                    return None;
                }
            }
        }
        return Some(current_node);
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    /// The key may be any borrowed form of the map’s key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(1, "a");
    /// assert_eq!(Some("a"), tree.remove(&1));
    /// assert_eq!(None, tree.remove(&1));
    /// ```
    pub fn remove(&self, key: &K) -> Option<V> {
        let mut current_node;
        if let Some(node) = self.find_leaf_node(key) {
            current_node = node;
        } else {
            return None;
        }
        // find until the leaf node contains the given key
        loop {
            // TODO: use read guard to search, then upgrade to write guard to delete
            let mut current_node_wg = current_node.content.write().unwrap();
            let search_result = current_node.scan_node_wg(key, &current_node_wg);
            match search_result {
                SearchResult::Found(_) => {
                    let result = current_node_wg.remove(key);
                    drop(current_node_wg);
                    return if let Some(ValueCell::Value(val)) = result {
                        self.size.fetch_sub(1, Ordering::Release);
                        Some(val)
                    } else if let Some(ValueCell::Node(_)) = result {
                        warn!("Delete node pointer.");
                        None
                    } else {
                        None
                    };
                }
                SearchResult::GoDown(next) | SearchResult::GoRight(next) => {
                    drop(current_node_wg);
                    current_node = Arc::clone(&next);
                }
                SearchResult::NotFound() => break,
                SearchResult::Error() => {
                    warn!("Unrecoverable error occurs.");
                    break;
                }
            }
        }
        None
    }

    /// Returns a reference to the value corresponding to the key.
    /// The key may be any borrowed form of the map’s key type, but the ordering on the borrowed form must match the ordering on the key type.
    ///
    ///  # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(1, "a");
    /// assert_eq!(Some("a"), tree.get(&1));
    /// assert_eq!(None, tree.get(&2));
    /// ```
    pub fn get(&self, key: &K) -> Option<V> {
        let mut current_node;
        if let Some(node) = self.find_leaf_node(key) {
            current_node = node;
        } else {
            return None;
        }
        // find until the leaf node contains the given key
        loop {
            let (search_result, _) = current_node.scan_node_rg(&key);
            match search_result {
                SearchResult::Found(value) => return Some(value),
                SearchResult::GoDown(next) | SearchResult::GoRight(next) => {
                    current_node = Arc::clone(&next);
                }
                SearchResult::NotFound() => break,
                SearchResult::Error() => {
                    warn!("Unrecoverable error occurs.");
                    break;
                }
            }
        }
        None
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
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// tree.insert(3, "a");
    /// tree.insert(5, "b");
    /// tree.insert(8, "c");
    /// let (keys, values) = tree.range((Included(4), Included(8)));
    /// for i in 0..keys.len() {
    ///     println!("{:#?}: {:#?}", keys.get(i), values.get(i));
    /// }
    /// ```
    pub fn range<T, R>(&self, range: R) -> (Vec<Arc<K>>, Vec<V>)
    where
        T: Ord + ?Sized,
        R: RangeBounds<T>,
    {
        // TODO: complete range search
        range.start_bound();
        let _leaf_nodes_head = Arc::clone(&self.leaf_nodes_head);
        (vec![], vec![])
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert_eq!(2, tree.len());
    /// tree.insert(1, "a");
    /// assert_eq!(3, tree.len());
    /// ```
    pub fn len(&self) -> usize {
        self.size.load(Ordering::Acquire)
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use btree::BLinkTree;
    ///
    /// let tree = BLinkTree::new(5, (i32::MIN, "dummy_value"), (i32::MAX, "dummy_value"));
    /// assert!(!tree.is_empty());
    /// tree.remove(&i32::MIN);
    /// tree.remove(&i32::MAX);
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size.load(Ordering::Acquire) == 0
    }
}

impl<K: Ord + Clone, V: Clone> Node<K, V> {
    /// Makes a new tree node.
    /// Each node contains at most 2 * half_maximum_entries entries.
    ///
    /// # Panics
    ///
    /// Panics if keys length and values length violate the constraints.
    /// non-leaf nodes: values.len() == keys.len() + 1
    /// leaf nodes: values.len() == keys.len()
    pub(crate) fn new(
        is_leaf: bool,
        high_key: K,
        link_pointer: Option<Arc<Node<K, V>>>,
        keys: Vec<K>,
        values: Vec<ValueCell<K, V>>,
    ) -> Node<K, V> {
        if is_leaf && values.len() != keys.len() {
            panic!("for leaf nodes, values.len() should equal keys.len().");
        } else if !is_leaf && values.len() != keys.len() + 1 {
            panic!("for non-leaf nodes, values.len() should equal keys.len() + 1.");
        }
        return Node {
            is_leaf,
            content: Arc::new(RwLock::new(NodeContent::new(
                high_key,
                link_pointer,
                keys,
                values,
            ))),
        };
    }

    /// Returns search result and this nodes' read guard.
    pub(crate) fn scan_node_rg(
        &self,
        key: &K,
    ) -> (SearchResult<K, V>, RwLockReadGuard<NodeContent<K, V>>) {
        let node_rg = self.content.read().unwrap();
        let key_pos = &node_rg.keys.binary_search(key);
        return if self.is_leaf {
            // find until position's key == key
            match key_pos {
                Ok(pos) => {
                    // value cells in leaf nodes should be value type
                    if let ValueCell::Value(val) = node_rg.values.get(*pos).unwrap() {
                        (SearchResult::Found(val.clone()), node_rg)
                    } else {
                        (SearchResult::Error(), node_rg)
                    }
                }
                Err(pos) => {
                    // check right sibling node
                    if *pos == node_rg.keys.len() && key > &node_rg.high_key {
                        if let Some(pointer) = &node_rg.link_pointer {
                            (SearchResult::GoRight(Arc::clone(&pointer)), node_rg)
                        } else {
                            (SearchResult::NotFound(), node_rg)
                        }
                    } else {
                        (SearchResult::NotFound(), node_rg)
                    }
                }
            }
        } else {
            // find until position's key <= key
            match key_pos {
                Ok(pos) => {
                    // value cells in leaf nodes should be node type
                    if let ValueCell::Node(next) = node_rg.values.get(*pos).unwrap() {
                        (SearchResult::GoDown(Arc::clone(next)), node_rg)
                    } else {
                        (SearchResult::Error(), node_rg)
                    }
                }
                Err(pos) => {
                    if *pos < node_rg.keys.len()
                        || (*pos == node_rg.keys.len() && key <= &node_rg.high_key)
                    {
                        // value cells in leaf nodes should be node type
                        if let ValueCell::Node(next) = node_rg.values.get(*pos).unwrap() {
                            (SearchResult::GoDown(Arc::clone(&next)), node_rg)
                        } else {
                            (SearchResult::Error(), node_rg)
                        }
                    } else if key > &node_rg.high_key {
                        if let Some(pointer) = &node_rg.link_pointer {
                            (SearchResult::GoRight(Arc::clone(&pointer)), node_rg)
                        } else {
                            (SearchResult::Error(), node_rg)
                        }
                    } else {
                        (SearchResult::Error(), node_rg)
                    }
                }
            }
        };
    }

    /// Returns search result.
    pub(crate) fn scan_node_wg(
        &self,
        key: &K,
        node_wg: &RwLockWriteGuard<NodeContent<K, V>>,
    ) -> SearchResult<K, V> {
        let key_pos = node_wg.keys.binary_search(key);
        return if self.is_leaf {
            // find until position's key == key
            match key_pos {
                Ok(pos) => {
                    // value cells in leaf nodes should be value type
                    if let ValueCell::Value(val) = node_wg.values.get(pos).unwrap() {
                        SearchResult::Found(val.clone())
                    } else {
                        SearchResult::Error()
                    }
                }
                Err(pos) => {
                    if pos == node_wg.keys.len() && key > &node_wg.high_key {
                        if let Some(pointer) = &node_wg.link_pointer {
                            SearchResult::GoRight(Arc::clone(&pointer))
                        } else {
                            SearchResult::NotFound()
                        }
                    } else {
                        SearchResult::NotFound()
                    }
                }
            }
        } else {
            // find until position's key <= key
            match key_pos {
                Ok(pos) => {
                    // value cells in leaf nodes should be node type
                    if let ValueCell::Node(next) = node_wg.values.get(pos).unwrap() {
                        SearchResult::GoDown(Arc::clone(next))
                    } else {
                        SearchResult::Error()
                    }
                }
                Err(pos) => {
                    if pos < node_wg.keys.len()
                        || (pos == node_wg.keys.len() && key <= &node_wg.high_key)
                    {
                        // value cells in leaf nodes should be node type
                        if let ValueCell::Node(next) = node_wg.values.get(pos).unwrap() {
                            SearchResult::GoDown(Arc::clone(&next))
                        } else {
                            SearchResult::Error()
                        }
                    } else if key > &node_wg.high_key {
                        if let Some(pointer) = &node_wg.link_pointer {
                            SearchResult::GoRight(Arc::clone(&pointer))
                        } else {
                            SearchResult::Error()
                        }
                    } else {
                        SearchResult::Error()
                    }
                }
            }
        };
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

    pub(crate) fn remove(&mut self, key: &K) -> Option<ValueCell<K, V>> {
        let key_pos = self.keys.binary_search(key);
        return match key_pos {
            Ok(pos) => {
                self.keys.remove(pos);
                Some(self.values.remove(pos))
            }
            Err(_) => None,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serial_insert() {
        let tree = BLinkTree::new(60, (i32::MIN, i32::MIN), (i32::MAX, i32::MAX));
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
        let tree = BLinkTree::new(60, (i32::MIN, i32::MIN), (i32::MAX, i32::MAX));
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
}
