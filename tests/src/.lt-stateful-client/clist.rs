// a minimum linked list implementation
use crate::my_std::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

pub type NodeRef<T> = Arc<RwLock<Node<T>>>;
type Link<T> = Option<NodeRef<T>>;

pub struct Platform {
    lock: Arc<RwLock<()>>,
}

impl Platform {
    pub fn new() -> Self {
        Self {
            lock: Arc::new(RwLock::new(())),
        }
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn acquire_shared_lock(&self) -> RwLockReadGuard<'_, ()> {
        self.lock.read()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn acquire_exclusive_lock(&self) -> RwLockWriteGuard<'_, ()> {
        self.lock.write()
    }

    pub fn execute<R, F>(&self, exclusive: bool, f: F) -> Option<R>
    where
        F: FnOnce() -> Option<R>,
    {
        if exclusive {
            let _lock = self.acquire_exclusive_lock();
            f()
        } else {
            let _lock = self.acquire_shared_lock();
            f()
        }
    }
}

pub struct Node<T> {
    pub revoked: bool,
    pub value: T,
    next: Link<T>,
}
pub fn new<T>(value: T, next: Link<T>) -> NodeRef<T> {
    Arc::new(RwLock::new(Node {
        revoked: false,
        value,
        next,
    }))
}

pub fn init<T>(value: T) -> NodeRef<T> {
    new(value, None)
}

pub fn insert<T>(platform: &Platform, node: &NodeRef<T>, value: T) -> Option<NodeRef<T>> {
    platform.execute(false, || {
        let mut ptr = node.write();
        if ptr.revoked {
            return None;
        }
        let new_node = new(value, ptr.next.clone());
        ptr.next = Some(new_node.clone());
        Some(new_node)
    })
}

pub fn revoke<T>(platform: &Platform, node: &NodeRef<T>) -> Option<()> {
    platform.execute(true, || {
        let next = {
            let mut ptr = node.write();
            if ptr.revoked {
                return None;
            }
            ptr.next.take()
        };

        revoke_suffix(next);
        Some(())
    })
}

fn revoke_suffix<T>(current: Link<T>) {
    if let Some(node) = current {
        let next = {
            let mut ptr = node.write();
            ptr.revoked = true;
            ptr.next.take()
        };
        revoke_suffix(next);
    }
}

pub fn get_child<T>(node: &NodeRef<T>) -> Link<T> {
    let ptr = node.read();
    ptr.next.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    fn values_from<T: Clone>(start: &NodeRef<T>) -> Vec<T> {
        let mut values = Vec::new();
        let mut current = Some(start.clone());

        while let Some(node) = current {
            let (value, next) = {
                let node = node.read();
                (node.value.clone(), node.next.clone())
            };
            values.push(value);
            current = next;
        }

        values
    }

    #[test]
    fn init_creates_a_single_node() {
        let node = init("head");
        let node = node.read();

        assert_eq!(node.value, "head");
        assert!(!node.revoked);
        assert!(node.next.is_none());
    }

    #[test]
    fn new_uses_the_supplied_successor() {
        let tail = init(2);
        let head = new(1, Some(tail.clone()));

        assert_eq!(values_from(&head), vec![1, 2]);

        let next = head.read().next.clone().unwrap();
        assert!(Arc::ptr_eq(&next, &tail));
    }

    #[test]
    fn insert_returns_the_inserted_node_and_preserves_the_tail() {
        let platform = Platform::new();
        let tail = init(3);
        let head = new(1, Some(tail.clone()));

        let inserted = insert(&platform, &head, 2).unwrap();

        assert_eq!(values_from(&head), vec![1, 2, 3]);

        let head_next = head.read().next.clone().unwrap();
        assert!(Arc::ptr_eq(&head_next, &inserted));

        let inserted_next = inserted.read().next.clone().unwrap();
        assert!(Arc::ptr_eq(&inserted_next, &tail));
    }

    #[test]
    fn repeated_insertions_at_the_same_node_are_lifo() {
        let platform = Platform::new();
        let head = init(0);
        let first = insert(&platform, &head, 1).unwrap();
        let second = insert(&platform, &head, 2).unwrap();

        assert_eq!(values_from(&head), vec![0, 2, 1]);

        let head_next = head.read().next.clone().unwrap();
        assert!(Arc::ptr_eq(&head_next, &second));

        let second_next = second.read().next.clone().unwrap();
        assert!(Arc::ptr_eq(&second_next, &first));
    }

    #[test]
    fn concurrent_insertions_do_not_lose_nodes() {
        const INSERTIONS: usize = 64;

        let platform = Arc::new(Platform::new());
        let head = init(0);
        let handles: Vec<_> = (1..=INSERTIONS)
            .map(|value| {
                let platform = platform.clone();
                let head = head.clone();
                thread::spawn(move || insert(&platform, &head, value).is_some())
            })
            .collect();

        for handle in handles {
            assert!(handle.join().unwrap());
        }

        let values = values_from(&head);
        assert_eq!(values[0], 0);

        let mut inserted_values = values[1..].to_vec();
        inserted_values.sort_unstable();
        assert_eq!(inserted_values, (1..=INSERTIONS).collect::<Vec<_>>());
    }

    #[test]
    fn revoke_detaches_and_marks_the_strict_suffix() {
        let platform = Platform::new();
        let head = init(0);
        let first = insert(&platform, &head, 1).unwrap();
        let second = insert(&platform, &first, 2).unwrap();
        let third = insert(&platform, &second, 3).unwrap();

        assert_eq!(revoke(&platform, &first), Some(()));
        assert_eq!(values_from(&head), vec![0, 1]);

        assert!(!head.read().revoked);
        assert!(!first.read().revoked);

        let second_state = second.read();
        assert!(second_state.revoked);
        assert!(second_state.next.is_none());
        drop(second_state);

        let third_state = third.read();
        assert!(third_state.revoked);
        assert!(third_state.next.is_none());
        drop(third_state);

        assert_eq!(Arc::strong_count(&second), 1);
        assert_eq!(Arc::strong_count(&third), 1);
        assert!(insert(&platform, &second, 4).is_none());
        assert_eq!(revoke(&platform, &second), None);
    }

    #[test]
    fn revoke_after_a_live_tail_is_a_successful_noop() {
        let platform = Platform::new();
        let tail = init(0);

        assert_eq!(revoke(&platform, &tail), Some(()));
        assert_eq!(values_from(&tail), vec![0]);
        assert!(!tail.read().revoked);
    }
}
