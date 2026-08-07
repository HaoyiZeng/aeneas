use std::marker::PhantomData;
use std::ops::Index;
use std::ops::{Deref, DerefMut};

pub struct Vec<T> {
    marker: PhantomData<T>,
}

impl<T> Vec<T> {
    #[verify::opaque]
    pub fn new() -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn len(&self) -> usize {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn push(&mut self, _value: T) {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn remove(&mut self, _index: usize) -> T {
        unimplemented!()
    }
}

impl<T> Index<usize> for Vec<T> {
    type Output = T;

    #[verify::opaque]
    fn index(&self, _index: usize) -> &T {
        unimplemented!()
    }
}

pub struct BTreeMap<K, V> {
    marker: PhantomData<(K, V)>,
}

impl<K, V> BTreeMap<K, V> {
    #[verify::opaque]
    pub fn new() -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn get(&self, _key: &K) -> Option<&V> {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn contains_key(&self, _key: &K) -> bool {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn insert(&mut self, _key: K, _value: V) -> Option<V> {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn remove(&mut self, _key: &K) -> Option<V> {
        unimplemented!()
    }
}

pub struct Arc<T> {
    marker: PhantomData<T>,
}

pub struct Weak<T> {
    marker: PhantomData<T>,
}

impl<T> Arc<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn downgrade(&self) -> Weak<T> {
        unimplemented!()
    }
}

impl<T> Clone for Arc<T> {
    #[verify::opaque]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

impl<T> Deref for Arc<T> {
    type Target = T;

    #[verify::opaque]
    fn deref(&self) -> &T {
        unimplemented!()
    }
}

impl<T> Weak<T> {
    #[verify::opaque]
    pub fn new() -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn upgrade(&self) -> Option<Arc<T>> {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn strong_count(&self) -> usize {
        unimplemented!()
    }
}

impl<T> Clone for Weak<T> {
    #[verify::opaque]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

pub struct RwLock<T> {
    marker: PhantomData<T>,
}

#[verify::opaque]
pub struct RwLockReadGuard<'a, T> {
    marker: PhantomData<&'a T>,
}

#[verify::opaque]
pub struct RwLockWriteGuard<'a, T> {
    marker: PhantomData<&'a mut T>,
}

impl<T> RwLock<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn write(&self) -> RwLockWriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<T> Deref for RwLockReadGuard<'_, T> {
    type Target = T;

    #[verify::opaque]
    fn deref(&self) -> &T {
        unimplemented!()
    }
}

impl<T> Drop for RwLockReadGuard<'_, T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

impl<T> Deref for RwLockWriteGuard<'_, T> {
    type Target = T;

    #[verify::opaque]
    fn deref(&self) -> &T {
        unimplemented!()
    }
}

impl<T> DerefMut for RwLockWriteGuard<'_, T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    fn deref_mut(&mut self) -> &mut T {
        unimplemented!()
    }
}

impl<T> Drop for RwLockWriteGuard<'_, T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}
