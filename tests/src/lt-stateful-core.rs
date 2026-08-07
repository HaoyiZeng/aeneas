//@ [!lean] skip
//@ [lean] aeneas-args=-stateful-lifetimes -eval-drops
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    marker: PhantomData<T>,
}

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    marker: PhantomData<&'a T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<'a, T> ReadGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn refresh(&mut self) {
        unimplemented!()
    }
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }
}

pub fn read_copy(lock: &Lock<i32>) -> i32 {
    let guard = lock.read();
    *guard.get()
}

pub fn write_set(lock: &Lock<i32>) {
    let mut guard = lock.write();
    *guard.get_mut() = 42;
}

pub struct Cell {
    value: i32,
}

impl Cell {
    pub fn set(&mut self, value: i32) {
        self.value = value;
    }
}

pub fn write_method(lock: &Lock<Cell>) {
    let mut guard = lock.write();
    guard.get_mut().set(42);
}

pub fn read_then_write(read_lock: &Lock<i32>, write_lock: &Lock<i32>) {
    let read_guard = read_lock.read();
    let _value = *read_guard.get();
    drop(read_guard);
    let _write_guard = write_lock.write();
}

pub fn scoped_read_then_write(read_lock: &Lock<i32>, write_lock: &Lock<i32>) {
    {
        let read_guard = read_lock.read();
        let _value = *read_guard.get();
    }
    let _write_guard = write_lock.write();
}

pub fn write_two(first: &Lock<i32>, second: &Lock<i32>) {
    let mut first_guard = first.write();
    let mut second_guard = second.write();
    *first_guard.get_mut() = 1;
    *second_guard.get_mut() = 2;
}

pub fn update_external_and_lock(value: &mut i32, lock: &Lock<i32>) {
    let mut guard = lock.write();
    *guard.get_mut() = 7;
    *value = 99;
}

pub fn call_update_external(lock: &Lock<i32>) -> i32 {
    let mut value = 0;
    update_external_and_lock(&mut value, lock);
    value
}

pub fn choose<'a>(value: &'a mut i32, lock: &Lock<i32>) -> &'a mut i32 {
    let mut guard = lock.write();
    *guard.get_mut() = 1;
    value
}

pub fn call_choose(lock: &Lock<i32>) -> i32 {
    let mut value = 0;
    {
        let selected = choose(&mut value, lock);
        *selected = 5;
    }
    value
}

pub fn write_branch(lock: &Lock<i32>, choose_first: bool) {
    let mut guard = lock.write();
    if choose_first {
        *guard.get_mut() = 1;
    } else {
        *guard.get_mut() = 2;
    }
    let _value = *guard.get();
}

pub fn refresh_one(lock: &Lock<i32>) {
    let mut guard = lock.read();
    guard.refresh();
    let _value = *guard.get();
}

pub fn refresh_cross(first: &Lock<i32>, second: &Lock<i32>) {
    let mut first_guard = first.read();
    {
        let second_guard = second.read();
        first_guard.refresh();
        let _second_value = *second_guard.get();
    }
    let _first_value = *first_guard.get();
}

pub fn refresh_branch(lock: &Lock<i32>, refresh: bool) -> i32 {
    let mut guard = lock.read();
    if refresh {
        guard.refresh();
    }
    *guard.get()
}

pub fn refresh_first_loop(first: &Lock<i32>, second: &Lock<i32>, count: u32) -> i32 {
    let mut first_guard = first.read();
    let second_guard = second.read();
    let mut index = 0;
    while index < count {
        first_guard.refresh();
        index += 1;
    }
    *first_guard.get() + *second_guard.get()
}

#[verify::stateful_lifetimes]
pub fn observe<'a>(lock: &'a Lock<i32>) -> i32 {
    let guard = lock.read();
    *guard.get()
}
