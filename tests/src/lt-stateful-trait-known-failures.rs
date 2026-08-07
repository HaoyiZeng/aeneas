//@ [!lean] skip
//@ [lean] aeneas-args=-stateful-lifetimes
#![feature(register_tool)]
#![register_tool(verify)]

//! Generic stateful trait dispatch is deliberately omitted with a diagnostic.
//! Concrete impl methods remain translatable and the generated module must
//! still elaborate.

pub trait StatefulUpdate {
    #[verify::stateful_lifetimes('a)]
    fn update<'a>(&'a mut self, value: i32);
}

pub struct StatefulCounter {
    value: i32,
}

impl StatefulUpdate for StatefulCounter {
    fn update<'a>(&'a mut self, value: i32) {
        self.value = value;
    }
}
