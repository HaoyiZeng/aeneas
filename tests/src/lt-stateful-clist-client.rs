//@ [!lean] skip
//@ [lean] aeneas-args=-stateful-lifetimes -eval-drops -loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_imports, unused_variables)]

#[path = ".lt-stateful-client/clist.rs"]
mod clist;
#[path = ".lt-stateful-client/my_std.rs"]
mod my_std;
