# Polymorphic Containers

[![Cargo](https://img.shields.io/crates/v/pcc)](https://crates.io/crates/pcc)
![Crates.io](https://img.shields.io/crates/l/pcc)
![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/wvwwvwwv/polymorphic-companion-containers/pcc.yml?branch=main)

## `CompanionStack`

`CompanionStack` is a polymorphic container that allows you to store and manipulate a collection of elements of different types sizes in the stack. The sizes of elements are not necessarily known at compile time, and they can vary dynamically during runtime.

### Examples

Two different `impl Future<Output = ()>` types can be coalesced into a single `dyn Future<Output = ()>` instance without allocating heap memory.

```rust
use pcc::CompanionStack;
use pcc::companion_stack::Handle;
use std::time::SystemTime;

let start = SystemTime::now();

let mut dyn_stack = CompanionStack::new();
let dyn_future: Handle<dyn Future<Output = ()>> = if start == SystemTime::now() {
    dyn_stack.push_one(|| {
        Ok::<_, ()>(async {
            println!("On time");
        })
    })
    .unwrap()
    .into()
} else {
    dyn_stack.push_one(|| {
        Ok::<_, ()>(async {
            println!("Late");
        })
    })
    .unwrap()
    .into()
};
```
