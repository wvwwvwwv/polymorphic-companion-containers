# Polymorphic Containers

*The crate is still work-in-progress. The API is subject to change.*

[![Cargo](https://img.shields.io/crates/v/pcc)](https://crates.io/crates/pcc)
![Crates.io](https://img.shields.io/crates/l/pcc)
![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/wvwwvwwv/polymorphic-companion-containers/pcc.yml?branch=main)

## `CompanionStack`

`CompanionStack` is a polymorphic container that allows you to store and manipulate a collection of elements of different types in the stack. The sizes of elements are not necessarily known at compile time, and they can vary dynamically during runtime.

### Examples

Instances of dynamically sized types can be allocated in the stack using `CompanionStack`.
* References to two differently sized/typed `impl Future<Output = ()>` instances can be coerced into a `dyn Future<Output = ()>` reference without allocating heap memory.
* Dynamically sized buffers can be stored and they can be uniformly referenced.

```rust
use pcc::CompanionStack;
use pcc::companion_stack::Handle;
use std::time::SystemTime;

let start = SystemTime::now();

let mut dyn_stack = CompanionStack::default();

// Different `impl Future<Output = ()>` can be used in the code, and
// either of them can be referred to as `dyn Future<Output = ()>` without
// boxing them.
let mut dyn_future: Handle<dyn Future<Output = ()>> = if start == SystemTime::now() {
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

// The `CompanionStack` instance can be retrieved, but the reference's
// lifetime is limited to the scope of the `dyn_future` variable.
let (dyn_future, dyn_stack) = dyn_future.retrieve_stack();

// The buffer is allocated on the stack.
let mut buffer_size = 1024;
let mut dyn_buffer: Handle<[u8]> =
    dyn_stack.push_many(|_| Ok::<_, ()>(0_u8), buffer_size).unwrap();
assert_eq!(dyn_buffer.len(), 1024);

// The buffer is popped from the stack.
drop(dyn_buffer);

// Another buffer of a different size is allocated on the stack.
buffer_size *= 2;
let mut dyn_buffer: Handle<[u8]> =
    dyn_stack.push_many(|_| Ok::<_, ()>(0_u8), buffer_size).unwrap();
assert_eq!(dyn_buffer.len(), 2048);
```
