# Polymorphic Containers

*The API is subject to change until the next major release.*

[![Cargo](https://img.shields.io/crates/v/pcc)](https://crates.io/crates/pcc)
![Crates.io](https://img.shields.io/crates/l/pcc)
![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/wvwwvwwv/polymorphic-companion-containers/pcc.yml?branch=main)

## `CompanionStack`

`CompanionStack` is a polymorphic container that allows you to store and manipulate a collection of elements of different types in the stack. The sizes of elements are not necessarily known at compile time, and they can vary dynamically during runtime.

### Examples

Instances of dynamically sized types can be allocated in the stack using `CompanionStack`.
* References to two differently sized/typed `impl Future<Output = ()>` instances can be coerced into a `dyn Future<Output = ()>` reference without allocating heap memory.
* Dynamically sized buffers can be stored and they can be uniformly referenced.
* Nightly-only feature: `+nightly --features nightly` allows `RefMut<T>` to be coerced into `RefMut<U>` if `T` can be coerced into `U`.

```rust
use pcc::CompanionStack;
use pcc::companion_stack::RefMut;
use std::time::SystemTime;

let start = SystemTime::now();

let mut dyn_stack = CompanionStack::default();

// Different `impl Future<Output = ()>` can be used in the code, and
// either of them can be referred to as `dyn Future<Output = ()>` without
// boxing them.
let mut dyn_future: RefMut<dyn Future<Output = ()>> = if start == SystemTime::now() {
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
let mut dyn_buffer: RefMut<[u8]> =
    dyn_stack.push_many(|_| Ok::<_, ()>(0_u8), buffer_size).unwrap();
assert_eq!(dyn_buffer.len(), 1024);

// The buffer is popped from the stack.
drop(dyn_buffer);

// Another buffer of a different size is allocated on the stack.
buffer_size *= 2;
let mut dyn_buffer: RefMut<[u8]> =
    dyn_stack.push_many(|_| Ok::<_, ()>(0_u8), buffer_size).unwrap();
assert_eq!(dyn_buffer.len(), 2048);

#[cfg(not(feature = "nightly"))]
fn nightly_example(_dyn_stack: &mut CompanionStack) {
    // `cargo +nightly build --features nightly` will enable the nightly feature.
}

#[cfg(feature = "nightly")]
fn nightly_example(dyn_stack: &mut CompanionStack) {
    let start = SystemTime::now();

    trait Len {
        fn len(&self) -> usize;
    }

    struct Data1(usize);
    impl Len for Data1 {
        fn len(&self) -> usize {
            1
        }
    }

    struct Data2(Vec<u8>);
    impl Len for Data2 {
        fn len(&self) -> usize {
            self.0.len()
        }
    }

    // `RefMut<Data1>` and `RefMut<Data2>` are coerced into `RefMut<dyn Len>`.
    let dyn_len: RefMut<dyn Len> = if start == SystemTime::now() {
        dyn_stack.push_one(|| Ok::<_, ()>(Data1(11))).unwrap()
    } else {
        dyn_stack
            .push_one(|| Ok::<_, ()>(Data2(vec![1, 2, 3, 4])))
            .unwrap()
    };
    assert!(dyn_len.len() == 1 || dyn_len.len() == 4);
}

nightly_example(dyn_buffer.retrieve_stack().1);
```
