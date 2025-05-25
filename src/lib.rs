#![deny(
    missing_docs,
    warnings,
    clippy::all,
    clippy::missing_safety_doc,
    clippy::pedantic
)]
#![doc = include_str!("../README.md")]

pub mod companion_stack;

mod exit_guard;
