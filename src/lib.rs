#![deny(
    missing_docs,
    warnings,
    clippy::all,
    clippy::missing_safety_doc,
    clippy::pedantic
)]
#![cfg_attr(
    not(miri),
    doc = include_str!("../README.md")
)]
#![cfg_attr(
    miri,
    doc = include_str!("../CHANGELOG.md")
)]
#![cfg_attr(
    feature = "nightly",
    allow(unstable_features),
    feature(coerce_unsized, unsize)
)]

pub mod companion_stack;
pub use companion_stack::CompanionStack;

mod exit_guard;
