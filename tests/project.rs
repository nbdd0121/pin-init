#![allow(dead_code)]

use pin_init::*;
use pin_project::pin_project;

// Ensure that pin_init can be used with pin_project.

#[pin_init]
#[pin_project]
struct InitProject {
    #[pin]
    a: usize,
    #[pin]
    b: usize,
    c: usize,
}

#[pin_project]
#[pin_init]
struct ProjectInit {
    #[pin]
    a: usize,
    #[pin]
    b: usize,
    c: usize,
}
