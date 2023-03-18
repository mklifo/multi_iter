[![CI](https://github.com/mklifo/multi_iter/actions/workflows/checks.yml/badge.svg)](https://github.com/mklifo/multi_iter/actions/workflows/checks.yml)
[![](https://docs.rs/multi_iter/badge.svg)](https://docs.rs/multi_iter)
[![crates.io](https://img.shields.io/crates/v/multi_iter.svg)](https://crates.io/crates/multi_iter)

# `multi_iter`

Iterator for acting on multiple elements at a time.

## Features

1. Peek multiple elements with:
   * `peek_n`
   * `peek_rest`
 
2. Advance in windows by using:
   * `next_n`
   * `next_n_if_each`
   * `next_n_if_slice`

3. Collect with zero allocations using:
   * `remaining`
   * `remaining_if`
   * `remaining_if_slice`

## Installation

```toml
[dependencies]
multi_iter = "0.1.4"
```

## No-std support

It is possible to use this crate without the Rust standard library.
Disable the default "std" feature by doing the following:

```toml
[dependencies]
multi_iter = { version = "0.1.4", default-features = false }
```
