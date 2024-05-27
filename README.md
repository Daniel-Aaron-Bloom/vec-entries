# vec-entries
[![Crates.io](https://img.shields.io/crates/v/vec-entries.svg)](https://crates.io/crates/vec-entries)
[![Workflow Status](https://github.com/Daniel-Aaron-Bloom/vec-entries/workflows/Rust/badge.svg)](https://github.com/Daniel-Aaron-Bloom/vec-entries/actions?query=workflow%3A%22Rust%22)

Entry API for iterating over and removing elements from a `Vec`.

### Description

Sometimes you want to do efficently remove and modify elements of a `Vec` in a slightly more
complex way than [`Vec::dedup_by`], [`Vec::retain`], or [`Vec::drain`] enable. This crate aims
to target a similar, but more expansive functionality.

### Usage

Just import the extension trait and call the new method. The [`EntriesExt::entries`] enables
iterating across elements, mutating, removing, and re-inserting as needed. Like
[`Vec::dedup_by`] this is done by passing in a function which take an [`Entries`] object and
returns anything.

```rust
use vec_entries::EntriesExt;

let mut v = vec![1, 2, 3];
let c = v.entries(.., |e| {
    let a = e.remove().unwrap();      // Remove the `1`
    let b = e.remove_back().unwrap(); // Remove the `3`
    e.try_insert_outside(0);          // Insert a `0` where we removed the `1`
    a + b
});
assert_eq!(c, 4);
assert_eq!(v, [0, 2]);
```

## License

Licensed under 
* MIT license ([LICENSE](LICENSE) or https://opensource.org/licenses/MIT)

[`EntriesExt::entries`]: https://docs.rs/vec-entries/latest/vec_entries/trait.EntriesExt.html#tymethod.entries
[`Entries`]: https://docs.rs/vec-entries/latest/vec_entries/struct.Entries.html
[`Vec::dedup_by`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by
[`Vec::retain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain
[`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
