![crates.io](https://img.shields.io/crates/v/volute.svg)
![Build](https://github.com/Coloquinte/volute/actions/workflows/build.yml/badge.svg)

<!-- cargo-rdme start -->

Logic function manipulation using truth tables (LUTs)

The crate implements truth table datastructures, either arbitrary-size Luts
([`Lut`](https://docs.rs/volute/latest/volute/struct.Lut.html)), or more efficient
fixed-size Luts ([`Lut2` to `Lut12`](https://docs.rs/volute/latest/volute/struct.StaticLut.html)).
They provide logical operators and utility functions for analysis, canonization and decomposition.
Some support is available for other standard representation, such as SoPs
([`Sop`](https://docs.rs/volute/latest/volute/struct.Sop.html)).

API and documentation try to follow the same terminology as the C++ library [Kitty](https://libkitty.readthedocs.io/en/latest).

# Examples

Create a constant-one Lut with five variables.
Check its hexadecimal value.
```rust
let lut = Lut::one(5);
assert_eq!(lut.to_string(), "Lut5(ffffffff)");
```

Create a Lut4 (four variables) which is the logical and of the 1st and 3rd.
Check its hexadecimal value.
```rust
let lut = Lut4::nth_var(0) & Lut4::nth_var(2);
assert_eq!(lut.to_string(), "Lut4(a0a0)");
```

Create the parity function on three variables, and check that in can be decomposed as a Xor.
Check its value in binary.
```rust
let lut = Lut::parity(3);
assert_eq!(lut.top_decomposition(0), DecompositionType::Xor);
assert_eq!(format!("{:b}", lut), "Lut3(10010110)");
```

<!-- cargo-rdme end -->
