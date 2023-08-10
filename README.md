# Volute

Implementation of logic functions as truth tables (also called lookup tables, or Luts).

The crate implements truth table datastructures, either arbitrary-size Luts (`Lut`), or more efficient fixed-size Luts (`Lut2` to `Lut12`).
They provide logical operators and utility functions for analysis, canonization and decomposition.

API and documentation try to follow the same terminology as the C++ library [Kitty](https://libkitty.readthedocs.io/en/latest).

## Examples

Create a constant-one Lut with five variables.
Display its hexadecimal value.
```rust
let lut = Lut::one(5);
assert_eq!(lut.to_string(), "Lut5(ffffffff)");
```

Create a Lut4 (four variables) which is the logical and of the 1st and 3rd.
Display its hexadecimal value.
```rust
let lut = Lut4::nth_var(0) & Lut4::nth_var(2);
assert_eq!(lut.to_string(), "Lut4(a0a0)");
```

Create the parity function on three variables, and check that in can be decomposed as a Xor.
Display its value in binary.
```rust
let lut = Lut::parity(3);
assert_eq!(lut.decomposition(0), DecompositionType::Xor);
assert_eq!(format!("{:b}", lut), "Lut3(10010110)");
```
