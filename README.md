[![Volute crate](https://img.shields.io/crates/v/volute.svg)](https://crates.io/crates/volute)
[![Volute documentation](https://docs.rs/volute/badge.svg)](https://docs.rs/volute)
[![Build status](https://github.com/Coloquinte/volute/actions/workflows/build.yml/badge.svg)](https://github.com/Coloquinte/volute/actions/workflows/build.yml)

<!-- cargo-rdme start -->

Logic function manipulation using truth tables (or lookup tables, `Luts`) that represent the
value of the function for the 2<sup>n</sup> possible inputs.

The crate implements optimized truth table datastructures, either arbitrary-size truth tables
([`Lut`](https://docs.rs/volute/latest/volute/struct.Lut.html)), or more efficient
fixed-size truth tables ([`Lut2` to `Lut12`](https://docs.rs/volute/latest/volute/struct.StaticLut.html)).
They provide logical operators and utility functions for analysis, canonization and decomposition.
Some support is available for other standard representation, such as Sum-of-Products
([`Sop`](https://docs.rs/volute/latest/volute/sop/struct.Sop.html)).

API and documentation try to follow the same terminology as the C++ library
[Kitty](https://libkitty.readthedocs.io/en/latest).

# Examples

Create a constant-one Lut with five variables and a constant-zero Lut with 4 variables.
```rust
let lut5 = Lut::one(5);
let lut4 = Lut::zero(4);
```

Create a Lut2 representing the first variable. Swap its inputs. Check the result.
```rust
let lut = Lut2::nth_var(0);
assert_eq!(lut.swap(0, 1), Lut2::nth_var(1));
```

Perform the logical and between two Lut4. Check its hexadecimal value.
```rust
let lut = Lut4::nth_var(0) & Lut4::nth_var(2);
assert_eq!(lut.to_string(), "Lut4(a0a0)");
```

Create a Lut6 (6 variables) from its hexadecimal value. Display it.
```rust
let lut = Lut6::from_hex_string("0123456789abcdef").unwrap();
print!("{lut}");
```

Small Luts (3 to 7 variables) can be converted to the integer type of the same size.
```rust
let lut5: u32 = Lut5::random().into();
let lut6: u64 = Lut6::random().into();
let lut7: u128 = Lut7::random().into();
```

Create the parity function on three variables, and check that in can be decomposed as a Xor.
Check its value in binary.
```rust
let lut = Lut::parity(3);
assert_eq!(lut.top_decomposition(0), DecompositionType::Xor);
assert_eq!(format!("{lut:b}"), "Lut3(10010110)");
```

## Sum of products and Exclusive sum of products

Volute provides Sum-of-Products (SOP) and Exclusive Sum-of-Products (ESOP)
representations.

Create Sum of products and perform operations on them.
```rust
let var4 = Sop::nth_var(10, 4);
let var2 = Sop::nth_var(10, 2);
let var_and = var4 & var2;
```

Exact decomposition methods can be used with the features `optim-mip`  (using a MILP solver)
or `optim-sat` (using a SAT solver).

 ```rust
let lut = Lut::threshold(6, 5);
let esop = sop::optim::optimize_esop_mip(&[lut], 1, 2);
```

## Canonical representation

For boolean optimization, Luts have several canonical forms that allow to only store
optimizations for a small subset of Luts.
Methods are available to find the smallest Lut that is identical up to variable
complementation (N), input permutation (P), or both (NPN).

```rust
let lut = Lut4::threshold(3);
let (canonical, flips) = lut.n_canonization();
let (canonical, perm) = lut.p_canonization();
let (canonical, perm, flips) = lut.npn_canonization();
assert_eq!(lut.permute(&perm).flip_n(flips), canonical);
```

<!-- cargo-rdme end -->
