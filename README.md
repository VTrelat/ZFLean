# ZFLean

A Lean 4 library for doing core mathematics inside Mathlib's model of ZFC set theory.

On top of `ZFSet`, ZFLean builds a relational calculus for binary relations and partial and
total functions, together with the canonical set-theoretic constructions — Booleans, naturals,
integers, rationals, sums, and options — carrying their usual algebraic structures.

*Transfers* between ZFC objects and Lean's native types carry algebraic structure across the
boundary and restate a set-level goal as the equivalent goal about its Mathlib counterpart,
where Mathlib's lemmas and decision procedures apply. Four small tactics
(`zrel`, `zpfun`, `zfun`, `zdom`) discharge the side conditions these definitions generate:
being a relation, a partial function, or a total function, and belonging to a function's
domain — the set-theoretic form of definedness.

The typed layer is a thin interface of refinement and quotient types over the set-theoretic
universe, adopted for ergonomics: Lean's rewriting, type classes, and algebra tactics thereby
apply to set-level goals.

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain in `lean-toolchain` is
picked up automatically.

```bash
git clone https://github.com/VTrelat/ZFLean.git
cd ZFLean
lake exe cache get
lake build
```

## Using ZFLean in a project

Add to your `lakefile.toml`:

```toml
[[require]]
name = "ZFLean"
git = "https://github.com/VTrelat/ZFLean.git"
rev = "v4.33.0"
```

Then `lake update ZFLean` and import what you need:

```lean
import ZFLean          -- everything
import ZFLean.Integers -- or a single module
```

ZFLean tracks Mathlib closely, so your project's `lean-toolchain` and Mathlib revision must
match the ones ZFLean is built against. Release tags are named after the Lean version they
build with, so set `rev` to the tag matching your project: `rev = "v4.33.0"` for a project on
Lean 4.33.0, and so on. Use `rev = "main"` only to follow the latest development version.

## Contributing

Fork the repository, branch off `main`, and open a pull request. Please make sure
`lake build` succeeds and that new declarations carry a docstring.