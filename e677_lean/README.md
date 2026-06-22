# Machine-checked core of the E677 prime-degree reduction

`E677Verified.lean` is a self-contained Lean 4 file (core Lean only, no Mathlib, no `sorry`)
that proves the parts of the prime-degree reduction that do not need group/field theory.

## What is proved

- `E677`, `E255` are the two laws as predicates on `op : M → M → M`:
  - E677: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`
  - E255: `((x ◇ x) ◇ x) ◇ x = x`
- `e255_of_e677_quasigroup` : if `op` satisfies E677, every left translation `u ↦ op a u`
  is injective, and every right translation `y ↦ op y a` is surjective, then `op` satisfies
  E255. (These two hypotheses hold for any quasigroup; left-injectivity already follows from
  E677, and right-surjectivity follows from right-cancellativity in the finite case. This is
  the "E677 + quasigroup ⊢ E255" step.)
- `Model5.{e677,e255}`, `Model7.{e677,e255}` : the constant-multiplier magmas
  `x ◇ y = a·y + V(x)` over 𝔽₅ (a=4) and 𝔽₇ (a=3) satisfy both laws, checked by `decide`.

## How to verify

```
lean E677Verified.lean
```

No imports, no Lake project needed. Success = exit 0 and the only output is the
`#print axioms` lines:

```
'e255_of_e677_quasigroup' does not depend on any axioms
'Model5.e677' depends on axioms: [propext]
'Model5.e255' depends on axioms: [propext]
'Model7.e677' depends on axioms: [propext]
'Model7.e255' depends on axioms: [propext]
```

The main theorem uses no axioms at all; the `decide` checks use only `propext`, which is part
of Lean's trusted core. A local toolchain is in `lean-4.31.0-linux/` (run
`./lean-4.31.0-linux/bin/lean E677Verified.lean`), or install any Lean 4.31 via elan.

## What is NOT formalized here

These need Mathlib (groups, primes, polynomials) and the equational_theories repo, so they
are not in this file and are not claimed as machine-checked:

- prime order ⟹ the magma is simple with primitive left-multiplication group;
- the Burnside tame/wild dichotomy at prime order;
- partial A-constancy: tame + deg(A), deg(V) < p/2 ⟹ the multiplier is constant.

They are the next formalization targets.
