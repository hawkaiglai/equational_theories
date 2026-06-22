/-
  E677Verified.lean
  ------------------
  Machine-checkable core of the prime-degree reduction for E677 ⊨_fin E255.

  Self-contained: core Lean 4 only, NO Mathlib, NO `sorry`, NO axioms beyond Lean's.
  Compile with:   lean E677Verified.lean      (no errors = verified)

  Provenance note: this development is LLM-assisted (Claude), human-directed (S. Chuks-Onah).
  The point of this file is that NOTHING here needs to be trusted on authority — `lean`
  checks every step. Two things are proved:

    1. e255_of_e677_quasigroup : E677 + (left translations injective, right translations
       surjective) ⟹ E255.  This is general (no finiteness), and is the "677 + quasigroup
       ⊢ 255" step that closes the tame branch once the multiplier is shown constant
       (constant multiplier ⟹ right-cancellative ⟹, in the finite case, quasigroup).

    2. Concrete witnesses: the constant-multiplier E677 magmas x◇y = a·y + V(x) over
       𝔽₅ (a=4) and 𝔽₇ (a=3) are checked, by `decide`, to satisfy both E677 and E255.

  What is NOT in this file (it needs Mathlib: groups, primes, polynomials) and is therefore
  only stated in prose, not claimed as formalized:
    (A) prime order ⟹ M simple with primitive left-multiplication group;
    (B) Burnside dichotomy tame/wild at prime order;
    (D) partial A-constancy: tame, deg(A),deg(V) < p/2 ⟹ multiplier constant.
  Those are the next formalization targets, against the equational_theories repo + Mathlib.
-/

universe u

/-- `E677 op` : the law `x = y ◇ (x ◇ ((y ◇ x) ◇ y))` for all `x, y`. -/
def E677 {M : Type u} (op : M → M → M) : Prop :=
  ∀ x y : M, x = op y (op x (op (op y x) y))

/-- `E255 op` : the law `((x ◇ x) ◇ x) ◇ x = x` for all `x`. -/
def E255 {M : Type u} (op : M → M → M) : Prop :=
  ∀ x : M, op (op (op x x) x) x = x

/--
E677, together with the quasigroup facts
  * `hLinj` : every left translation `u ↦ op a u` is injective, and
  * `hRsurj`: every right translation `y ↦ op y a` is surjective,
implies E255.  No finiteness and no Mathlib are used.

Proof outline (all four ◇-facts below are instances of E677 or the hypotheses):
  Fix `x`.  Right-surjectivity gives `y` with `y◇x = x`.
  E677 at `(x,y)` with `y◇x = x` collapses to `x = y◇(x◇(x◇y))`; left-injectivity of
  `op y` then gives `x◇(x◇y) = x`.
  E677 at `(x,x)` gives `x◇(x◇((x◇x)◇x)) = x`.
  The two left-hand sides agree, so peeling `op x` twice (left-injectivity) gives
  `y = (x◇x)◇x`.  Hence `((x◇x)◇x)◇x = y◇x = x`, which is E255 at `x`.
-/
theorem e255_of_e677_quasigroup {M : Type u} (op : M → M → M)
    (h677 : E677 op)
    (hLinj : ∀ a u v : M, op a u = op a v → u = v)
    (hRsurj : ∀ a b : M, ∃ y : M, op y a = b) :
    E255 op := by
  intro x
  obtain ⟨y, hy⟩ := hRsurj x x                      -- hy : op y x = x
  have hbig : x = op y (op x (op x y)) := by         -- E677 at (x,y), using hy
    have h := h677 x y
    rwa [hy] at h
  have hxxy : op x (op x y) = x :=                   -- left-cancel op y
    hLinj y _ _ (hbig.symm.trans hy.symm)
  have hsx : op x (op x (op (op x x) x)) = x :=      -- E677 at (x,x)
    (h677 x x).symm
  have hpeel : op x y = op x (op (op x x) x) :=      -- peel one op x
    hLinj x _ _ (hxxy.trans hsx.symm)
  have hyeq : y = op (op x x) x :=                   -- peel the second op x
    hLinj x _ _ hpeel
  show op (op (op x x) x) x = x
  rw [← hyeq]; exact hy

/-! ### Concrete witnesses (checked by `decide`)

The constant-multiplier magmas `x ◇ y = a·y + V(x)` over `𝔽ₚ`.  We work over `Nat` with
explicit reduction mod `p`, and verify E677/E255 for all arguments `< p`; this is a faithful
check of the `p`-element magma. -/

namespace Model5
/-- `V` for the 𝔽₅ model (a = 4): the fully-idempotent size-5 E677 magma. -/
def V (k : Nat) : Nat := [0, 2, 4, 1, 3].getD k 0
/-- `x ◇ y = 4·y + V(x)  (mod 5)`. -/
def op (x y : Nat) : Nat := (4 * y + V x) % 5

theorem e677 : ∀ x, x < 5 → ∀ y, y < 5 → x = op y (op x (op (op y x) y)) := by decide
theorem e255 : ∀ x, x < 5 → op (op (op x x) x) x = x := by decide
end Model5

namespace Model7
/-- `V` for the 𝔽₇ model (a = 3). -/
def V (k : Nat) : Nat := [0, 4, 1, 5, 2, 6, 3].getD k 0
/-- `x ◇ y = 3·y + V(x)  (mod 7)`. -/
def op (x y : Nat) : Nat := (3 * y + V x) % 7

theorem e677 : ∀ x, x < 7 → ∀ y, y < 7 → x = op y (op x (op (op y x) y)) := by decide
theorem e255 : ∀ x, x < 7 → op (op (op x x) x) x = x := by decide
end Model7

#print axioms e255_of_e677_quasigroup
#print axioms Model5.e677
#print axioms Model5.e255
#print axioms Model7.e677
#print axioms Model7.e255
