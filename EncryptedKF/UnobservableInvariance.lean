module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Unobservable Invariance (paper Lemma 1)

Formalization of Lemma 1 of *"Encrypted Kalman Filtering with Bounded-Error
Guarantees"* (Lois & Cole).

**Statement.** If `u` is an eigenvector of `A` at eigenvalue `1` (`A u = u`) and
`u` is unobservable (`C u = 0`), then the closed-loop map `(I - K C) A` fixes `u`
for *every* gain matrix `K`:
`(I - K C) A u = u`.

This is the gain-independence property the paper relies on: no Kalman gain can
move an unobservable, marginally stable mode, so the corresponding eigenvalue of
`F = (I - K_kf C) A` is pinned at `1` regardless of what the Riccati equation
returns.

The proof is the exact algebraic identity from the paper:
`(I - K C) A u = A u - K (C u) = A u - K·0 = A u = u`.
-/

open Matrix

variable {m n R : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq n]

/-- **Unobservable Invariance (paper Lemma 1).**
If `A *ᵥ u = u` and `C *ᵥ u = 0`, then `((1 - K * C) * A) *ᵥ u = u` for every
matrix `K` of compatible dimension. -/
public theorem unobservable_invariance
    (A : Matrix n n R) (C : Matrix m n R) (K : Matrix n m R) (u : n → R)
    (hA : A *ᵥ u = u) (hC : C *ᵥ u = 0) :
    (((1 : Matrix n n R) - K * C) * A) *ᵥ u = u := by
  rw [← Matrix.mulVec_mulVec, hA, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_zero, sub_zero]
