# EncryptedKF-Lean

Machine-checked proofs accompanying the paper
**"Encrypted Kalman Filtering with Bounded-Error Guarantees"** (R. Lois and
D. G. Cole).

The proofs are formalized in [Lean 4](https://lean-lang.org/) using the
[Mathlib](https://github.com/leanprover-community/mathlib4) library, and are
verified by the Lean kernel on every build.

## Contents

| Paper result | Lean file | Lean name |
|---|---|---|
| **Lemma 1 (Unobservable Invariance)** | [`EncryptedKF/UnobservableInvariance.lean`](EncryptedKF/UnobservableInvariance.lean) | `unobservable_invariance` |

### Lemma 1 — Unobservable Invariance

> If `u` is an eigenvector of `A` at eigenvalue `1` with `Cu = 0`, then
> `(I − KC)Au = u` for every matrix `K` of compatible dimension.

This is the gain-independence property the paper relies on in Proposition 2
(grid-aligned quantization), Proposition 3 (stochastic marginal-mode
refinement), and the benchmark of Section 6: no Kalman gain can move an
unobservable, marginally stable mode, so the corresponding eigenvalue of the
deployed closed-loop matrix `F = (I − K_kf C)A` is pinned at `1` regardless of
what the Riccati equation returns.

The Lean statement is a faithful transcription over an arbitrary commutative
ring `R`, with `A : Matrix n n R`, `C : Matrix m n R`, `K : Matrix n m R`, and
`u : n → R`:

```lean
theorem unobservable_invariance
    (A : Matrix n n R) (C : Matrix m n R) (K : Matrix n m R) (u : n → R)
    (hA : A *ᵥ u = u) (hC : C *ᵥ u = 0) :
    (((1 : Matrix n n R) - K * C) * A) *ᵥ u = u
```

The proof is the exact algebraic identity from the paper,
`(I − KC)Au = Au − K(Cu) = Au = u`, discharged by rewriting with the matrix
`mulVec` lemmas of Mathlib.

## Building / verifying

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager); the pinned toolchain (`lean-toolchain`) and Mathlib version
(`lakefile.toml`, Mathlib `v4.35.0`) are fetched automatically.

```bash
lake exe cache get   # download the prebuilt Mathlib cache (first time only)
lake build           # compile and kernel-check all proofs
```

A successful `lake build` means the Lean kernel has verified every theorem in
this repository.

## Notes

- Toolchain: Lean `v4.35.0`, Mathlib `v4.35.0`.
- The formalization was developed with the assistance of Claude Code
  (Anthropic).
