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
| **Prop. 2 (Grid-Aligned Quantization)** — core invariance `F̃ e₁ = e₁` | [`EncryptedKF/GridAlignedQuantization.lean`](EncryptedKF/GridAlignedQuantization.lean) | `gridAligned_invariance` |
| **Prop. 2** — quantization preserves the marginal column | [`EncryptedKF/GridAlignedQuantization.lean`](EncryptedKF/GridAlignedQuantization.lean) | `gridAligned_quantized_invariance` |
| **Prop. 2** — zero marginal leakage (`L = 0`) | [`EncryptedKF/GridAlignedQuantization.lean`](EncryptedKF/GridAlignedQuantization.lean) | `gridAligned_leakage_zero` |
| **Theorem 1** — error recursion closed form | [`EncryptedKF/DeterministicBound.lean`](EncryptedKF/DeterministicBound.lean) | `error_closed_form` |
| **Theorem 1** — deterministic `O(k)` bound | [`EncryptedKF/DeterministicBound.lean`](EncryptedKF/DeterministicBound.lean) | `deterministic_bounded_error` |
| **Theorem 1** — Schur-stable bounded tube | [`EncryptedKF/DeterministicBound.lean`](EncryptedKF/DeterministicBound.lean) | `deterministic_bounded_error_schur` |

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

### Proposition 2 — Grid-Aligned Quantization

The paper aligns a known marginal eigenvector `u` (with `F u = u`) to a standard
basis vector `e₁` via an integer, unimodular coordinate change `T` (`T u = e₁`),
and writes `F̃ = T F T⁻¹`. The formalization splits the proposition into three
machine-checked parts (over an arbitrary commutative ring `R`):

- **`gridAligned_invariance`** — if `F u = u`, `T u = e`, and `Tinv` is a left
  inverse of `T`, then `(T F Tinv) e = e`. Taking `e = e₁`, this is the paper's
  `F̃ e₁ = e₁`: the marginal column of `F̃` is exactly `(1, 0, …, 0)ᵀ`.
- **`gridAligned_quantized_invariance`** — for any quantizer `qt` with `qt 0 = 0`
  and `qt 1 = 1`, the quantized matrix `F̃.map qt` also fixes `e₁`. The column
  entries (`0`s and a single `1`) are exact fixed points of entrywise
  quantization at every precision.
- **`gridAligned_leakage_zero`** — if both `F̃` and its quantization `F̃_q` fix
  the marginal direction `e`, then `(F̃_q − F̃) e = 0`. The marginal direction
  leaks nowhere, so the leakage term is exactly `0` rather than `O(δ)`.

All proofs are axiom-clean: `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` (no `sorry`).

### Theorem 1 — Deterministic Bounded Error

The implementation-induced error obeys `e[k] = F_q e[k-1] + ε[k]`, where `ε[k]`
is the per-cycle re-encoding disturbance. The paper bounds the error over an
indefinite horizon. The key step is the closed form

```
e[k] = F_q^k e[0] + Σ_{j=1}^k F_q^{k-j} ε[j],
```

in which *every* matrix power is bounded by `κ := sup_m ‖F_q^m‖` — a naive
induction on the recursion would instead accumulate a `κ^k` factor. The results
are formalized for an arbitrary continuous linear operator `T` on a normed
space, which generalizes the paper's quantized matrix `F_q` acting by `mulVec`
(continuous, as the state space is finite dimensional).

- **`error_closed_form`** — `e k = Tᵏ (e 0) + Σ_{i<k} Tⁱ (ε (k-i))`, by induction
  on the recursion.
- **`deterministic_bounded_error`** — if `‖Tᵐ‖ ≤ κ` for all `m` and `‖ε j‖ ≤ ε̄`,
  then `‖e k‖ ≤ κ ‖e 0‖ + k κ ε̄`: the error grows at most linearly in the
  horizon, with a single factor of `κ`.
- **`deterministic_bounded_error_schur`** — if the powers decay geometrically,
  `‖Tᵐ‖ ≤ C ρᵐ` with `0 ≤ ρ < 1`, then `‖e k‖ ≤ C ρᵏ ‖e 0‖ + C ε̄ / (1 - ρ)`:
  the forcing term stays in a bounded invariant error tube of size `O(ε̄)`,
  independent of the horizon.

All three are axiom-clean (`#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`).

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
