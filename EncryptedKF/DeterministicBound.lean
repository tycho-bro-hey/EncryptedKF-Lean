module

public import Mathlib

/-!
# Deterministic Bounded Error (paper Theorem 1)

Formalization of Theorem 1 of *"Encrypted Kalman Filtering with Bounded-Error
Guarantees"* (Lois & Cole).

The implementation-induced error obeys the recursion `e[k] = F_q e[k-1] + ε[k]`,
where `ε[k]` is the per-cycle re-encoding disturbance. The paper bounds the error
over an indefinite horizon. The key step is the closed form
`e[k] = F_q^k e[0] + Σ_{j=1}^k F_q^{k-j} ε[j]`, in which *every* matrix power is
bounded by `κ := sup_m ‖F_q^m‖`; a naive induction on the recursion would instead
accumulate a `κ^k` factor.

We formalize the result for an arbitrary continuous linear operator `T` on a
normed space, which generalizes the paper's quantized matrix `F_q` acting by
`mulVec` (a continuous linear map, since the state space is finite dimensional).
`κ` and `ε̄` are the operator-power bound and the re-encoding bound of the paper.
-/

open Finset

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]

/-- **Closed form of the error recursion (paper Thm 1 proof).**
If `e (k+1) = T (e k) + ε (k+1)` for all `k`, then
`e k = Tᵏ (e 0) + Σ_{i<k} Tⁱ (ε (k-i))`. (Re-indexing `i = k-j` of the paper's
`Σ_{j=1}^k F_q^{k-j} ε[j]`.) -/
public theorem error_closed_form (T : V →L[𝕜] V) (e ε : ℕ → V)
    (hrec : ∀ k, e (k + 1) = T (e k) + ε (k + 1)) (k : ℕ) :
    e k = (T ^ k) (e 0) + ∑ i ∈ range k, (T ^ i) (ε (k - i)) := by
  have hcomp : ∀ (i : ℕ) (x : V), (T ^ (i + 1)) x = T ((T ^ i) x) := fun i x => by
    simp [pow_succ']
  have hone : ∀ x : V, (T ^ 0) x = x := fun x => by simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hrec k, ih, map_add, map_sum, Finset.sum_range_succ']
    simp only [hcomp, hone, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    abel

/-- **Deterministic bounded error (paper Theorem 1).**
If the operator powers are uniformly bounded, `‖Tᵐ‖ ≤ κ` for all `m`, and the
per-cycle disturbance satisfies `‖ε j‖ ≤ ε̄`, then
`‖e k‖ ≤ κ ‖e 0‖ + k κ ε̄`. The bound grows at most linearly in the horizon `k`,
with a single factor of `κ`. -/
public theorem deterministic_bounded_error (T : V →L[𝕜] V) (e ε : ℕ → V)
    (hrec : ∀ k, e (k + 1) = T (e k) + ε (k + 1))
    (κ εbar : ℝ) (hκ : ∀ m, ‖T ^ m‖ ≤ κ) (hε : ∀ j, ‖ε j‖ ≤ εbar) (k : ℕ) :
    ‖e k‖ ≤ κ * ‖e 0‖ + k * κ * εbar := by
  have hκ0 : 0 ≤ κ := le_trans (norm_nonneg _) (hκ 0)
  have hεbar0 : 0 ≤ εbar := le_trans (norm_nonneg _) (hε 0)
  rw [error_closed_form T e ε hrec k]
  calc ‖(T ^ k) (e 0) + ∑ i ∈ range k, (T ^ i) (ε (k - i))‖
      ≤ ‖(T ^ k) (e 0)‖ + ‖∑ i ∈ range k, (T ^ i) (ε (k - i))‖ := norm_add_le _ _
    _ ≤ κ * ‖e 0‖ + ∑ i ∈ range k, κ * εbar := by
        gcongr
        · calc ‖(T ^ k) (e 0)‖ ≤ ‖T ^ k‖ * ‖e 0‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ κ * ‖e 0‖ := by gcongr; exact hκ k
        · calc ‖∑ i ∈ range k, (T ^ i) (ε (k - i))‖
                ≤ ∑ i ∈ range k, ‖(T ^ i) (ε (k - i))‖ := norm_sum_le _ _
            _ ≤ ∑ i ∈ range k, κ * εbar := by
                apply Finset.sum_le_sum
                intro i _
                calc ‖(T ^ i) (ε (k - i))‖ ≤ ‖T ^ i‖ * ‖ε (k - i)‖ :=
                      ContinuousLinearMap.le_opNorm _ _
                  _ ≤ κ * εbar := by gcongr; exacts [hκ i, hε _]
    _ = κ * ‖e 0‖ + k * κ * εbar := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Schur-stable refinement (paper Theorem 1, final clause).**
If the operator powers decay geometrically, `‖Tᵐ‖ ≤ C ρᵐ` with `0 ≤ ρ < 1`, then
the error is uniformly bounded for all `k`:
`‖e k‖ ≤ C ρᵏ ‖e 0‖ + C ε̄ / (1 - ρ)`.
The forcing term no longer grows with the horizon: repeated rounding is confined
to a bounded invariant error tube of size `O(ε̄) = O(2^{-Υ})`. -/
public theorem deterministic_bounded_error_schur (T : V →L[𝕜] V) (e ε : ℕ → V)
    (hrec : ∀ k, e (k + 1) = T (e k) + ε (k + 1))
    (C ρ εbar : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpow : ∀ m, ‖T ^ m‖ ≤ C * ρ ^ m) (hε : ∀ j, ‖ε j‖ ≤ εbar) (k : ℕ) :
    ‖e k‖ ≤ C * ρ ^ k * ‖e 0‖ + C * εbar / (1 - ρ) := by
  have hC0 : 0 ≤ C := by have h := hpow 0; simpa using le_trans (norm_nonneg _) h
  have hεbar0 : 0 ≤ εbar := le_trans (norm_nonneg _) (hε 0)
  have hgeom : ∑ i ∈ range k, ρ ^ i ≤ (1 - ρ)⁻¹ := by
    have hpos : (0 : ℝ) < 1 - ρ := by linarith
    have h2 : (∑ i ∈ range k, ρ ^ i) * (1 - ρ) = 1 - ρ ^ k := by
      linear_combination -geom_sum_mul ρ k
    rw [inv_eq_one_div, le_div_iff₀ hpos, h2]
    have : 0 ≤ ρ ^ k := pow_nonneg hρ0 k
    linarith
  have hinit : ‖(T ^ k) (e 0)‖ ≤ C * ρ ^ k * ‖e 0‖ :=
    calc ‖(T ^ k) (e 0)‖ ≤ ‖T ^ k‖ * ‖e 0‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ρ ^ k * ‖e 0‖ := mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _)
  have hforcing : ‖∑ i ∈ range k, (T ^ i) (ε (k - i))‖ ≤ C * εbar / (1 - ρ) :=
    calc ‖∑ i ∈ range k, (T ^ i) (ε (k - i))‖
          ≤ ∑ i ∈ range k, ‖(T ^ i) (ε (k - i))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range k, C * ρ ^ i * εbar :=
            Finset.sum_le_sum fun i _ =>
              calc ‖(T ^ i) (ε (k - i))‖ ≤ ‖T ^ i‖ * ‖ε (k - i)‖ :=
                    ContinuousLinearMap.le_opNorm _ _
                _ ≤ C * ρ ^ i * εbar := by gcongr; exacts [hpow i, hε _]
      _ = ∑ i ∈ range k, C * εbar * ρ ^ i := Finset.sum_congr rfl fun i _ => by ring
      _ = C * εbar * ∑ i ∈ range k, ρ ^ i := by rw [Finset.mul_sum]
      _ ≤ C * εbar * (1 - ρ)⁻¹ := mul_le_mul_of_nonneg_left hgeom (mul_nonneg hC0 hεbar0)
      _ = C * εbar / (1 - ρ) := (div_eq_mul_inv _ _).symm
  rw [error_closed_form T e ε hrec k]
  calc ‖(T ^ k) (e 0) + ∑ i ∈ range k, (T ^ i) (ε (k - i))‖
        ≤ ‖(T ^ k) (e 0)‖ + ‖∑ i ∈ range k, (T ^ i) (ε (k - i))‖ := norm_add_le _ _
    _ ≤ C * ρ ^ k * ‖e 0‖ + C * εbar / (1 - ρ) := add_le_add hinit hforcing
