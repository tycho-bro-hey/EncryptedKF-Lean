module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Grid-Aligned Quantization (paper Proposition 2)

Formalization of Proposition 2 of *"Encrypted Kalman Filtering with Bounded-Error
Guarantees"* (Lois & Cole).

The paper aligns a known marginal eigenvector `u` (with `F u = u`) to a standard
basis vector `e₁` via an integer, unimodular coordinate change `T` (`T u = e₁`,
`T` and `T⁻¹` integer). Writing `F̃ = T F T⁻¹`:

1. `gridAligned_invariance` : `F̃ e₁ = e₁` exactly — the marginal column of `F̃`
   is `(1,0,…,0)ᵀ`.
2. `gridAligned_quantized_invariance` : the quantized matrix `F̃.map qt` also
   fixes `e₁`, because the column entries (`0`s and a single `1`) are exact fixed
   points of any quantizer `qt` with `qt 0 = 0` and `qt 1 = 1`, at every
   precision.
3. `gridAligned_leakage_zero` : the leakage `(F̃_q − F̃) e₁ = 0` — the marginal
   direction leaks nowhere, so the leakage term is exactly `0` rather than
   `O(δ)`.
-/

open Matrix

variable {n R : Type*} [CommRing R] [Fintype n]

/-- Evaluating `M *ᵥ eⱼ` (with `eⱼ = Pi.single j 1`) at index `i` returns the
entry `M i j`: the matrix-vector product against a standard basis vector reads
off the `j`-th column. -/
private theorem mulVec_single_one_apply [DecidableEq n] (M : Matrix n n R) (j i : n) :
    (M *ᵥ Pi.single j (1 : R)) i = M i j := by
  simp

/-- **Core invariance under the unimodular change of coordinates (paper Prop. 2).**
If `F u = u`, the coordinate change sends `u` to `e` (`T u = e`), and `Tinv` is a
left inverse of `T`, then the transformed matrix `T F Tinv` fixes `e`. Taking
`e = e₁`, this is `F̃ e₁ = e₁`. -/
public theorem gridAligned_invariance [DecidableEq n]
    (F T Tinv : Matrix n n R) (u e : n → R)
    (hFu : F *ᵥ u = u) (hTu : T *ᵥ u = e) (hTinv : Tinv * T = 1) :
    (T * F * Tinv) *ᵥ e = e := by
  have hTinv_e : Tinv *ᵥ e = u := by
    rw [← hTu, Matrix.mulVec_mulVec, hTinv, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hTinv_e, ← Matrix.mulVec_mulVec, hFu, hTu]

/-- **Quantization preserves the marginal column (paper Prop. 2).**
If the `i₀`-column of `F̃` is the standard basis vector `e₁ = Pi.single i₀ 1`
(`F̃ e₁ = e₁`) and the quantizer `qt` fixes `0` and `1`, then the quantized
matrix `F̃.map qt` also fixes `e₁`. The column entries are exact fixed points of
entrywise quantization at every precision. -/
public theorem gridAligned_quantized_invariance [DecidableEq n]
    (Ftil : Matrix n n R) (qt : R → R) (i₀ : n)
    (hq0 : qt 0 = 0) (hq1 : qt 1 = 1)
    (hcol : Ftil *ᵥ Pi.single i₀ (1 : R) = Pi.single i₀ (1 : R)) :
    (Ftil.map qt) *ᵥ Pi.single i₀ (1 : R) = Pi.single i₀ (1 : R) := by
  funext i
  have h := congrFun hcol i
  rw [mulVec_single_one_apply] at h
  rw [mulVec_single_one_apply, Matrix.map_apply, h]
  rcases eq_or_ne i i₀ with hi | hi
  · subst hi; simp [hq1]
  · simp [Pi.single_eq_of_ne hi, hq0]

/-- **Zero marginal leakage (paper Prop. 2, `L = 0`).**
If both `F̃` and its quantization `F̃_q` fix the marginal direction `e`, then the
difference `F̃_q − F̃` annihilates `e`: the marginal direction leaks nowhere, so
the leakage term is exactly `0` rather than `O(δ)`. -/
public theorem gridAligned_leakage_zero
    (Ftil Fq : Matrix n n R) (e : n → R)
    (hF : Ftil *ᵥ e = e) (hFq : Fq *ᵥ e = e) :
    (Fq - Ftil) *ᵥ e = 0 := by
  rw [Matrix.sub_mulVec, hFq, hF, sub_self]
