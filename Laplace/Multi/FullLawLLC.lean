/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MinibatchFluctuation
import Laplace.Sampler.FullStep

/-!
# The LLC mean under the full (state-dependent) minibatch covariance law (E8)

The note's full law `Σ = AΣAᵀ + N + c∑ᵢDᵢΣDᵢᵀ` (`fullFixed`, `Dᵢ = Hᵢ − H` the per-sample Hessian
deviations,
`c = minibatchCoeff`) dominates the additive (constant-noise) law's solution `Σ^{mb} = lyapunovVia
U ρ N` by at least the
first-order Hessian-fluctuation term (`fullFixed_sub_sub_posSemidef`). In a frame diagonalising `H`
with `λ ≥ 0`,
`tr(HX) = ∑ᵢλᵢ(UᵀXU)ᵢᵢ` is monotone in the PSD order (`trace_mul_nonneg_frame`,
`trace_mul_le_frame`), so
**`tr(HΣ^{mb}) + c·tr(H·stateTerm D Σ^{mb}) ≤ tr(HΣ_full)`** (`fullFixed_trace_ge`) with `0 ≤
tr(H·stateTerm D Σ^{mb})`, and the
LLC mean chain **`(t/2)∑λᵢ/(pᵢκᵢ) ≤ (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) ≤ (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) +
(t/2)c·tr(H·stateTerm D Σ^{mb})
≤ (t/2)tr(HΣ_full)`** (`ula_llc_le_minibatch_llc_frame`, `fullLaw_llc_ge`): the state-dependent
gradient noise inflates the LLC
mean beyond the constant-noise value by at least the **one-step** Hessian-fluctuation term (the
exact first-order correction in `c`
propagates it through the additive Lyapunov resolvent, `Σ_full = Σ^{mb} + c(1 − T)⁻¹B(Σ^{mb}) +
O(c²)`, and is larger), which in the frame
reads `∑ᵢ∑ⱼλⱼ∑ₖₗ(UᵀDᵢU)ⱼₖ Ŝₖₗ (UᵀDᵢU)ⱼₗ` (`trace_stateTerm_frame`). The finite iterates `X_k =
fullStep^k(Σ^{mb})` give monotone lower bounds
`tr(HX_k) ≤ tr(HX_{k+1}) ≤ tr(HΣ_full)` converging to the full law (`fullStep_iterate_trace_mono`,
`fullStep_iterate_trace_le`), and
`c = 0` or `D = 0` recover the additive law exactly (`fullFixed_eq_of_c_zero`,
`fullFixed_eq_of_D_zero`). The identification of
`(t/2)tr(HΣ_full)` with the LLC mean under the (non-Gaussian) full-law stationary distribution uses
only the second-moment identity
`E[½uᵀHu] = ½tr(HΣ) + ½mᵀHm` (prose).
-/

open Matrix Filter Topology Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-! ### The trace against `H ⪰ 0` is monotone in the PSD order -/

omit [DecidableEq ι] in
theorem posSemidef_transpose_mul_mul (U : Matrix ι ι ℝ) {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    (Uᵀ * X * U).PosSemidef := by
  have := hX.conjTranspose_mul_mul_same U
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem trace_mul_nonneg_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) {X : Matrix ι ι ℝ} (hX : X.PosSemidef) : 0 ≤ (H * X).trace := by
  rw [trace_mul_eq_sum_conj_diag hU hdiagH]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (posSemidef_transpose_mul_mul U
      hX).diag_nonneg

theorem trace_mul_le_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) {X Y : Matrix ι ι ℝ} (hXY : (Y - X).PosSemidef) :
    (H * X).trace ≤ (H * Y).trace := by
  have := trace_mul_nonneg_frame hU hdiagH hlam hXY
  rw [Matrix.mul_sub, Matrix.trace_sub] at this
  linarith

/-! ### The full law dominates the additive law in the LLC mean -/

/-- **E8, full law**: `tr(HΣ^{mb}) + c·tr(H·stateTerm D Σ^{mb}) ≤ tr(HΣ_full)`. -/
theorem fullFixed_trace_ge (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (D : Fin n → Matrix ι ι
        ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    (H * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C)).trace + c * (H * stateTerm D
        (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))).trace ≤ (H * fullFixed
            (ulaStep P h) (minibatchNoise h t C) D hc hK).trace := by
  have hS : covStep (ulaStep P h) (minibatchNoise h t C) (lyapunovVia U (fun i => 1 - h * p i)
      (minibatchNoise h t C)) = lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) :=
    (minibatch_fixed_iff_frame hU hdiag hp hh hev t C _).2 rfl
  have hSpsd : (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C)).PosSemidef :=
      (minibatchCov_posDef_frame hU hp hh hev t hC).posSemidef
  have h1 := trace_mul_nonneg_frame hU hdiagH hlam (fullFixed_sub_sub_posSemidef _ _ D hc hK hS
      hSpsd)
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul] at h1
  linarith

theorem stateTerm_trace_nonneg (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) (D : Fin n → Matrix ι ι ℝ) {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    0 ≤ (H * stateTerm D X).trace :=
  trace_mul_nonneg_frame hU hdiagH hlam (stateTerm_posSemidef D hX)

/-- `tr(HΣ^{mb}) ≤ tr(HΣ_full)`. -/
theorem fullFixed_trace_ge' (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (D : Fin n → Matrix ι ι
        ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    (H * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C)).trace ≤ (H * fullFixed
        (ulaStep P h) (minibatchNoise h t C) D hc hK).trace := by
  have h1 := fullFixed_trace_ge hU hdiag hp hh hev hdiagH hlam t hC D hc hK
  have h2 := stateTerm_trace_nonneg hU hdiagH hlam D
    (minibatchCov_posDef_frame hU hp hh hev t hC).posSemidef
  nlinarith

omit [DecidableEq ι] in
/-- The constant-noise LLC mean dominates the exact-gradient one: `Ĉᵢᵢ ≥ 0`. -/
theorem ula_llc_le_minibatch_llc_frame (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    t / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2))) ≤
      t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) :=
          by
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  have hCU := posSemidef_transpose_mul_mul U hC
  have hκ : 0 < p i * (1 - h * p i / 2) := mul_pos (hp i) (by linarith [hev i])
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hκ.le) (hlam i)
  have : 0 ≤ h * t ^ 2 * (Uᵀ * C * U) i i / 2 := by
    have := hCU.diag_nonneg (i := i)
    positivity
  linarith

/-- **The LLC mean chain under the full law**:
`(t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)c·tr(H·stateTerm D Σ^{mb}) ≤ (t/2)tr(HΣ_full)`. -/
theorem fullLaw_llc_ge (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
        t / 2 * (c * (H * stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t
            C))).trace) ≤
      t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace := by
  rw [← minibatch_llc_frame hU hdiagH hp hh hev t C, ← mul_add]
  exact mul_le_mul_of_nonneg_left (fullFixed_trace_ge hU hdiag hp hh hev hdiagH hlam t hC D hc hK)
    (by positivity)

/-! ### Monotone finite-iterate bounds and the zero-noise equalities -/

omit [DecidableEq ι] in
theorem fullLinear_posSemidef (A : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) : (fullLinear A D c Y).PosSemidef := by
  unfold fullLinear
  refine Matrix.PosSemidef.add ?_ ((stateTerm_posSemidef D hY).smul hc)
  have := hY.mul_mul_conjTranspose_same A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- `Σ_full − fullStep^k(S) ⪰ 0` for any fixed point `S` of the additive law. -/
theorem fullFixed_sub_iterate_posSemidef (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S)
    (hSpsd : S.PosSemidef) (k : ℕ) :
    (fullFixed A N D hc hK - (fullStep A N D c)^[k] S).PosSemidef := by
  induction k with
  | zero => simpa using fullFixed_sub_posSemidef A N D hc hK hS hSpsd
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← fullStep_fullFixed A N D hc hK, fullStep_sub]
    exact fullLinear_posSemidef A D hc ih

omit [DecidableEq ι] in
/-- `fullStep^{k+1}(S) − fullStep^k(S) ⪰ 0`: the iterates from the additive fixed point increase. -/
theorem fullStep_iterate_succ_sub_posSemidef (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hSpsd : S.PosSemidef) (k : ℕ) :
    ((fullStep A N D c)^[k + 1] S - (fullStep A N D c)^[k] S).PosSemidef := by
  induction k with
  | zero =>
    have e : fullStep A N D c S - S = c • stateTerm D S := by
      have h' : A * S * Aᵀ + N = S := hS
      unfold fullStep fullLinear
      rw [show A * S * Aᵀ + c • stateTerm D S + N - S = (A * S * Aᵀ + N) + c • stateTerm D S - S by
        abel, h']
      abel
    simpa [e] using (stateTerm_posSemidef D hSpsd).smul hc
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fullStep_sub]
    exact fullLinear_posSemidef A D hc ih

/-- The LLC lower bounds from the finite iterates increase with `k`. -/
theorem fullStep_iterate_trace_mono (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hSpsd : S.PosSemidef) (k : ℕ) :
    (H * (fullStep A N D c)^[k] S).trace ≤ (H * (fullStep A N D c)^[k + 1] S).trace :=
  trace_mul_le_frame hU hdiagH hlam (fullStep_iterate_succ_sub_posSemidef A N D hc hS hSpsd k)

/-- Every finite iterate is a lower bound for the full law's LLC mean. -/
theorem fullStep_iterate_trace_le (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hSpsd :
        S.PosSemidef)
    (k : ℕ) : (H * (fullStep A N D c)^[k] S).trace ≤ (H * fullFixed A N D hc hK).trace :=
  trace_mul_le_frame hU hdiagH hlam (fullFixed_sub_iterate_posSemidef A N D hc hK hS hSpsd k)

/-- `c = 0`: the full law is the additive law. -/
theorem fullFixed_eq_of_c_zero (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ)
    (hK : fullLipschitz A D 0 < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) :
    fullFixed A N D (le_refl 0) hK = S := by
  refine (eq_fullFixed_of_fixed A N D (le_refl 0) hK ?_).symm
  unfold fullStep fullLinear
  rw [zero_smul, add_zero]
  exact hS

/-- `D = 0`: the full law is the additive law. -/
theorem fullFixed_eq_of_D_zero (A N : Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A (fun _ : Fin n => (0 : Matrix ι ι ℝ)) c < 1) {S : Matrix ι ι ℝ}
    (hS : covStep A N S = S) : fullFixed A N (fun _ : Fin n => (0 : Matrix ι ι ℝ)) hc hK = S := by
  refine (eq_fullFixed_of_fixed A N _ hc hK ?_).symm
  unfold fullStep fullLinear stateTerm
  simp only [Matrix.zero_mul, Matrix.transpose_zero, Matrix.mul_zero, Finset.sum_const_zero,
      smul_zero,
    add_zero]
  exact hS

/-! ### The first-order term in the frame -/

theorem trace_mul_conj_apply (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (Dm S : Matrix ι ι ℝ) :
    (H * (Dm * S * Dmᵀ)).trace =
      ∑ j, lam j * ∑ k, ∑ l, (Uᵀ * Dm * U) j k * (Uᵀ * S * U) k l * (Uᵀ * Dm * U) j l := by
  rw [trace_mul_eq_sum_conj_diag hU hdiagH]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hUU := mul_transpose_eq_one_of hU
  have e : Uᵀ * (Dm * S * Dmᵀ) * U = (Uᵀ * Dm * U) * (Uᵀ * S * U) * (Uᵀ * Dm * U)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hUU, Matrix.one_mul, ← Matrix.mul_assoc U Uᵀ, hUU, Matrix.one_mul]
  rw [e, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply]

/-- `tr(H∑ᵢDᵢSDᵢᵀ) = ∑ᵢ∑ⱼλⱼ∑ₖₗ(UᵀDᵢU)ⱼₖ(UᵀSU)ₖₗ(UᵀDᵢU)ⱼₗ`. -/
theorem trace_stateTerm_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (D : Fin n → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) :
    (H * stateTerm D S).trace =
      ∑ i, ∑ j, lam j * ∑ k, ∑ l, (Uᵀ * D i * U) j k * (Uᵀ * S * U) k l * (Uᵀ * D i * U) j l := by
  unfold stateTerm
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i _ => trace_mul_conj_apply hU hdiagH (D i) S

end Frame

end Laplace.Sampler
