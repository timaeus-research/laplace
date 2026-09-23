/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FullLawLLC

/-!
# The full law is `O(c)` from the additive law (E8, upper bounds)

Tide 107 showed that the solution `Σ_full` of the state-dependent minibatch covariance law `X ↦
AXAᵀ + N + c∑ᵢDᵢXDᵢᵀ` dominates the
additive solution `Σ^{mb}` and that the LLC mean under the full law exceeds the constant-noise
value by at least the one-step term
`c·tr(HB(Σ^{mb}))`, `B(X) = ∑ᵢDᵢXDᵢᵀ`. This file gives the matching upper bounds from Banach's
a-priori estimate for the contraction
(`ℓ∞` operator norm, Lipschitz constant `L = ‖A‖‖Aᵀ‖ + c∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖ < 1`):
* `‖Σ_full − Σ^{mb}‖ ≤ c‖B(Σ^{mb})‖/(1−L) ≤ c(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖Σ^{mb}‖/(1−L)` (`fullFixed_sub_norm_le`,
`fullFixed_sub_norm_le'`), entrywise too
  (`abs_fullFixed_sub_entry_le`): the state-dependent correction to the stationary covariance is
  `O(c)`;
* `tr(HΣ_full) ≤ tr(HΣ^{mb}) + d‖H‖·c‖B(Σ^{mb})‖/(1−L)` (`trace_fullFixed_le`), hence the two-sided
LLC bound
  `LLC^{mb} + (t/2)c·tr(HB(Σ^{mb})) ≤ (t/2)tr(HΣ_full) ≤ LLC^{mb} + (t/2)d‖H‖c‖B(Σ^{mb})‖/(1−L)`
  (`fullLaw_llc_le`, with tide 107's `fullLaw_llc_ge`);
* the note's instance `c = h²t²(1−m/n)/(m(n−1))`, `Dᵢ = Hᵢ − H` (`e8_fullFixed_sub_norm_le`): the
Hessian-fluctuation correction is
  `O(c/(1−L))`, i.e. `O(ht²/m)` once the contraction gap `1 − L = Θ(h)` is accounted for.
The contraction hypothesis is norm-dependent: for `A = I − hP` it is the eigenbasis (frame) form
`max|1−hpᵢ| < 1` that is automatic; in a
general basis `‖A‖‖Aᵀ‖` may exceed `1` although the iteration converges, so the bounds are stated
conditionally on `L < 1`.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-! ### Entries and traces against the `ℓ∞` operator norm -/

/-- Every entry is bounded by the `ℓ∞` operator norm. -/
theorem abs_entry_le_linfty_opNorm (M : Matrix ι ι ℝ) (i j : ι) : |M i j| ≤ ‖M‖ := by
  rw [linfty_opNorm_def]
  have h1 : ‖M i j‖₊ ≤ ∑ j, ‖M i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 : (∑ j, ‖M i j‖₊) ≤ Finset.univ.sup (fun i => ∑ j, ‖M i j‖₊) :=
    Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h3 := h1.trans h2
  rw [← Real.norm_eq_abs, ← coe_nnnorm]
  exact_mod_cast h3

/-- `|tr M| ≤ d·‖M‖`. -/
theorem abs_trace_le (M : Matrix ι ι ℝ) : |M.trace| ≤ Fintype.card ι * ‖M‖ := by
  unfold Matrix.trace
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |Matrix.diag M i| ≤ ∑ i : ι, ‖M‖ :=
        Finset.sum_le_sum fun i _ => abs_entry_le_linfty_opNorm M i i
    _ = Fintype.card ι * ‖M‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `|tr(HX)| ≤ d·‖H‖·‖X‖`. -/
theorem abs_trace_mul_le (H X : Matrix ι ι ℝ) : |(H * X).trace| ≤ Fintype.card ι * (‖H‖ * ‖X‖) :=
  (abs_trace_le _).trans (mul_le_mul_of_nonneg_left (linfty_opNorm_mul H X) (by positivity))

/-! ### The a-priori estimate for the full law -/

/-- **The full law is `O(c)` from the additive law**: `‖Σ_full − Σ_add‖ ≤ c‖B(Σ_add)‖/(1 − L)`. -/
theorem fullFixed_sub_norm_le (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) :
    ‖fullFixed A N D hc hK - S‖ ≤ c * ‖stateTerm D S‖ / (1 - fullLipschitz A D c) := by
  have h : dist S (fullFixed A N D hc hK) ≤
      dist S (fullStep A N D c S) / (1 - fullLipschitz A D c) :=
    (contractingWith_fullStep A N D hc hK).dist_fixedPoint_le S
  rw [dist_eq_norm, dist_eq_norm] at h
  have e : S - fullStep A N D c S = -(c • stateTerm D S) := by
    have h2 := fullStep_sub_covStep A N D c S
    rw [hS] at h2
    rw [← h2]
    abel
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at h
  rw [norm_sub_rev]
  exact h

/-- Explicit `O(c)`: `‖Σ_full − Σ_add‖ ≤ c(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖Σ_add‖/(1 − L)`. -/
theorem fullFixed_sub_norm_le' (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) :
    ‖fullFixed A N D hc hK - S‖ ≤
      c * (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖S‖ / (1 - fullLipschitz A D c) := by
  refine (fullFixed_sub_norm_le A N D hc hK hS).trans ?_
  have h1L : 0 < 1 - fullLipschitz A D c := sub_pos.2 hK
  refine div_le_div_of_nonneg_right ?_ h1L.le
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_stateTerm_le D S) hc

/-- Relative: `‖Σ_full − Σ_add‖/‖Σ_add‖ ≤ c(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)/(1 − L)`. -/
theorem fullFixed_sub_norm_div_le (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤
    c)
    (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) (hS0 : S ≠ 0) :
    ‖fullFixed A N D hc hK - S‖ / ‖S‖ ≤ c * (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) / (1 - fullLipschitz A D c) :=
        by
  rw [div_le_iff₀ (norm_pos_iff.2 hS0)]
  exact (fullFixed_sub_norm_le' A N D hc hK hS).trans (le_of_eq (by ring))

/-- Entrywise: `|(Σ_full)ᵢⱼ − (Σ_add)ᵢⱼ| ≤ c‖B(Σ_add)‖/(1 − L)`. -/
theorem abs_fullFixed_sub_entry_le (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S)
    (i j : ι) :
    |fullFixed A N D hc hK i j - S i j| ≤ c * ‖stateTerm D S‖ / (1 - fullLipschitz A D c) := by
  have h := abs_entry_le_linfty_opNorm (fullFixed A N D hc hK - S) i j
  rw [Matrix.sub_apply] at h
  exact h.trans (fullFixed_sub_norm_le A N D hc hK hS)

/-- **Upper bound on the trace**: `tr(HΣ_full) ≤ tr(HΣ_add) + d‖H‖·c‖B(Σ_add)‖/(1 − L)`. -/
theorem trace_fullFixed_le (H A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz A D c < 1) {S : Matrix ι ι ℝ} (hS : covStep A N S = S) :
    (H * fullFixed A N D hc hK).trace ≤ (H * S).trace +
      Fintype.card ι * ‖H‖ * (c * ‖stateTerm D S‖ / (1 - fullLipschitz A D c)) := by
  have h1 := abs_trace_mul_le H (fullFixed A N D hc hK - S)
  rw [Matrix.mul_sub, Matrix.trace_sub] at h1
  have h2 := fullFixed_sub_norm_le A N D hc hK hS
  have h3 : |(H * fullFixed A N D hc hK).trace - (H * S).trace| ≤
      Fintype.card ι * ‖H‖ * (c * ‖stateTerm D S‖ / (1 - fullLipschitz A D c)) := by
    refine h1.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith [(abs_le.1 h3).2]

/-! ### The E8 instance -/

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-- **The LLC mean under the full law, upper bound**:
`(t/2)tr(HΣ_full) ≤ (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)·d‖H‖·c‖B(Σ^{mb})‖/(1 − L)`. -/
theorem fullLaw_llc_le (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) {t : ℝ}
    (ht : 0 ≤ t) (C : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hK : fullLipschitz (ulaStep P h) D c < 1) :
    t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace ≤
      t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
        t / 2 * (Fintype.card ι * ‖H‖ * (c * ‖stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
            (minibatchNoise h t C))‖ /
          (1 - fullLipschitz (ulaStep P h) D c))) := by
  have hS : covStep (ulaStep P h) (minibatchNoise h t C) (lyapunovVia U (fun i => 1 - h * p i)
      (minibatchNoise h t C)) = lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) :=
    (minibatch_fixed_iff_frame hU hdiag hp hh hev t C _).2 rfl
  rw [← minibatch_llc_frame hU hdiagH hp hh hev t C, ← mul_add]
  exact mul_le_mul_of_nonneg_left (trace_fullFixed_le H _ _ D hc hK hS) (by positivity)

/-- **Two-sided**: with tide 107, `LLC^{mb} + (t/2)c·tr(HB(Σ^{mb})) ≤ (t/2)tr(HΣ_full) ≤ LLC^{mb} +
(t/2)d‖H‖c‖B(Σ^{mb})‖/(1−L)`. -/
theorem fullLaw_llc_bounds (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
        t / 2 * (c * (H * stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t
            C))).trace) ≤ t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc
                hK).trace ∧
      t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace ≤
        t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
          t / 2 * (Fintype.card ι * ‖H‖ * (c * ‖stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
              (minibatchNoise h t C))‖ /
            (1 - fullLipschitz (ulaStep P h) D c))) :=
  ⟨fullLaw_llc_ge hU hdiag hp hh hev hdiagH hlam ht hC D hc hK,
    fullLaw_llc_le hU hdiag hp hh hev hdiagH ht C D hc hK⟩

end Frame

/-- **The note's instance**: with `c = h²t²(1−m/n)/(m(n−1))` and `Dᵢ = Hᵢ − H`, the
Hessian-fluctuation correction to the stationary
covariance is bounded by `c(∑ᵢ‖Hᵢ−H‖‖(Hᵢ−H)ᵀ‖)‖Σ^{mb}‖/(1−L)`: `O(c/(1−L))` with `c = O(h²t²/m)`.
Since the contraction gap `1 − L` is itself
`Θ(h)` at small step, this is `O(ht²/m)` in general, not `O(h²t²/m)` (a fixed-gap perturbation
statement). -/
theorem e8_fullFixed_sub_norm_le (P : Matrix ι ι ℝ) (h t : ℝ) (C : Matrix ι ι ℝ)
    (Hs : Fin n → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hK : fullLipschitz (ulaStep P h) (fun i => Hs i - H) (minibatchCoeff h t m n) < 1)
    {S : Matrix ι ι ℝ} (hS : covStep (ulaStep P h) (minibatchNoise h t C) S = S) :
    ‖fullFixed (ulaStep P h) (minibatchNoise h t C) (fun i => Hs i - H) (minibatchCoeff_nonneg h t
        hm hmn) hK
        - S‖ ≤ minibatchCoeff h t m n * (∑ i, ‖Hs i - H‖ * ‖(Hs i - H)ᵀ‖) * ‖S‖ /
      (1 - fullLipschitz (ulaStep P h) (fun i => Hs i - H) (minibatchCoeff h t m n)) :=
  fullFixed_sub_norm_le' _ _ _ (minibatchCoeff_nonneg h t hm hmn) hK hS

end Laplace.Sampler
