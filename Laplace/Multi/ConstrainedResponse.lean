/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.QuotientMeanMap
import Laplace.Multi.MeanMapJacobian

/-!
# Constrained responses: the Schur complement

Move the data in the direction `v` while adjusting the direction `w` so that the response `⟨R_w⟩`
stays constant. The free response `⟨R_v⟩` then changes at the rate

  `d/ds ⟨R_v⟩ = −t (Var(R_v) − Cov(R_v, R_w)² / Var(R_w))`   (`constrained_response_deriv`),

the Schur complement of the covariance matrix, which is the variance of the residual of `R_v` after
linear regression on `R_w` (`schur_eq_var_residual`) and is positive unless `R_v` is a.e. an affine
function of `R_w` (`schur_pos_iff`). This is the one mechanism behind the fixed-mean monotonicity of
the two-monomial wall's mean band and the residual-variance law of the temperature slices.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
/-- Bilinearity of the covariance in the contrast direction (left slot). -/
theorem priorCov_dirLoss_add_smul (a : ι → ℝ) (v w : ι → ℝ) (c : ℝ) {ψ : X → ℝ}
    (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) (dirLoss R (v + c • w)) ψ t =
      priorCov μ π (affLoss L₀ R a) (dirLoss R v) ψ t +
        c * priorCov μ π (affLoss L₀ R a) (dirLoss R w) ψ t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  rw [← sum_mul_priorCov_eq hν hR hψ, ← sum_mul_priorCov_eq hν hR hψ,
    ← sum_mul_priorCov_eq hν hR hψ, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Nonempty X] in
/-- Bilinearity of the covariance in the contrast direction (right slot). -/
theorem priorCov_dirLoss_add_smul_right (a : ι → ℝ) (v w : ι → ℝ) (c : ℝ) {ψ : X → ℝ}
    (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) ψ (dirLoss R (v + c • w)) t =
      priorCov μ π (affLoss L₀ R a) ψ (dirLoss R v) t +
        c * priorCov μ π (affLoss L₀ R a) ψ (dirLoss R w) t := by
  rw [priorCov_comm, priorCov_dirLoss_add_smul hπm hπi hπ hπpos hL₀m hL₀ hR a v w c hψ,
    priorCov_comm π _ (dirLoss R v) ψ t, priorCov_comm π _ (dirLoss R w) ψ t]

omit [Nonempty X] in
/-- The Schur complement `Var(R_v) − Cov(R_v,R_w)²/Var(R_w)` is the variance of the regression
residual `R_{v − λ w}`, `λ = Cov(R_v,R_w)/Var(R_w)`. -/
theorem schur_eq_var_residual (a : ι → ℝ) (v w : ι → ℝ)
    (hw : priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t ≠ 0) :
    priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t -
        priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R w) t ^ 2 /
          priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t =
      priorCov μ π (affLoss L₀ R a)
        (dirLoss R (v + (-(priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R w) t /
          priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t)) • w))
        (dirLoss R (v + (-(priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R w) t /
          priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t)) • w)) t := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = -(priorCov μ π (affLoss L₀ R a) (dirLoss R v)
    (dirLoss R w) t / priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t) := ⟨_, rfl⟩
  rw [← hlam]
  have hvw := bdd_dirLoss hR (v + lam • w)
  rw [priorCov_dirLoss_add_smul hπm hπi hπ hπpos hL₀m hL₀ hR a v w lam hvw,
    priorCov_dirLoss_add_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR a v w lam (bdd_dirLoss hR v),
    priorCov_dirLoss_add_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR a v w lam (bdd_dirLoss hR w),
    priorCov_comm π _ (dirLoss R w) (dirLoss R v) t, hlam]
  field_simp
  ring

/-- The Schur complement is positive iff `R_v` is not a.e. an affine function of `R_w`. -/
theorem schur_pos_iff (ht : 0 < t) (a : ι → ℝ) (v w : ι → ℝ)
    (hw : priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t ≠ 0) :
    0 < priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t -
        priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R w) t ^ 2 /
          priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t ↔
      ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, dirLoss R (v + (-(priorCov μ π (affLoss L₀ R a) (dirLoss R v)
        (dirLoss R w) t / priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t)) • w) x =
        c := by
  rw [schur_eq_var_residual hπm hπi hπ hπpos hL₀m hL₀ hR a v w hw]
  set u := v + (-(priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R w) t /
    priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t)) • w
  have h0 := responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht a u
  have hnn := priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (bdd_dirLoss hR u)
  unfold responseForm at h0
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ ht.ne')] at h0
  constructor
  · intro hpos hc
    have := h0.2 hc
    linarith
  · intro hne
    exact lt_of_le_of_ne hnn fun h ↦ hne (h0.1 h.symm)

/-- **The constrained response**: along `a(s) = a₀ + s v + β(s) w` with `⟨R_w⟩` constant,
`d/ds ⟨R_v⟩ = −t (Var(R_v) − Cov(R_v,R_w)²/Var(R_w))`. -/
theorem constrained_response_deriv (ht : 0 < t) (a₀ v w : ι → ℝ) {β β' : ℝ → ℝ}
    (hβ : ∀ s, HasDerivAt β (β' s) s) {c : ℝ}
    (hconst : ∀ s, priorExp μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R w) t = c)
    (s : ℝ)
    (hw : priorCov μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R w) (dirLoss R w) t ≠ 0) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R v) t)
      (-t * (priorCov μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R v) (dirLoss R v) t -
        priorCov μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R v) (dirLoss R w) t ^ 2 /
          priorCov μ π (affLoss L₀ R (a₀ + s • v + β s • w)) (dirLoss R w) (dirLoss R w) t)) s := by
  set a : ℝ → ι → ℝ := fun s ↦ a₀ + s • v + β s • w with ha
  have hw' : priorCov μ π (affLoss L₀ R (a s)) (dirLoss R w) (dirLoss R w) t ≠ 0 := hw
  change HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R v) t)
    (-t * (priorCov μ π (affLoss L₀ R (a s)) (dirLoss R v) (dirLoss R v) t -
      priorCov μ π (affLoss L₀ R (a s)) (dirLoss R v) (dirLoss R w) t ^ 2 /
        priorCov μ π (affLoss L₀ R (a s)) (dirLoss R w) (dirLoss R w) t)) s
  have hpath : HasDerivAt a (v + β' s • w) s := by
    have h1 : HasDerivAt (fun s : ℝ ↦ a₀ + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add a₀
    exact h1.add ((hβ s).smul_const w)
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  obtain ⟨hwm, Mw, hwb⟩ := bdd_dirLoss hR w
  -- the derivative of the constrained response vanishes
  have hDw : HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R w) t)
      (obsMapDeriv μ π L₀ (dirLoss R w) R t (a s) (v + β' s • w)) s :=
    (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hwm hwb ht (a s)).comp_hasDerivAt s hpath
  have hzero : obsMapDeriv μ π L₀ (dirLoss R w) R t (a s) (v + β' s • w) = 0 := by
    have hc : HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R w) t) 0 s := by
      have : (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R w) t) = fun _ ↦ c :=
        funext fun s ↦ hconst s
      rw [this]; exact hasDerivAt_const s c
    exact hDw.unique hc
  rw [obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hwm hwb ht,
    priorCov_dirLoss_add_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR _ v w _ ⟨hwm, Mw, hwb⟩] at hzero
  -- `β' = −Cov(R_v,R_w)/Var(R_w)`
  have hβ' : β' s = -(priorCov μ π (affLoss L₀ R (a s)) (dirLoss R v) (dirLoss R w) t /
      priorCov μ π (affLoss L₀ R (a s)) (dirLoss R w) (dirLoss R w) t) := by
    have h1 : priorCov μ π (affLoss L₀ R (a s)) (dirLoss R v) (dirLoss R w) t +
        β' s * priorCov μ π (affLoss L₀ R (a s)) (dirLoss R w) (dirLoss R w) t = 0 := by
      rcases mul_eq_zero.1 hzero with h | h
      · exact absurd h (by linarith)
      · rw [priorCov_comm π _ (dirLoss R w) (dirLoss R v) t] at h; linarith
    field_simp
    linarith
  -- the free response
  have hDv : HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R v) t)
      (obsMapDeriv μ π L₀ (dirLoss R v) R t (a s) (v + β' s • w)) s :=
    (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht (a s)).comp_hasDerivAt s hpath
  refine hDv.congr_deriv ?_
  rw [obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hvm hvb ht,
    priorCov_dirLoss_add_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR _ v w _ ⟨hvm, Mv, hvb⟩, hβ']
  field_simp
  ring

end

end Laplace.Multi
