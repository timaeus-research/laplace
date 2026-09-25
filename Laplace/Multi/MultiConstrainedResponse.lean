/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ConstrainedResponse

/-!
# Constrained responses with several constraints: the regression residual

Move the data in the direction `v` while adjusting a family of directions `w k` so that all the
responses `⟨R_{w k}⟩` stay constant. For any bounded observable `φ`,

  `d/ds ⟨φ⟩ = −t (Cov(φ, R_v) − ∑ₖ bₖ Cov(φ, R_{w k}))`,   `C b = c`
  (`multi_constrained_response_deriv`),

where `C = (Cov(R_{w k}, R_{w l}))` is the covariance matrix of the constrained statistics and
`c = (Cov(R_{w k}, R_v))`: only the part of `R_v` orthogonal to the constrained statistics drives
the response. For `φ = R_v` the rate is minus the variance of the regression residual
`R_v − ∑ bₖ R_{w k}` (`residual_var`, `multi_constrained_response_deriv_self`), which vanishes iff
`R_v` is a.e. an affine function of the `R_{w k}` (`residual_var_eq_zero_iff`). The covariance
matrix is invertible whenever the `w k` are linearly independent and the family is nondegenerate
(`covMat_mulVec_injective`). Nothing here depends on which family the path lives in beyond the
fixed-temperature response rule `d/ds⟨φ⟩ = −t Cov(φ, R_{ȧ})`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
  {κ : Type*} [Fintype κ]

theorem Bdd.sub {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun x ↦ f x - g x := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  obtain ⟨hgm, Mg, hMg⟩ := hg
  exact ⟨hfm.sub hgm, Mf + Mg, fun x ↦ (abs_sub _ _).trans (add_le_add (hMf x) (hMg x))⟩

section Bilinear

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
theorem priorCov_dirLoss_add_left (a v u : ι → ℝ) {ψ : X → ℝ} (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) (dirLoss R (v + u)) ψ t =
      priorCov μ π (affLoss L₀ R a) (dirLoss R v) ψ t +
        priorCov μ π (affLoss L₀ R a) (dirLoss R u) ψ t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  rw [← sum_mul_priorCov_eq hν hR hψ, ← sum_mul_priorCov_eq hν hR hψ,
    ← sum_mul_priorCov_eq hν hR hψ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.add_apply]; ring

omit [Nonempty X] in
theorem priorCov_dirLoss_add_right (a v u : ι → ℝ) {ψ : X → ℝ} (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) ψ (dirLoss R (v + u)) t =
      priorCov μ π (affLoss L₀ R a) ψ (dirLoss R v) t +
        priorCov μ π (affLoss L₀ R a) ψ (dirLoss R u) t := by
  rw [priorCov_comm π _ ψ _ t, priorCov_dirLoss_add_left hπm hπi hπ hπpos hL₀m hL₀ hR a v u hψ,
    priorCov_comm π _ (dirLoss R v) ψ t, priorCov_comm π _ (dirLoss R u) ψ t]

omit [Nonempty X] in
/-- Left-slot linearity over a finite combination of directions. -/
theorem priorCov_dirLoss_sum_smul_left (a : ι → ℝ) (c : κ → ℝ) (w : κ → ι → ℝ) {ψ : X → ℝ}
    (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) (dirLoss R (∑ k, c k • w k)) ψ t =
      ∑ k, c k * priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) ψ t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have e : ∀ k, priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) ψ t =
      ∑ i, w k i * priorCov μ π (affLoss L₀ R a) (R i) ψ t :=
    fun k ↦ (sum_mul_priorCov_eq hν hR hψ (w k)).symm
  simp only [e]
  rw [← sum_mul_priorCov_eq hν hR hψ]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

omit [Nonempty X] in
/-- Right-slot linearity over a finite combination of directions. -/
theorem priorCov_dirLoss_sum_smul_right (a : ι → ℝ) (c : κ → ℝ) (w : κ → ι → ℝ) {ψ : X → ℝ}
    (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) ψ (dirLoss R (∑ k, c k • w k)) t =
      ∑ k, c k * priorCov μ π (affLoss L₀ R a) ψ (dirLoss R (w k)) t := by
  rw [priorCov_comm π _ ψ _ t, priorCov_dirLoss_sum_smul_left hπm hπi hπ hπpos hL₀m hL₀ hR a c w hψ]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [priorCov_comm π _ (dirLoss R (w k)) ψ t]

theorem priorCov_sub_left (a : ι → ℝ) {f g ψ : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) (fun x ↦ f x - g x) ψ t =
      priorCov μ π (affLoss L₀ R a) f ψ t - priorCov μ π (affLoss L₀ R a) g ψ t := by
  have h1 : Integrable (fun x ↦ f x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hf
  have h2 : Integrable (fun x ↦ g x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hg
  have h3 : Integrable (fun x ↦ f x * ψ x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hf.mul hψ)
  have h4 : Integrable (fun x ↦ g x * ψ x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hg.mul hψ)
  have e1 : (∫ x, (f x - g x) * ψ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) =
      (∫ x, f x * ψ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) -
        ∫ x, g x * ψ x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ := by
    rw [← integral_sub h3 h4]
    congr 1; funext x; ring
  have e2 : (∫ x, (f x - g x) * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) =
      (∫ x, f x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) -
        ∫ x, g x * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ := by
    rw [← integral_sub h1 h2]
    congr 1; funext x; ring
  simp only [priorCov, priorExp]
  rw [e1, e2]
  ring

theorem priorCov_sub_right (a : ι → ℝ) {f g ψ : X → ℝ} (hf : Bdd f) (hg : Bdd g) (hψ : Bdd ψ) :
    priorCov μ π (affLoss L₀ R a) ψ (fun x ↦ f x - g x) t =
      priorCov μ π (affLoss L₀ R a) ψ f t - priorCov μ π (affLoss L₀ R a) ψ g t := by
  rw [priorCov_comm π _ ψ _ t, priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a hf hg hψ,
    priorCov_comm π _ f ψ t, priorCov_comm π _ g ψ t]

end Bilinear

/-- The covariance matrix of the constrained statistics `R_{w k}` under `P_a`. -/
noncomputable def covMat (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)
    (w : κ → ι → ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun k l ↦ priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) (dirLoss R (w l)) t

/-- The covariances `Cov(R_{w k}, φ)` of the constrained statistics with an observable. -/
noncomputable def covVec (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ)
    (w : κ → ι → ℝ) (φ : X → ℝ) : κ → ℝ :=
  fun k ↦ priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t

section Residual

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
/-- The quadratic form of the covariance matrix is the variance of the combined statistic. -/
theorem dotProduct_covMat_mulVec (a : ι → ℝ) (w : κ → ι → ℝ) (u : κ → ℝ) :
    dotProduct u ((covMat μ π L₀ R t a w).mulVec u) =
      priorCov μ π (affLoss L₀ R a) (dirLoss R (∑ k, u k • w k))
        (dirLoss R (∑ k, u k • w k)) t := by
  rw [priorCov_dirLoss_sum_smul_left hπm hπi hπ hπpos hL₀m hL₀ hR a u w (bdd_dirLoss hR _)]
  simp only [dotProduct, Matrix.mulVec, covMat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [priorCov_dirLoss_sum_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR a u w (bdd_dirLoss hR (w k))]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by ring

/-- **The regression residual**: if `C b = c` then
`Var(φ − ∑ₖ bₖ R_{w k}) = Var φ − ∑ₖ bₖ Cov(R_{w k}, φ)`. -/
theorem residual_var (a : ι → ℝ) (w : κ → ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) (b : κ → ℝ)
    (hb : (covMat μ π L₀ R t a w).mulVec b = covVec μ π L₀ R t a w φ) :
    priorCov μ π (affLoss L₀ R a) (fun x ↦ φ x - dirLoss R (∑ k, b k • w k) x)
        (fun x ↦ φ x - dirLoss R (∑ k, b k • w k) x) t =
      priorCov μ π (affLoss L₀ R a) φ φ t -
        ∑ k, b k * priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t := by
  have hu := bdd_dirLoss hR (∑ k, b k • w k)
  rw [priorCov_sub_left hπm hπi hπ hπpos hL₀m hL₀ hR a hφ hu (hφ.sub hu),
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a hφ hu hφ,
    priorCov_sub_right hπm hπi hπ hπpos hL₀m hL₀ hR a hφ hu hu,
    priorCov_dirLoss_sum_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR a b w hφ,
    priorCov_dirLoss_sum_smul_left hπm hπi hπ hπpos hL₀m hL₀ hR a b w hφ,
    priorCov_dirLoss_sum_smul_left hπm hπi hπ hπpos hL₀m hL₀ hR a b w hu]
  have hk : ∀ k, priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) (dirLoss R (∑ l, b l • w l)) t =
      priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t := by
    intro k
    rw [priorCov_dirLoss_sum_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR a b w (bdd_dirLoss hR (w k))]
    have := congrFun hb k
    simp only [Matrix.mulVec, dotProduct, covMat, Matrix.of_apply, covVec] at this
    rw [← this]
    exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
  simp only [hk]
  have e : ∀ k, priorCov μ π (affLoss L₀ R a) φ (dirLoss R (w k)) t =
      priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t := fun k ↦ priorCov_comm π _ φ _ t
  simp only [e]
  ring

theorem residual_var_nonneg (a : ι → ℝ) (w : κ → ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) (b : κ → ℝ)
    (hb : (covMat μ π L₀ R t a w).mulVec b = covVec μ π L₀ R t a w φ) :
    0 ≤ priorCov μ π (affLoss L₀ R a) φ φ t -
        ∑ k, b k * priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t := by
  rw [← residual_var hπm hπi hπ hπpos hL₀m hL₀ hR a w hφ b hb]
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
    (hφ.sub (bdd_dirLoss hR _))

/-- The residual variance vanishes iff `φ` is a.e. an affine function of the constrained
statistics. -/
theorem residual_var_eq_zero_iff (a : ι → ℝ) (w : κ → ι → ℝ) {φ : X → ℝ}
    (hφ : Bdd φ) (b : κ → ℝ)
    (hb : (covMat μ π L₀ R t a w).mulVec b = covVec μ π L₀ R t a w φ) :
    priorCov μ π (affLoss L₀ R a) φ φ t -
        ∑ k, b k * priorCov μ π (affLoss L₀ R a) (dirLoss R (w k)) φ t = 0 ↔
      ∃ c : ℝ, ∀ᵐ x ∂μ, φ x - dirLoss R (∑ k, b k • w k) x = c := by
  rw [← residual_var hπm hπi hπ hπpos hL₀m hL₀ hR a w hφ b hb]
  have hres : Bdd fun x ↦ φ x - dirLoss R (∑ k, b k • w k) x := hφ.sub (bdd_dirLoss hR _)
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  constructor
  · intro h
    have h0 : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
      (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
        (Bdd.const 1)).congr (Eventually.of_forall fun x ↦ by simp)
    exact ⟨_, ae_eq_const_of_priorCov_self_eq_zero hπ hZ h0
      (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hres)
      (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hres.mul hres)) h⟩
  · rintro ⟨c, hc⟩
    exact priorCov_self_eq_zero_of_ae_const hZ hc

/-- **Invertibility of the constrained covariance**: under nondegeneracy, the covariance matrix of
linearly independent contrast directions is injective. -/
theorem covMat_mulVec_injective (ht : 0 < t)
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (a : ι → ℝ) (w : κ → ι → ℝ) (hw : LinearIndependent ℝ w) :
    Function.Injective (covMat μ π L₀ R t a w).mulVec := by
  intro u₁ u₂ h
  have h0 : (covMat μ π L₀ R t a w).mulVec (u₁ - u₂) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hq : priorCov μ π (affLoss L₀ R a) (dirLoss R (∑ k, (u₁ - u₂) k • w k))
      (dirLoss R (∑ k, (u₁ - u₂) k • w k)) t = 0 := by
    rw [← dotProduct_covMat_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR a w (u₁ - u₂), h0,
      dotProduct_zero]
  have hform : responseForm μ π L₀ R a t (∑ k, (u₁ - u₂) k • w k) (∑ k, (u₁ - u₂) k • w k) = 0 := by
    unfold responseForm
    rw [hq, mul_zero]
  obtain ⟨c, hc⟩ := (responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht a _).1 hform
  have hsum : ∑ k, (u₁ - u₂) k • w k = 0 := by
    by_contra hne
    exact hnd _ hne ⟨c, hc.mono fun x hx _ ↦ hx⟩
  have := Fintype.linearIndependent_iff.1 hw (u₁ - u₂) hsum
  exact sub_eq_zero.1 (funext this)

end Residual

section Path

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The multi-constrained response, path form**: along a differentiable path whose velocity at `s`
is `v + ∑ₖ γₖ w k` and along which every `⟨R_{w k}⟩` is locally constant, if `C b = c` with `C`
injective then `d/ds ⟨φ⟩ = −t (Cov(φ, R_v) − ∑ₖ bₖ Cov(φ, R_{w k}))`. -/
theorem multi_constrained_response_deriv_path (a : ℝ → ι → ℝ) (v : ι → ℝ) (w : κ → ι → ℝ)
    (γ : κ → ℝ) (s : ℝ) (hpath : HasDerivAt a (v + ∑ k, γ k • w k) s) {c : κ → ℝ}
    (hconst : ∀ k, ∀ᶠ s' in 𝓝 s, priorExp μ π (affLoss L₀ R (a s')) (dirLoss R (w k)) t = c k)
    {b : κ → ℝ}
    (hb : (covMat μ π L₀ R t (a s) w).mulVec b = covVec μ π L₀ R t (a s) w (dirLoss R v))
    (hinj : Function.Injective (covMat μ π L₀ R t (a s) w).mulVec)
    {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) φ t)
      (-t * (priorCov μ π (affLoss L₀ R (a s)) φ (dirLoss R v) t -
        ∑ k, b k * priorCov μ π (affLoss L₀ R (a s)) φ (dirLoss R (w k)) t)) s := by
  -- the response rule along the path, for any bounded observable
  have hD : ∀ {ψ : X → ℝ}, Bdd ψ → HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) ψ t)
      (-t * (priorCov μ π (affLoss L₀ R (a s)) ψ (dirLoss R v) t +
        ∑ k, γ k * priorCov μ π (affLoss L₀ R (a s)) ψ (dirLoss R (w k)) t)) s := by
    intro ψ hψ
    obtain ⟨hψm, Mψ, hψb⟩ := hψ
    have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hψm hψb ht (a s)).comp_hasDerivAt
      s hpath
    refine h.congr_deriv ?_
    rw [obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hψm hψb ht,
      priorCov_dirLoss_add_right hπm hπi hπ hπpos hL₀m hL₀ hR _ v _ ⟨hψm, Mψ, hψb⟩,
      priorCov_dirLoss_sum_smul_right hπm hπi hπ hπpos hL₀m hL₀ hR _ _ w ⟨hψm, Mψ, hψb⟩]
  -- the constraints force `C γ = −c`
  have hzero : ∀ k, priorCov μ π (affLoss L₀ R (a s)) (dirLoss R (w k)) (dirLoss R v) t +
      ∑ l, γ l * priorCov μ π (affLoss L₀ R (a s)) (dirLoss R (w k)) (dirLoss R (w l)) t =
        0 := by
    intro k
    have h1 := hD (bdd_dirLoss hR (w k))
    have h2 : HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a s)) (dirLoss R (w k)) t) 0 s :=
      (hasDerivAt_const s (c k)).congr_of_eventuallyEq ((hconst k).mono fun s' h ↦ h)
    rcases mul_eq_zero.1 (h1.unique h2) with h | h
    · exact absurd h (by linarith)
    · exact h
  have hγ : γ = -b := by
    apply hinj
    rw [Matrix.mulVec_neg, hb]
    funext k
    simp only [Matrix.mulVec, dotProduct, covMat, Matrix.of_apply, covVec, Pi.neg_apply]
    have e : ∑ l, priorCov μ π (affLoss L₀ R (a s)) (dirLoss R (w k)) (dirLoss R (w l)) t *
        γ l = ∑ l, γ l * priorCov μ π (affLoss L₀ R (a s)) (dirLoss R (w k))
          (dirLoss R (w l)) t := Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
    rw [e]
    linarith [hzero k]
  refine (hD hφ).congr_deriv ?_
  rw [hγ]
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **The multi-constrained response**: along `a(s) = a₀ + s v + ∑ₖ βₖ(s) w k` with every
`⟨R_{w k}⟩` constant, and `C b = c` with `C` injective,
`d/ds ⟨φ⟩ = −t (Cov(φ, R_v) − ∑ₖ bₖ Cov(φ, R_{w k}))`. -/
theorem multi_constrained_response_deriv (a₀ v : ι → ℝ) (w : κ → ι → ℝ) {β β' : ℝ → κ → ℝ}
    (hβ : ∀ s k, HasDerivAt (fun s ↦ β s k) (β' s k) s) {c : κ → ℝ}
    (hconst : ∀ s k, priorExp μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k))
      (dirLoss R (w k)) t = c k)
    (s : ℝ) {b : κ → ℝ}
    (hb : (covMat μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w).mulVec b =
      covVec μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w (dirLoss R v))
    (hinj : Function.Injective (covMat μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w).mulVec)
    {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k)) φ t)
      (-t * (priorCov μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k)) φ (dirLoss R v) t -
        ∑ k, b k * priorCov μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k)) φ
          (dirLoss R (w k)) t)) s := by
  have hpath : HasDerivAt (fun s : ℝ ↦ a₀ + s • v + ∑ k, β s k • w k)
      (v + ∑ k, β' s k • w k) s := by
    have h1 : HasDerivAt (fun s : ℝ ↦ a₀ + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add a₀
    have h2 : HasDerivAt (fun s : ℝ ↦ ∑ k, β s k • w k) (∑ k, β' s k • w k) s :=
      HasDerivAt.fun_sum fun k _ ↦ (hβ s k).smul_const (w k)
    exact h1.add h2
  exact multi_constrained_response_deriv_path hπm hπi hπ hπpos hL₀m hL₀ hR ht
    (fun s ↦ a₀ + s • v + ∑ k, β s k • w k) v w (β' s) s hpath
    (fun k ↦ Eventually.of_forall fun s' ↦ hconst s' k) hb hinj hφ

/-- For `φ = R_v` the constrained response rate is minus the residual variance. -/
theorem multi_constrained_response_deriv_self (a₀ v : ι → ℝ) (w : κ → ι → ℝ)
    {β β' : ℝ → κ → ℝ} (hβ : ∀ s k, HasDerivAt (fun s ↦ β s k) (β' s k) s) {c : κ → ℝ}
    (hconst : ∀ s k, priorExp μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k))
      (dirLoss R (w k)) t = c k)
    (s : ℝ) {b : κ → ℝ}
    (hb : (covMat μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w).mulVec b =
      covVec μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w (dirLoss R v))
    (hinj : Function.Injective (covMat μ π L₀ R t (a₀ + s • v + ∑ k, β s k • w k) w).mulVec) :
    HasDerivAt (fun s ↦ priorExp μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k))
        (dirLoss R v) t)
      (-t * priorCov μ π (affLoss L₀ R (a₀ + s • v + ∑ k, β s k • w k))
        (fun x ↦ dirLoss R v x - dirLoss R (∑ k, b k • w k) x)
        (fun x ↦ dirLoss R v x - dirLoss R (∑ k, b k • w k) x) t) s := by
  refine (multi_constrained_response_deriv hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ v w hβ hconst s hb
    hinj (bdd_dirLoss hR v)).congr_deriv ?_
  rw [residual_var hπm hπi hπ hπpos hL₀m hL₀ hR _ w (bdd_dirLoss hR v) b hb]
  congr 2
  exact Finset.sum_congr rfl fun k _ ↦ by rw [priorCov_comm π _ (dirLoss R v) _ t]

end Path

end Laplace.Multi
