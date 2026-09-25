/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MeanMapInjective
import Laplace.Multi.GibbsVariational

/-!
# Entropy duality on the mean-map image

The free energy `F_t(a) = −(1/t) log Z_t(L_a)` of an affine family is concave with gradient the
mean map `m(a) = (⟨Rᵢ⟩_a)ᵢ` (`AffineConvexity`, `MeanMapInjective`). Its Legendre dual, evaluated at
a realised mean `m(a)`, is the **constrained entropy functional**

  `J_t(m(a)) = F_t(a) − a·m(a) = ⟨L₀⟩_a + (1/t) KL(P_a ‖ π)`   (`meanMap_legendre`),

by the Gibbs variational identity (`gibbs_variational_eq`), and it is the supremum of
`F_t(b) − b·m(a)` over all `b` (`affFreeEnergy_sub_dot_le`), because the concave `F_t` lies below
its tangent hyperplane (`affFreeEnergy_le_tangent`): `F_t(b) ≤ F_t(a) + (b − a)·m(a)`. Finally the
Kullback–Leibler divergence between two posteriors of the family is the Bregman divergence of the
log-partition function (`mixKL_aff_eq`):

  `KL(P_a ‖ P_b) = A(b) − A(a) + t (b − a)·m(a)`,   `A = log Z_t`.

These identities connect the affine parameters, the mean coordinates, the local response metric
(the Hessian of `A`) and global posterior distinguishability into one convex-analytic picture
(Astra, rounds 22–23).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- `⟨φ⟩_{t,L} = ∫ φ ρ_{t,L}`. -/
theorem priorExp_eq_integral_gibbsDensity (π L φ : X → ℝ) (t : ℝ) :
    priorExp μ π L φ t = ∫ x, φ x * gibbsDensity μ π L t x ∂μ := by
  unfold priorExp gibbsDensity
  rw [← MeasureTheory.integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [mul_div_assoc, mul_assoc]

/-- Additivity of the posterior expectation in the observable. -/
theorem priorExp_add_of_integrable {π L f g : X → ℝ} {t : ℝ}
    (hf : Integrable (fun x ↦ f x * Real.exp (-(t * L x)) * π x) μ)
    (hg : Integrable (fun x ↦ g x * Real.exp (-(t * L x)) * π x) μ) :
    priorExp μ π L (fun x ↦ f x + g x) t = priorExp μ π L f t + priorExp μ π L g t := by
  unfold priorExp
  rw [← add_div, ← integral_add hf hg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [add_mul]

variable [Nonempty X]

omit [Nonempty X] in
/-- **Entropy duality at a realised mean**: `F_t(a) − a·m(a) = ⟨L₀⟩_a + (1/t) KL(P_a ‖ π)`. -/
theorem meanMap_legendre {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (a : ι → ℝ) :
    affFreeEnergy μ π L₀ R t a - ∑ i, a i * meanMap μ π L₀ R t a i =
      priorExp μ π (affLoss L₀ R a) L₀ t +
        (1 / t) * relEnt μ (gibbsDensity μ π (affLoss L₀ R a) t) π := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a a t
  have hZ : 0 < priorZ μ π (affLoss L₀ R a) t := h.ν_pos
  have hZint : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ := h.ν_int
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss hL₀m hL₀ hR a
  have hρi : Integrable (gibbsDensity μ π (affLoss L₀ R a) t) μ := integrable_gibbsDensity hZint
  have hgL : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R a) t x * affLoss L₀ R a x) μ := by
    have := hρi.bdd_mul hLm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hLb x)
    exact this.congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
  have hgπ : Integrable (fun x ↦ gibbsDensity μ π (affLoss L₀ R a) t x *
      Real.log (gibbsDensity μ π (affLoss L₀ R a) t x / π x)) μ := by
    have hb : ∀ x, |-(t * affLoss L₀ R a x) - Real.log (priorZ μ π (affLoss L₀ R a) t)| ≤
        t * ML + |Real.log (priorZ μ π (affLoss L₀ R a) t)| := fun x ↦ by
      calc |-(t * affLoss L₀ R a x) - Real.log (priorZ μ π (affLoss L₀ R a) t)|
          ≤ |-(t * affLoss L₀ R a x)| + |Real.log (priorZ μ π (affLoss L₀ R a) t)| := abs_sub _ _
        _ ≤ t * ML + |Real.log (priorZ μ π (affLoss L₀ R a) t)| := by
          rw [abs_neg, abs_mul, abs_of_pos ht]
          exact add_le_add (mul_le_mul_of_nonneg_left (hLb x) ht.le) le_rfl
    have hmeas : Measurable fun x ↦ -(t * affLoss L₀ R a x) -
        Real.log (priorZ μ π (affLoss L₀ R a) t) :=
      ((hLm.const_mul t).neg).sub measurable_const
    have := hρi.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hb x)
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    by_cases hπx : π x = 0
    · simp [gibbsDensity, hπx]
    · have e : gibbsDensity μ π (affLoss L₀ R a) t x / π x =
          Real.exp (-(t * affLoss L₀ R a x)) / priorZ μ π (affLoss L₀ R a) t := by
        unfold gibbsDensity
        field_simp
      rw [e, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp, mul_comm]
  have key := gibbs_variational_eq hZ hZint hgL hgπ
  have hEL : ∫ x, gibbsDensity μ π (affLoss L₀ R a) t x * affLoss L₀ R a x ∂μ =
      priorExp μ π (affLoss L₀ R a) L₀ t + ∑ i, a i * meanMap μ π L₀ R t a i := by
    have e1 : ∫ x, gibbsDensity μ π (affLoss L₀ R a) t x * affLoss L₀ R a x ∂μ =
        priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t := by
      rw [priorExp_eq_integral_gibbsDensity]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
    have hf : Integrable (fun x ↦ L₀ x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
      (hZint.bdd_mul hL₀m.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hL₀ x)).congr
        (Filter.Eventually.of_forall fun x ↦ by ring)
    obtain ⟨ham, Ma, hab⟩ := bdd_dirLoss hR a
    have hg : Integrable (fun x ↦ dirLoss R a x * Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
      (hZint.bdd_mul ham.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hab x)).congr
        (Filter.Eventually.of_forall fun x ↦ by ring)
    have e2 := priorExp_add_of_integrable hf hg
    rw [e1, show priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ L₀ x + dirLoss R a x) t from rfl, e2,
      priorExp_dirLoss h.ν_int hR]
    rfl
  rw [hEL] at key
  unfold affFreeEnergy affLogZ
  have hlog : Real.log (priorZ μ π (affLoss L₀ R a) t) =
      -(t * (priorExp μ π (affLoss L₀ R a) L₀ t + ∑ i, a i * meanMap μ π L₀ R t a i) +
        relEnt μ (gibbsDensity μ π (affLoss L₀ R a) t) π) := by linarith
  rw [hlog]
  field_simp
  ring

omit [Nonempty X] in
/-- The mean of the contrast `R_{b−a}` at `a` is `(b − a)·m(a)`. -/
theorem mixExp_zero_eq_dot {π L₀ : X → ℝ} {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
    (a b : ι → ℝ) (hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ) :
    mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 0 =
      ∑ i, (b i - a i) * meanMap μ π L₀ R t a i := by
  unfold mixExp
  rw [show pathLoss (affLoss L₀ R a) (dirLoss R (b - a)) 0 = affLoss L₀ R a from
    funext fun x ↦ by simp [pathLoss], priorExp_dirLoss hν hR]
  rfl

/-- **The concave free energy lies below its tangent hyperplane**:
`F_t(b) ≤ F_t(a) + (b − a)·m(a)`. -/
theorem affFreeEnergy_le_tangent {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (a b : ι → ℝ) :
    affFreeEnergy μ π L₀ R t b ≤
      affFreeEnergy μ π L₀ R t a + ∑ i, (b i - a i) * meanMap μ π L₀ R t a i := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a (b - a) t
  have hΔ : Bdd (dirLoss R (b - a)) := bdd_dirLoss hR (b - a)
  have hd : ∀ s, HasDerivAt (fun s ↦ mixLogZ μ π (affLoss L₀ R a) (dirLoss R (b - a)) t s)
      (-t * mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t s) s :=
    fun s ↦ h.hasDerivAt_mixLogZ s
  have hcont : Continuous fun s ↦
      -t * mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t s :=
    continuous_iff_continuousAt.mpr fun s ↦ (h.hasDerivAt_mixExp hΔ s).continuousAt.const_mul _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s _ ↦ hd s) (hcont.intervalIntegrable (μ := volume) 0 1)
  have hmono : ∀ s ∈ Icc (0 : ℝ) 1,
      -t * mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t 0 ≤
      -t * mixExp μ π (affLoss L₀ R a) (dirLoss R (b - a)) (dirLoss R (b - a)) t s := fun s hs ↦ by
    have := h.mixExp_antitone ht.le hs.1
    nlinarith
  have hge := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
    (hcont.intervalIntegrable (μ := volume) 0 1) hmono
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hge
  rw [hftc] at hge
  simp only [affLogZ_line, zero_smul, add_zero, one_smul, add_sub_cancel] at hge
  rw [mixExp_zero_eq_dot hR a b h.ν_int] at hge
  unfold affFreeEnergy
  have hinv : 0 < 1 / t := by positivity
  have := mul_le_mul_of_nonneg_left hge hinv.le
  rw [← mul_assoc, show 1 / t * -t = -1 by field_simp] at this
  linarith

/-- **Legendre duality at a realised mean**: the supremum of `F_t(b) − b·m(a)` is attained at
`b = a`. -/
theorem affFreeEnergy_sub_dot_le {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
    (a b : ι → ℝ) :
    affFreeEnergy μ π L₀ R t b - ∑ i, b i * meanMap μ π L₀ R t a i ≤
      affFreeEnergy μ π L₀ R t a - ∑ i, a i * meanMap μ π L₀ R t a i := by
  have := affFreeEnergy_le_tangent hπm hπi hπ hπpos hL₀m hL₀ hR ht a b
  have e : ∑ i, (b i - a i) * meanMap μ π L₀ R t a i =
      ∑ i, b i * meanMap μ π L₀ R t a i - ∑ i, a i * meanMap μ π L₀ R t a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  linarith

/-- **KL is the Bregman divergence of the log-partition function**:
`KL(P_a ‖ P_b) = A(b) − A(a) + t (b − a)·m(a)`. -/
theorem mixKL_aff_eq {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) (a b : ι → ℝ) :
    mixKL μ π (affLoss L₀ R a) (dirLoss R (b - a)) t 0 1 =
      affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a +
        t * ∑ i, (b i - a i) * meanMap μ π L₀ R t a i := by
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a (b - a) t
  rw [h.mixKL_eq hπ 0 1, mixExp_zero_eq_dot hR a b h.ν_int]
  simp only [affLogZ_line, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero]
  ring

end Laplace.Multi
