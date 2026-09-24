/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianMomentsPosDef
import Laplace.Multi.OrthantSplit

/-!
# The two-scaled tied-truth integral on the positive quadrant

Two scaled coordinates `y = (y₀, y₁)` on `(0,∞)²`, a phase monomial `c ∏ y^κ` and a cutoff
`h < Q·log y` (the tied truth constraint in logarithmic form). If the density exponents satisfy
the dual decomposition `a = η κ − θ Q` with `η, θ > 0` and `Δ = κ₀Q₁ − κ₁Q₀ ≠ 0`, the substitution
`y = e^v` followed by the linear change `(w, h) = (κ·v, Q·v)` factors the integral completely:

`∫_{y > 0, h < Q·log y} ∏ y^{a−1} e^{−c ∏ y^κ} dy = Γ(η) c^{−η} · e^{−θh}/θ · 1/|Δ|`

(`integral_twoScaledInner`, with the integrability `integrable_twoScaledInner`). The two
constraints — the exponential monomial and the cutoff — isolate the two scaled directions; this
is Astra's two-constraint certificate for tied-truth optima (`research_partial_v1.md`, §(b)).
-/

open Real MeasureTheory Set Filter Topology
open scoped Matrix

namespace Laplace.Multi

section OneDim

/-- The substitution `y = e^v` on the whole line. -/
theorem integral_comp_exp_univ (g : ℝ → ℝ) : ∫ v, exp v * g (exp v) = ∫ y in Ioi 0, g y := by
  rw [← Real.range_exp, ← Set.image_univ, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g,
    Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  simp [abs_of_pos (exp_pos v)]

theorem integrable_comp_exp_univ_iff (g : ℝ → ℝ) :
    Integrable (fun v ↦ exp v * g (exp v)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← Real.range_exp, ← Set.image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g,
    IntegrableOn, Measure.restrict_univ]
  refine integrable_congr (Eventually.of_forall fun v ↦ ?_)
  simp [abs_of_pos (exp_pos v)]

theorem exp_mul_exp_neg_exp_eq (η c v : ℝ) :
    exp (η * v) * exp (-(c * exp v)) = exp v * (exp v ^ (η - 1) * exp (-c * exp v)) := by
  rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- `∫_ℝ e^{ηv} e^{−c e^v} dv = Γ(η) c^{−η}`. -/
theorem integral_exp_mul_exp_neg_exp {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∫ v : ℝ, exp (η * v) * exp (-(c * exp v)) = Gamma η * c ^ (-η) := by
  have h1 := integral_comp_exp_univ (fun y ↦ y ^ (η - 1) * exp (-c * y))
  rw [show (fun v : ℝ ↦ exp (η * v) * exp (-(c * exp v))) =
    fun v ↦ exp v * (exp v ^ (η - 1) * exp (-c * exp v)) from funext fun v ↦
      exp_mul_exp_neg_exp_eq η c v, h1]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := η - 1) (b := c) one_pos
    (by linarith) hc
  simp only [Real.rpow_one, sub_add_cancel, div_one, mul_one] at this
  rw [this, mul_comm]

theorem integrable_exp_mul_exp_neg_exp {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    Integrable fun v : ℝ ↦ exp (η * v) * exp (-(c * exp v)) := by
  have h1 := integrable_comp_exp_univ_iff (fun y ↦ y ^ (η - 1) * exp (-c * y))
  rw [show (fun v : ℝ ↦ exp (η * v) * exp (-(c * exp v))) =
    fun v ↦ exp v * (exp v ^ (η - 1) * exp (-c * exp v)) from funext fun v ↦
      exp_mul_exp_neg_exp_eq η c v, h1]
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := η - 1) (b := c)
    (by linarith) one_pos hc
  simpa only [Real.rpow_one] using this

/-- `∫_{x > h} e^{−θx} dx = e^{−θh}/θ`. -/
theorem integral_exp_neg_mul_Ioi {θ : ℝ} (hθ : 0 < θ) (h : ℝ) :
    ∫ x in Ioi h, exp (-(θ * x)) = exp (-(θ * h)) / θ := by
  have := integral_comp_mul_left_Ioi (fun x ↦ exp (-x)) h hθ
  simp only [smul_eq_mul] at this
  rw [this, integral_exp_neg_Ioi, div_eq_inv_mul]

theorem integrableOn_exp_neg_mul_Ioi' {θ : ℝ} (hθ : 0 < θ) (h : ℝ) :
    IntegrableOn (fun x ↦ exp (-(θ * x))) (Ioi h) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi h hθ

end OneDim

section ExpMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of the coordinatewise exponential `v ↦ e^v`. -/
noncomputable def expDeriv (v : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal fun i ↦ exp (v i)))

theorem hasFDerivAt_expMap (v : ι → ℝ) :
    HasFDerivAt (fun w : ι → ℝ ↦ fun i ↦ exp (w i)) (expDeriv v) v := by
  refine hasFDerivAt_pi'.mpr fun i ↦ ?_
  refine ((hasFDerivAt_apply (𝕜 := ℝ) i v).exp).congr_fderiv ?_
  ext w
  simp [expDeriv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem det_expDeriv (v : ι → ℝ) : (expDeriv v).det = ∏ i, exp (v i) := by
  rw [ContinuousLinearMap.det, expDeriv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_diagonal]

omit [Fintype ι] [DecidableEq ι] in
theorem expMap_injective : Function.Injective (fun w : ι → ℝ ↦ fun i ↦ exp (w i)) := by
  intro w w' h
  funext i
  exact exp_injective (congrFun h i)

omit [Fintype ι] [DecidableEq ι] in
theorem range_expMap :
    Set.range (fun w : ι → ℝ ↦ fun i ↦ exp (w i)) = Set.pi univ fun _ ↦ Ioi (0 : ℝ) := by
  ext y
  simp only [Set.mem_range, Set.mem_univ_pi, mem_Ioi]
  constructor
  · rintro ⟨w, rfl⟩ i
    exact exp_pos _
  · intro hy
    exact ⟨fun i ↦ log (y i), funext fun i ↦ exp_log (hy i)⟩

omit [DecidableEq ι] in
/-- The coordinatewise substitution `y = e^v` on the positive orthant. -/
theorem integral_posOrthant_comp_exp (g : (ι → ℝ) → ℝ) :
    ∫ y in Set.pi univ (fun _ : ι ↦ Ioi (0 : ℝ)), g y =
      ∫ v : ι → ℝ, (∏ i, exp (v i)) * g (fun i ↦ exp (v i)) := by
  classical
  rw [← range_expMap, ← Set.image_univ, integral_image_eq_integral_abs_det_fderiv_smul volume
    MeasurableSet.univ (fun v _ ↦ (hasFDerivAt_expMap v).hasFDerivWithinAt)
    expMap_injective.injOn g, Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  simp only [det_expDeriv, smul_eq_mul]
  rw [abs_of_pos (Finset.prod_pos fun i _ ↦ exp_pos _)]

omit [DecidableEq ι] in
theorem integrableOn_posOrthant_comp_exp_iff (g : (ι → ℝ) → ℝ) :
    IntegrableOn g (Set.pi univ (fun _ : ι ↦ Ioi (0 : ℝ))) ↔
      Integrable fun v : ι → ℝ ↦ (∏ i, exp (v i)) * g (fun i ↦ exp (v i)) := by
  classical
  rw [← range_expMap, ← Set.image_univ, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume MeasurableSet.univ (fun v _ ↦ (hasFDerivAt_expMap v).hasFDerivWithinAt)
    expMap_injective.injOn g, IntegrableOn, Measure.restrict_univ]
  refine integrable_congr (Eventually.of_forall fun v ↦ ?_)
  simp only [det_expDeriv, smul_eq_mul]
  rw [abs_of_pos (Finset.prod_pos fun i _ ↦ exp_pos _)]

end ExpMap

section FinTwo

theorem integral_fin_two_mul (f g : ℝ → ℝ) :
    ∫ x : Fin 2 → ℝ, f (x 0) * g (x 1) = (∫ y, f y) * ∫ y, g y := by
  have := integral_fintype_prod_volume_eq_prod (fun i : Fin 2 ↦ (![f, g] : Fin 2 → ℝ → ℝ) i)
  simpa [Fin.prod_univ_two] using this

theorem integrable_fin_two_mul {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable fun x : Fin 2 → ℝ ↦ f (x 0) * g (x 1) := by
  have := Integrable.fintype_prod (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
    (f := fun i : Fin 2 ↦ (![f, g] : Fin 2 → ℝ → ℝ) i) (fun i ↦ by fin_cases i <;> simpa)
  rw [volume_pi]
  simpa [Fin.prod_univ_two] using this

/-- The two-constraint matrix `[κ; Q]`. -/
def twoMat (κS QS : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![κS, QS]

theorem twoMat_mulVec_zero (κS QS v : Fin 2 → ℝ) :
    (twoMat κS QS *ᵥ v) 0 = ∑ i, κS i * v i := by
  simp [twoMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem twoMat_mulVec_one (κS QS v : Fin 2 → ℝ) :
    (twoMat κS QS *ᵥ v) 1 = ∑ i, QS i * v i := by
  simp [twoMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_twoMat (κS QS : Fin 2 → ℝ) :
    (twoMat κS QS).det = κS 0 * QS 1 - κS 1 * QS 0 := by
  rw [Matrix.det_fin_two]
  simp [twoMat]

end FinTwo

section Inner

/-- The two-scaled tied-truth integrand on the positive quadrant: cut `h < Q·log y`, density
`∏ y^{a−1} e^{−c ∏ y^κ}`. -/
noncomputable def twoScaledInner (κS QS aS : Fin 2 → ℝ) (c h : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  (Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ)).indicator
    (fun y ↦ {y : Fin 2 → ℝ | h < ∑ i, QS i * log (y i)}.indicator
      (fun y ↦ (∏ i, y i ^ (aS i - 1)) * exp (-(c * ∏ i, y i ^ κS i))) y) y

/-- The factorised integrand in the coordinates `(w, s) = (κ·v, Q·v)`. -/
noncomputable def twoScaledSplit (η θ c h : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (exp (η * x 0) * exp (-(c * exp (x 0)))) * (Ioi h).indicator (fun s ↦ exp (-(θ * s))) (x 1)

theorem measurable_twoScaledSplit (η θ c h : ℝ) : Measurable (twoScaledSplit η θ c h) := by
  unfold twoScaledSplit
  have h0 : Measurable fun x : Fin 2 → ℝ ↦ x 0 := measurable_pi_apply 0
  have h1 : Measurable fun x : Fin 2 → ℝ ↦ x 1 := measurable_pi_apply 1
  refine Measurable.mul ?_ ?_
  · exact (h0.const_mul η).exp.mul (((h0.exp.const_mul c).neg).exp)
  · exact (Measurable.indicator (by fun_prop) measurableSet_Ioi).comp h1

theorem twoScaledInner_comp_exp {κS QS aS : Fin 2 → ℝ} {η θ : ℝ}
    (haS : ∀ i, aS i = η * κS i - θ * QS i) (c h : ℝ) (v : Fin 2 → ℝ) :
    (∏ i, exp (v i)) * twoScaledInner κS QS aS c h (fun i ↦ exp (v i)) =
      twoScaledSplit η θ c h (twoMat κS QS *ᵥ v) := by
  unfold twoScaledInner twoScaledSplit
  rw [twoMat_mulVec_zero, twoMat_mulVec_one,
    Set.indicator_of_mem (show (fun i ↦ exp (v i)) ∈ Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ) from
      Set.mem_univ_pi.mpr fun i ↦ exp_pos _)]
  have hmem : (fun i ↦ exp (v i)) ∈ {y : Fin 2 → ℝ | h < ∑ i, QS i * log (y i)} ↔
      h < ∑ i, QS i * v i := by
    simp only [Set.mem_ofPred_eq, log_exp]
  by_cases hcut : h < ∑ i, QS i * v i
  · rw [Set.indicator_of_mem (hmem.mpr hcut),
      Set.indicator_of_mem (show ∑ i, QS i * v i ∈ Ioi h from hcut)]
    have e1 : ∀ e : Fin 2 → ℝ, ∏ i, exp (v i) ^ e i = exp (∑ i, e i * v i) := fun e ↦ by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [← Real.exp_mul, mul_comm]
    rw [e1, e1, ← Real.exp_sum]
    have e2 : ∑ i, (aS i - 1) * v i = η * ∑ i, κS i * v i - θ * ∑ i, QS i * v i - ∑ i, v i := by
      simp only [Fin.sum_univ_two, haS]
      ring
    rw [e2]
    have e3 : exp (∑ i, v i) * (exp (η * ∑ i, κS i * v i - θ * ∑ i, QS i * v i - ∑ i, v i) *
        exp (-(c * exp (∑ i, κS i * v i)))) =
        exp (η * ∑ i, κS i * v i) * exp (-(c * exp (∑ i, κS i * v i))) *
          exp (-(θ * ∑ i, QS i * v i)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    exact e3
  · rw [Set.indicator_of_notMem (fun h' ↦ hcut (hmem.mp h')),
      Set.indicator_of_notMem (show ∑ i, QS i * v i ∉ Ioi h from hcut), mul_zero, mul_zero]

theorem twoScaledInner_eq_zero_of_notMem {κS QS aS : Fin 2 → ℝ} {c h : ℝ} {y : Fin 2 → ℝ}
    (hy : y ∉ Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ)) : twoScaledInner κS QS aS c h y = 0 :=
  Set.indicator_of_notMem hy _

theorem integral_twoScaledSplit {η θ c : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hc : 0 < c) (h : ℝ) :
    ∫ x, twoScaledSplit η θ c h x = Gamma η * c ^ (-η) * (exp (-(θ * h)) / θ) := by
  unfold twoScaledSplit
  refine (integral_fin_two_mul (fun w ↦ exp (η * w) * exp (-(c * exp w)))
    (fun s ↦ (Ioi h).indicator (fun s ↦ exp (-(θ * s))) s)).trans ?_
  rw [integral_exp_mul_exp_neg_exp hη hc, integral_indicator measurableSet_Ioi,
    integral_exp_neg_mul_Ioi hθ]

theorem integrable_twoScaledSplit {η θ c : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hc : 0 < c) (h : ℝ) :
    Integrable (twoScaledSplit η θ c h) := by
  unfold twoScaledSplit
  have h2 : Integrable fun s ↦ (Ioi h).indicator (fun s ↦ exp (-(θ * s))) s := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_neg_mul_Ioi' hθ h
  exact integrable_fin_two_mul (integrable_exp_mul_exp_neg_exp hη hc) h2

/-- **The two-scaled tied-truth integral**: `Γ(η) c^{−η} e^{−θh}/(θ|Δ|)`. -/
theorem integral_twoScaledInner {κS QS aS : Fin 2 → ℝ} {η θ c : ℝ}
    (hΔ : κS 0 * QS 1 - κS 1 * QS 0 ≠ 0) (haS : ∀ i, aS i = η * κS i - θ * QS i)
    (hη : 0 < η) (hθ : 0 < θ) (hc : 0 < c) (h : ℝ) :
    ∫ y, twoScaledInner κS QS aS c h y =
      Gamma η * c ^ (-η) * (exp (-(θ * h)) / θ) / |κS 0 * QS 1 - κS 1 * QS 0| := by
  have hM : (twoMat κS QS).det ≠ 0 := by rw [det_twoMat]; exact hΔ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy ↦ twoScaledInner_eq_zero_of_notMem hy), integral_posOrthant_comp_exp]
  simp_rw [twoScaledInner_comp_exp haS]
  have h1 := integral_comp_mulVec (twoMat κS QS) hM (twoScaledSplit η θ c h)
    (measurable_twoScaledSplit η θ c h).aestronglyMeasurable
  rw [integral_twoScaledSplit hη hθ hc, det_twoMat] at h1
  rw [eq_div_iff (abs_ne_zero.mpr hΔ), h1, mul_comm]

theorem integrable_twoScaledInner {κS QS aS : Fin 2 → ℝ} {η θ c : ℝ}
    (hΔ : κS 0 * QS 1 - κS 1 * QS 0 ≠ 0) (haS : ∀ i, aS i = η * κS i - θ * QS i)
    (hη : 0 < η) (hθ : 0 < θ) (hc : 0 < c) (h : ℝ) :
    Integrable (twoScaledInner κS QS aS c h) := by
  have hM : (twoMat κS QS).det ≠ 0 := by rw [det_twoMat]; exact hΔ
  rw [← integrableOn_iff_integrable_of_support_subset (s := Set.pi univ fun _ : Fin 2 ↦ Ioi (0 : ℝ))
    (fun y hy ↦ by
      by_contra h'
      exact hy (twoScaledInner_eq_zero_of_notMem h')),
    integrableOn_posOrthant_comp_exp_iff]
  simp_rw [twoScaledInner_comp_exp haS]
  exact (integrable_comp_mulVec_iff (twoMat κS QS) hM (twoScaledSplit η θ c h)
    (measurable_twoScaledSplit η θ c h).aestronglyMeasurable).mpr
    (integrable_twoScaledSplit hη hθ hc h)

theorem twoScaledInner_nonneg (κS QS aS : Fin 2 → ℝ) (c h : ℝ) (y : Fin 2 → ℝ) :
    0 ≤ twoScaledInner κS QS aS c h y := by
  unfold twoScaledInner
  refine Set.indicator_nonneg (fun y hy ↦ ?_) y
  by_cases hc : y ∈ {y : Fin 2 → ℝ | h < ∑ i, QS i * log (y i)}
  · rw [Set.indicator_of_mem hc]
    exact mul_nonneg (Finset.prod_nonneg fun i _ ↦
      rpow_nonneg (Set.mem_univ_pi.mp hy i).le _) (exp_pos _).le
  · rw [Set.indicator_of_notMem hc]

end Inner

end Laplace.Multi
