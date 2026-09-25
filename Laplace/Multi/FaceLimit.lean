/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AnnealingRay

/-!
# Boundary rays: the positive-mass face

Tilt a positive prior `π` by a bounded statistic `V` with essential lower bound `α`:
`q_λ ∝ e^{−λV} π`, `λ → ∞`. Let `F = {V = α}` be the supporting face and `p = ∫_F π` its mass.

* the shifted normaliser converges to the face mass, `e^{λα} Z_λ → p` (`tendsto_shifted_priorZ`);
* if `p > 0`, every bounded observable converges to its conditional expectation on the face,
  `⟨φ⟩_λ → (∫_F φ π)/p` (`tendsto_priorExp_face`): the ray has a boundary posterior, the
  conditional law on the face;
* the tilt-weighted excess `λ ⟨V − α⟩_λ → 0` (`tendsto_mul_priorExp_shift`), so that the
  information relative to the prior converges, `KL(q_λ ‖ π̄) → −log (p / ∫π) = −log π̄(F)`
  (`tendsto_mixKL_face`): reaching a positive-mass face costs exactly the log of its prior mass.

Instantiated on the feature ray `a = s v` at fixed temperature `t`, with `V = R_v` and the tilted
prior `e^{−tL₀}π` (`tendsto_priorExp_ray_face`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem mul_exp_neg_le_exp_neg_one (y : ℝ) : y * Real.exp (-y) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y - 1)
  have hpos := Real.exp_pos (-y)
  have e : Real.exp (y - 1) * Real.exp (-y) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  calc y * Real.exp (-y) ≤ Real.exp (y - 1) * Real.exp (-y) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
    _ = Real.exp (-1) := e

/-- The shifted normaliser `e^{λα} Z_λ = ∫ e^{−λ(V−α)} π`. -/
theorem exp_mul_priorZ (π V : X → ℝ) (α lam : ℝ) :
    Real.exp (lam * α) * priorZ μ π V lam =
      ∫ x, Real.exp (-(lam * (V x - α))) * π x ∂μ := by
  unfold priorZ
  rw [← integral_const_mul]
  congr 1
  funext x
  have e : Real.exp (lam * α) * Real.exp (-(lam * V x)) = Real.exp (-(lam * (V x - α))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← mul_assoc, e]

theorem priorExp_sub_const (π V L : X → ℝ) (α lam : ℝ) (hV' : Integrable (fun x ↦ V x *
    Real.exp (-(lam * L x)) * π x) μ) (h0 : Integrable (fun x ↦ Real.exp (-(lam * L x)) * π x) μ)
    (hZ : priorZ μ π L lam ≠ 0) :
    priorExp μ π L (fun x ↦ V x - α) lam = priorExp μ π L V lam - α := by
  unfold priorExp
  have e : (∫ x, (V x - α) * Real.exp (-(lam * L x)) * π x ∂μ) =
      (∫ x, V x * Real.exp (-(lam * L x)) * π x ∂μ) -
        α * ∫ x, Real.exp (-(lam * L x)) * π x ∂μ := by
    rw [← integral_const_mul, ← integral_sub hV' (h0.const_mul α)]
    congr 1; funext x; ring
  rw [e]
  unfold priorZ at hZ ⊢
  field_simp

section Face

variable {π : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) {V : X → ℝ} (hVm : Measurable V) {M : ℝ} (hV : ∀ x, |V x| ≤ M)
  {α : ℝ} (hα : ∀ᵐ x ∂μ, α ≤ V x)
include hπm hπi hπ hπpos hVm hV hα

omit hπi hπ hπpos hV hα in
theorem aestronglyMeasurable_shift_weight {φ : X → ℝ} (hφm : Measurable φ) (lam : ℝ) :
    AEStronglyMeasurable (fun x ↦ φ x * Real.exp (-(lam * (V x - α))) * π x) μ :=
  ((hφm.mul (Real.measurable_exp.comp ((hVm.sub measurable_const).const_mul lam).neg)).mul
    hπm).aestronglyMeasurable

omit hπm hπi hπ hπpos hVm hV in
/-- Pointwise limit of the shifted weights: the indicator of the face. -/
theorem tendsto_shift_weight (φ : X → ℝ) :
    ∀ᵐ x ∂μ, Tendsto (fun lam : ℝ ↦ φ x * Real.exp (-(lam * (V x - α))) * π x) atTop
      (𝓝 ({x | V x = α}.indicator (fun x ↦ φ x * π x) x)) := by
  filter_upwards [hα] with x hx
  by_cases hxF : V x = α
  · rw [Set.indicator_of_mem (show x ∈ {x | V x = α} from hxF)]
    simp only [hxF, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem (show x ∉ {x | V x = α} from hxF)]
    have hpos : 0 < V x - α := sub_pos.2 (lt_of_le_of_ne hx fun h ↦ hxF h.symm)
    have h1 : Tendsto (fun lam : ℝ ↦ lam * (V x - α)) atTop atTop :=
      tendsto_id.atTop_mul_const hpos
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := (h2.const_mul (φ x)).mul_const (π x)
    simpa [Function.comp_def] using h3

omit hπpos hV in
/-- Dominated convergence of the shifted numerators to the face integral. -/
theorem tendsto_shift_integral {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) :
    Tendsto (fun lam : ℝ ↦ ∫ x, φ x * Real.exp (-(lam * (V x - α))) * π x ∂μ) atTop
      (𝓝 (∫ x in {x | V x = α}, φ x * π x ∂μ)) := by
  have hF : MeasurableSet {x | V x = α} := hVm (measurableSet_singleton α)
  rw [← integral_indicator hF]
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ Mφ * π x)
    (Eventually.of_forall fun lam ↦ aestronglyMeasurable_shift_weight hπm hVm hφm lam) ?_
    (hπi.const_mul Mφ) (tendsto_shift_weight hα φ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
  filter_upwards [hα] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (hπ x)]
  have h1 : Real.exp (-(lam * (V x - α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ x)
  calc |φ x| * Real.exp (-(lam * (V x - α))) * π x ≤ Mφ * 1 * π x :=
        mul_le_mul (mul_le_mul (hφ x) h1 (Real.exp_pos _).le hMφ) le_rfl (hπ x).le
          (by positivity)
    _ = Mφ * π x := by ring

omit hπpos hV in
/-- **The shifted normaliser converges to the face mass**: `e^{λα} Z_λ → ∫_F π`. -/
theorem tendsto_shifted_priorZ :
    Tendsto (fun lam : ℝ ↦ Real.exp (lam * α) * priorZ μ π V lam) atTop
      (𝓝 (∫ x in {x | V x = α}, π x ∂μ)) := by
  simp only [exp_mul_priorZ π V α]
  have h := tendsto_shift_integral hπm hπi hπ hVm hα (φ := fun _ ↦ (1 : ℝ))
    measurable_const (Mφ := 1) (fun _ ↦ by simp)
  simpa using h

omit hπpos hV in
/-- **The boundary posterior on a positive-mass face**: `⟨φ⟩_λ → (∫_F φ π) / (∫_F π)`. -/
theorem tendsto_priorExp_face (hp : 0 < ∫ x in {x | V x = α}, π x ∂μ) {φ : X → ℝ}
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) :
    Tendsto (fun lam : ℝ ↦ priorExp μ π V φ lam) atTop
      (𝓝 ((∫ x in {x | V x = α}, φ x * π x ∂μ) / ∫ x in {x | V x = α}, π x ∂μ)) := by
  have hnum := tendsto_shift_integral hπm hπi hπ hVm hα hφm hφ
  have hden := tendsto_shifted_priorZ hπm hπi hπ hVm hα
  have e : (fun lam : ℝ ↦ priorExp μ π V φ lam) = fun lam ↦
      (∫ x, φ x * Real.exp (-(lam * (V x - α))) * π x ∂μ) /
        (Real.exp (lam * α) * priorZ μ π V lam) := by
    funext lam
    unfold priorExp
    rw [← mul_div_mul_left _ _ (Real.exp_pos (lam * α)).ne', ← integral_const_mul]
    congr 1
    congr 1
    funext x
    have e' : Real.exp (lam * α) * Real.exp (-(lam * V x)) = Real.exp (-(lam * (V x - α))) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (lam * α) * (φ x * Real.exp (-(lam * V x)) * π x)
        = φ x * (Real.exp (lam * α) * Real.exp (-(lam * V x))) * π x := by ring
      _ = _ := by rw [e']
  rw [e]
  exact (hnum.div hden hp.ne').congr fun lam ↦ rfl

omit hπpos hV in
/-- **The tilt-weighted excess vanishes on a positive-mass face**: `λ ⟨V − α⟩_λ → 0`. -/
theorem tendsto_mul_priorExp_shift (hp : 0 < ∫ x in {x | V x = α}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ lam * priorExp μ π V (fun x ↦ V x - α) lam) atTop (𝓝 0) := by
  have hden := tendsto_shifted_priorZ hπm hπi hπ hVm hα
  -- the numerator `∫ λ(V−α) e^{−λ(V−α)} π → 0`
  have hnum : Tendsto (fun lam : ℝ ↦ ∫ x, lam * (V x - α) * Real.exp (-(lam * (V x - α))) *
      π x ∂μ) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μ := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ Real.exp (-1) * π x) ?_ ?_
      (hπi.const_mul _) ?_
    · exact Eventually.of_forall fun lam ↦
        (((measurable_const.mul (hVm.sub measurable_const)).mul
          (Real.measurable_exp.comp ((hVm.sub measurable_const).const_mul lam).neg)).mul
          hπm).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
      filter_upwards [hα] with x hx
      have hy : 0 ≤ lam * (V x - α) := mul_nonneg hlam (by linarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hπ x), abs_of_nonneg (mul_nonneg hy
        (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (mul_exp_neg_le_exp_neg_one _) (hπ x).le
    · filter_upwards [hα] with x hx
      by_cases hxF : V x = α
      · simp [hxF]
      · have hpos : 0 < V x - α := sub_pos.2 (lt_of_le_of_ne hx fun h ↦ hxF h.symm)
        have h1 : Tendsto (fun lam : ℝ ↦ lam * (V x - α)) atTop atTop :=
          tendsto_id.atTop_mul_const hpos
        have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1
        have h3 := h2.mul_const (π x)
        simpa [Function.comp_def] using h3
  have e : (fun lam : ℝ ↦ lam * priorExp μ π V (fun x ↦ V x - α) lam) = fun lam ↦
      (∫ x, lam * (V x - α) * Real.exp (-(lam * (V x - α))) * π x ∂μ) /
        (Real.exp (lam * α) * priorZ μ π V lam) := by
    funext lam
    unfold priorExp
    rw [← mul_div_assoc, ← mul_div_mul_left _ _ (Real.exp_pos (lam * α)).ne',
      ← integral_const_mul, ← integral_const_mul]
    congr 1
    congr 1
    funext x
    have e' : Real.exp (lam * α) * Real.exp (-(lam * V x)) = Real.exp (-(lam * (V x - α))) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (lam * α) * (lam * ((V x - α) * Real.exp (-(lam * V x)) * π x))
        = lam * (V x - α) * (Real.exp (lam * α) * Real.exp (-(lam * V x))) * π x := by ring
      _ = _ := by rw [e']
  rw [e]
  have := hnum.div hden hp.ne'
  rw [zero_div] at this
  exact this.congr fun lam ↦ rfl

/-- **The information cost of a positive-mass face**: `KL(q_λ ‖ π̄) → log ∫π − log ∫_F π`. -/
theorem tendsto_mixKL_face [Nonempty X] (hp : 0 < ∫ x in {x | V x = α}, π x ∂μ) :
    Tendsto (fun lam : ℝ ↦ mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0) atTop
      (𝓝 (Real.log (∫ x, π x ∂μ) - Real.log (∫ x in {x | V x = α}, π x ∂μ))) := by
  have hT : ∀ lam : ℝ, TiltData μ (baseWeight π (fun _ ↦ (0 : ℝ)) lam) V M := fun lam ↦
    tiltData_baseWeight_of_bounded (μ := μ) hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const
      (M₀ := 0) (fun _ ↦ by simp) hVm hV lam
  have hkl : ∀ lam : ℝ, mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0 =
      Real.log (∫ x, π x ∂μ) - Real.log (Real.exp (lam * α) * priorZ μ π V lam) -
        lam * priorExp μ π V (fun x ↦ V x - α) lam := by
    intro lam
    rw [(hT lam).mixKL_eq (fun x ↦ (hπ x).le) 1 0]
    unfold mixLogZ mixExp
    have e0 : pathLoss (fun _ ↦ (0 : ℝ)) V 0 = fun _ ↦ (0 : ℝ) := by
      funext x; simp [pathLoss]
    have e1 : pathLoss (fun _ ↦ (0 : ℝ)) V 1 = V := by
      funext x; simp [pathLoss]
    rw [e0, e1]
    have hZ0 : priorZ μ π (fun _ ↦ (0 : ℝ)) lam = ∫ x, π x ∂μ := by
      unfold priorZ; simp
    have hT' : TiltData μ (baseWeight π V lam) V M :=
      tiltData_baseWeight_of_bounded (μ := μ) (L₀ := V) (Δ := V) hπm hπi (fun x ↦ (hπ x).le)
        hπpos hVm hV hVm hV lam
    have hZ : priorZ μ π V lam ≠ 0 := hT'.ν_pos.ne'
    have hI1 : Integrable (fun x ↦ V x * Real.exp (-(lam * V x)) * π x) μ :=
      (hT'.integrable_tilt hVm hV lam 0).congr (Eventually.of_forall fun x ↦ by
        simp only [baseWeight, mul_zero, neg_zero, Real.exp_zero, mul_one]; ring)
    have hI0 : Integrable (fun x ↦ Real.exp (-(lam * V x)) * π x) μ :=
      (hT'.integrable_tilt (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1) (fun _ ↦ by simp)
        lam 0).congr (Eventually.of_forall fun x ↦ by
          simp only [baseWeight, mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul])
    rw [hZ0, Real.log_mul (Real.exp_pos _).ne' hZ, Real.log_exp,
      priorExp_sub_const π V V α lam hI1 hI0 hZ]
    ring
  have e : (fun lam : ℝ ↦ mixKL μ π (fun _ ↦ (0 : ℝ)) V lam 1 0) = fun lam ↦
      Real.log (∫ x, π x ∂μ) - Real.log (Real.exp (lam * α) * priorZ μ π V lam) -
        lam * priorExp μ π V (fun x ↦ V x - α) lam := funext hkl
  rw [e]
  have h := ((tendsto_const_nhds (x := Real.log (∫ x, π x ∂μ))).sub
    ((tendsto_shifted_priorZ hπm hπi hπ hVm hα).log hp.ne')).sub
    (tendsto_mul_priorExp_shift hπm hπi hπ hVm hα hp)
  simpa using h

end Face

end Laplace.Multi
