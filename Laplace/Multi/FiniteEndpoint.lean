/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NaturalCoordinates

/-!
# Endpoints of natural rays on a finite alphabet: faces of the moment polytope

On a finite alphabet with the counting measure, the posterior `P_r ∝ π e^{-rL}` converges as
`r → ∞` to the prior conditioned on the ground set `{L = min L}`
(`tendsto_priorExp_atTop_finite`, `tendsto_gibbsDensity_atTop_finite`). For the joint exponential
family of `NaturalCoordinates` this says that every natural direction `h` selects the face of the
moment polytope on which `S_h` is minimal: `P_{rh} → π(· | S_h = min S_h)` and the joint mean map
converges to the conditional mean of the augmented statistic on that face
(`tendsto_meanMap_natural_ray_finite`). The prior resolves ties within the face; the direction
selects the face. This is the global boundary map of the response chart, from the featureless
anchor `θ = 0` to the ground states in every direction.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Finite

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The ground-state average of `φ` under `π` on the level set `{L = m₀}`. -/
noncomputable def groundAvg (π L φ : X → ℝ) (m₀ : ℝ) : ℝ :=
  (∑ x ∈ Finset.univ.filter (fun x ↦ L x = m₀), φ x * π x) /
    ∑ x ∈ Finset.univ.filter (fun x ↦ L x = m₀), π x

variable {π L : X → ℝ} (hπ : ∀ x, 0 < π x) {m₀ : ℝ} (hm₀ : ∀ x, m₀ ≤ L x) (hex : ∃ x, L x = m₀)
include hπ hm₀ hex

omit [MeasurableSpace X] [MeasurableSingletonClass X] hπ hm₀ in
theorem ground_filter_nonempty : (Finset.univ.filter (fun x ↦ L x = m₀)).Nonempty := by
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, by simp [hx]⟩

omit [MeasurableSpace X] [MeasurableSingletonClass X] hm₀ in
theorem ground_sum_pos : 0 < ∑ x ∈ Finset.univ.filter (fun x ↦ L x = m₀), π x :=
  Finset.sum_pos (fun x _ ↦ hπ x) (ground_filter_nonempty hex)

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] hπ hex in
/-- The tilted weight `e^{-r(L x − m₀)} c x` tends to `c x` on the ground set and to `0` off it. -/
theorem tendsto_tilt_weight (c : X → ℝ) (x : X) :
    Tendsto (fun r : ℝ ↦ c x * Real.exp (-(r * (L x - m₀)))) atTop
      (𝓝 (if L x = m₀ then c x else 0)) := by
  by_cases hx : L x = m₀
  · simp only [hx, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one, if_true]
    exact tendsto_const_nhds
  · simp only [hx, if_false]
    have hpos : 0 < L x - m₀ := sub_pos.mpr (lt_of_le_of_ne (hm₀ x) (Ne.symm hx))
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hpos)
    have := h.const_mul (c x)
    simpa [Function.comp_def] using this

omit [MeasurableSpace X] [MeasurableSingletonClass X] hπ hex in
/-- The tilted sum tends to the ground-set sum. -/
theorem tendsto_tilt_sum (c : X → ℝ) :
    Tendsto (fun r : ℝ ↦ ∑ x, c x * Real.exp (-(r * (L x - m₀)))) atTop
      (𝓝 (∑ x ∈ Finset.univ.filter (fun x ↦ L x = m₀), c x)) := by
  rw [Finset.sum_filter]
  exact tendsto_finsetSum Finset.univ fun x _ ↦ tendsto_tilt_weight hm₀ c x

omit hπ hm₀ hex in
/-- The posterior expectation on a finite alphabet, as a ratio of tilted sums. -/
theorem priorExp_count_eq (φ : X → ℝ) (r : ℝ) :
    priorExp Measure.count π L φ r =
      (∑ x, φ x * π x * Real.exp (-(r * (L x - m₀)))) /
        ∑ x, π x * Real.exp (-(r * (L x - m₀))) := by
  unfold priorExp priorZ
  rw [integral_count, integral_count]
  have hc : Real.exp (r * m₀) ≠ 0 := (Real.exp_pos _).ne'
  have e : ∀ x, Real.exp (r * m₀) * Real.exp (-(r * L x)) = Real.exp (-(r * (L x - m₀))) :=
    fun x ↦ by rw [← Real.exp_add]; congr 1; ring
  rw [← mul_div_mul_left _ _ hc, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ ↦ ?_ <;> rw [← e x] <;> ring

/-- **The endpoint of a ray on a finite alphabet**: `⟨φ⟩_r → E_π[φ | L = min L]`. -/
theorem tendsto_priorExp_atTop_finite (φ : X → ℝ) :
    Tendsto (fun r ↦ priorExp Measure.count π L φ r) atTop (𝓝 (groundAvg π L φ m₀)) := by
  have hnum := tendsto_tilt_sum hm₀ (fun x ↦ φ x * π x)
  have hden := tendsto_tilt_sum hm₀ π
  have h := hnum.div hden (ground_sum_pos hπ hex).ne'
  refine h.congr' (Filter.Eventually.of_forall fun r ↦ ?_)
  simp only [Pi.div_apply]
  rw [priorExp_count_eq (m₀ := m₀) φ r]

/-- **The endpoint density**: `P_r(x) → π(x)/π(ground)` on the ground set and `→ 0` off it. -/
theorem tendsto_gibbsDensity_atTop_finite (x : X) :
    Tendsto (fun r ↦ gibbsDensity Measure.count π L r x) atTop
      (𝓝 (if L x = m₀ then π x / ∑ y ∈ Finset.univ.filter (fun y ↦ L y = m₀), π y else 0)) := by
  classical
  have h := tendsto_priorExp_atTop_finite hπ hm₀ hex (fun y ↦ if y = x then 1 else 0)
  have e : ∀ r, priorExp Measure.count π L (fun y ↦ if y = x then 1 else 0) r =
      gibbsDensity Measure.count π L r x := fun r ↦ by
    unfold priorExp gibbsDensity
    rw [integral_count]
    congr 1
    rw [Finset.sum_eq_single x (fun y _ hy ↦ by simp [hy]) (by simp)]
    simp
  simp_rw [e] at h
  have hval : groundAvg π L (fun y ↦ if y = x then 1 else 0) m₀ =
      if L x = m₀ then π x / ∑ y ∈ Finset.univ.filter (fun y ↦ L y = m₀), π y else 0 := by
    unfold groundAvg
    rw [Finset.sum_filter, Finset.sum_filter]
    by_cases hx : L x = m₀
    · rw [if_pos hx]
      congr 1
      rw [Finset.sum_eq_single x (fun y _ hy ↦ by simp [hy]) (by simp)]
      simp [hx]
    · rw [if_neg hx]
      have : (∑ y, if L y = m₀ then (if y = x then (1 : ℝ) else 0) * π y else 0) = 0 :=
        Finset.sum_eq_zero fun y _ ↦ by
          by_cases hy : y = x
          · subst hy; simp [hx]
          · simp [hy]
      rw [this, zero_div]
  rw [hval] at h
  exact h

end Finite

/-! ### Natural rays of the joint family -/

section Joint

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  {ι : Type*} [Fintype ι] {π L₀ : X → ℝ} (hπ : ∀ x, 0 < π x) {R : ι → X → ℝ}
  (h : Option ι → ℝ) {m₀ : ℝ} (hm₀ : ∀ x, m₀ ≤ dirLoss (jointStat L₀ R) h x)
  (hex : ∃ x, dirLoss (jointStat L₀ R) h x = m₀)
include hπ hm₀ hex

omit [Fintype X] [MeasurableSingletonClass X] hπ hm₀ hex in
/-- The natural ray `θ = r h` is the tilt of the statistic `S_h` by `r`. -/
theorem priorExp_natural_ray (φ : X → ℝ) (r : ℝ) :
    priorExp Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (r • h)) φ 1 =
      priorExp Measure.count π (dirLoss (jointStat L₀ R) h) φ r := by
  have e : affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) (r • h) =
      fun x ↦ r * dirLoss (jointStat L₀ R) h x + 0 := by
    funext x
    simp only [affLoss, dirLoss, Pi.smul_apply, smul_eq_mul, zero_add, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e, priorExp_smul_add, mul_one]

/-- **Faces of the moment polytope**: along the natural ray `rh` the posterior expectation of any
observable converges to its prior average on the face `{S_h = min S_h}`. -/
theorem tendsto_priorExp_natural_ray (φ : X → ℝ) :
    Tendsto (fun r : ℝ ↦ priorExp Measure.count π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R)
      (r • h)) φ 1) atTop (𝓝 (groundAvg π (dirLoss (jointStat L₀ R) h) φ m₀)) := by
  simp_rw [priorExp_natural_ray h]
  exact tendsto_priorExp_atTop_finite hπ hm₀ hex φ

/-- **The boundary map of the response chart**: the joint mean map along the natural ray `rh`
converges to the conditional mean of the augmented statistic on the face selected by `h`. -/
theorem tendsto_meanMap_natural_ray_finite (j : Option ι) :
    Tendsto (fun r : ℝ ↦ meanMap Measure.count π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (r • h) j)
      atTop
      (𝓝 (groundAvg π (dirLoss (jointStat L₀ R) h) (jointStat L₀ R j) m₀)) :=
  tendsto_priorExp_natural_ray hπ h hm₀ hex (jointStat L₀ R j)

end Joint

end Laplace.Multi
