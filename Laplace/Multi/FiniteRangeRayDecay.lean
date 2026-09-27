/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteRangeFaceGeometry
import Laplace.Multi.RayVarianceSandwich
import Laplace.Multi.FisherAccessibility

/-!
# Exponential decay along the normal ray under a support gap

Along the natural ray `θ − t u` towards the exposed face `{⟨u,S⟩ = β}`, a **support gap**
`δ > 0` — almost surely `⟨u,S⟩ = β` or `⟨u,S⟩ ≤ β − δ` — makes the off-face mass decay
exponentially, `B_t ≤ e^{−δt} B_0` (`offFaceMass_le_exp`), hence the Fisher speed of the ray decays
as `raySpeedSq(t) ≤ D² (B_0/A) e^{−δt}` (`raySpeedSq_le_exp`) with `D` a bound on the slack and
`A` the face mass, so the ray has **finite Fisher length**
(`integrableOn_sqrt_raySpeedSq_of_gap`). Every exposed face of a finitely supported model is
reached by its normal ray in finite Fisher length (`integrableOn_sqrt_raySpeedSq_of_finiteRange`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Decay

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ) {δ : ℝ} (hδ : 0 < δ)
  (hgap : ∀ᵐ x ∂ν, dirLoss S u x = β ∨ dirLoss S u x ≤ β - δ)
include hS hδ hgap

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The support gap gives the a.e. slack bound `⟨u,S⟩ ≤ β`. -/
theorem ae_dirLoss_le_of_gap : ∀ᵐ x ∂ν, dirLoss S u x ≤ β := by
  filter_upwards [hgap] with x hx
  rcases hx with h | h
  · exact h.le
  · linarith

omit [Nonempty X] [Nonempty J] hδ in
/-- **The off-face mass decays exponentially**: `B_t ≤ e^{−δt} B_0` for `t ≥ 0`. -/
theorem offFaceMass_le_exp {t : ℝ} (ht : 0 ≤ t) :
    offFaceMass S ν θ u β t ≤ Real.exp (-(δ * t)) * offFaceMass S ν θ u β 0 := by
  unfold offFaceMass
  rw [← integral_const_mul]
  refine integral_mono_ae (integrable_offFace hS ν θ u β t).integrableOn
    ((integrable_offFace hS ν θ u β 0).integrableOn.const_mul _) ?_
  filter_upwards [ae_restrict_of_ae hgap, ae_restrict_mem (measurableSet_faceFibre hS u β).compl]
    with x hx hxF
  have hxF' : ¬ dirLoss S u x = β := hxF
  rcases hx with h | h
  · exact absurd h hxF'
  · simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    rw [mul_comm (Real.exp (-(δ * t)))]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (famWeight_pos θ x).le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : δ ≤ β - dirLoss S u x) ht]

omit [Nonempty X] [Nonempty J] hδ in
/-- **The second moment of the slack decays exponentially**:
`∫ (β − ⟨u,S⟩)² dP_{θ−tu} ≤ D² (B_0/A) e^{−δt}` for a slack bound `|β − ⟨u,S⟩| ≤ D`. -/
theorem integral_sq_slack_le_exp (hp : 0 < ν.real {x | dirLoss S u x = β}) {D : ℝ}
    (hD : ∀ x, |β - dirLoss S u x| ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, (β - dirLoss S u x) ^ 2 * famDens S ν (θ - t • u) x ∂ν ≤
      D ^ 2 * (offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ * t)) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hAB : 0 < faceMass S ν θ u β + offFaceMass S ν θ u β t := by linarith
  have hF := measurableSet_faceFibre hS u β
  have hmg : Measurable fun x ↦ β - dirLoss S u x := (bdd_dirLoss hS u).1.const_sub β
  have e : ∀ x, (β - dirLoss S u x) ^ 2 * famDens S ν (θ - t • u) x =
      (β - dirLoss S u x) ^ 2 * (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t) := fun x ↦ by
    rw [famDens_ray hS ν θ u β]
    ring
  simp_rw [e]
  rw [integral_div]
  have hint : Integrable (fun x ↦ (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x))))) ν :=
    (integrable_offFace hS ν θ u β t).bdd_mul (hmg.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hD x) 2)
  -- the integrand vanishes on the face and is at most `D²` times the off-face weight off it
  have hsplit : ∫ x, (β - dirLoss S u x) ^ 2 *
      (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν ≤
      D ^ 2 * offFaceMass S ν θ u β t := by
    rw [← integral_add_compl₀ hF.nullMeasurableSet hint,
      setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
        have hx' : dirLoss S u x = β := hx
        rw [hx', sub_self]
        ring, zero_add, offFaceMass, ← integral_const_mul]
    refine setIntegral_mono_on hint.integrableOn
      ((integrable_offFace hS ν θ u β t).integrableOn.const_mul _) hF.compl fun x _ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (famWeight_pos θ x).le (Real.exp_pos _).le)
    calc (β - dirLoss S u x) ^ 2 = |β - dirLoss S u x| ^ 2 := (sq_abs _).symm
      _ ≤ D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hD x) 2
  calc (∫ x, (β - dirLoss S u x) ^ 2 *
        (famWeight S θ x * Real.exp (-(t * (β - dirLoss S u x)))) ∂ν) /
        (faceMass S ν θ u β + offFaceMass S ν θ u β t)
      ≤ D ^ 2 * offFaceMass S ν θ u β t / faceMass S ν θ u β := by
        refine (div_le_div_of_nonneg_right hsplit hAB.le).trans ?_
        exact div_le_div_of_nonneg_left (by positivity) hA (by linarith)
    _ ≤ D ^ 2 * (Real.exp (-(δ * t)) * offFaceMass S ν θ u β 0) / faceMass S ν θ u β := by
        gcongr
        exact offFaceMass_le_exp hS ν θ u β hgap ht
    _ = D ^ 2 * (offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ * t)) := by
        ring

omit [Nonempty X] [Nonempty J] hδ in
/-- **The Fisher speed of the ray decays exponentially**: `raySpeedSq(t) ≤ D² (B_0/A) e^{−δt}`. -/
theorem raySpeedSq_le_exp (hp : 0 < ν.real {x | dirLoss S u x = β}) {D : ℝ}
    (hD : ∀ x, |β - dirLoss S u x| ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    raySpeedSq S ν θ u t ≤
      D ^ 2 * (offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ * t)) :=
  (raySpeedSq_le_integral_sq hS ν θ u β t).trans
    (integral_sq_slack_le_exp hS ν θ u β hgap hp hD ht)

omit [Nonempty J] hδ in
/-- The Fisher speed of the ray is dominated by an exponential. -/
theorem sqrt_raySpeedSq_le_exp (hp : 0 < ν.real {x | dirLoss S u x = β}) {D : ℝ}
    (hD : ∀ x, |β - dirLoss S u x| ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    √(raySpeedSq S ν θ u t) ≤
      D * √(offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ / 2 * t)) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD (Classical.arbitrary X))
  have hr0 : 0 ≤ offFaceMass S ν θ u β 0 / faceMass S ν θ u β :=
    div_nonneg (offFaceMass_nonneg hS ν θ u β 0) (faceMass_pos hS ν θ u β hp).le
  calc √(raySpeedSq S ν θ u t) ≤
        √(D ^ 2 * (offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ * t))) :=
        Real.sqrt_le_sqrt (raySpeedSq_le_exp hS ν θ u β hgap hp hD ht)
    _ = D * √(offFaceMass S ν θ u β 0 / faceMass S ν θ u β) * Real.exp (-(δ / 2 * t)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD0]
        congr 1
        rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
        congr 1
        ring

omit [Nonempty J] in
/-- **A support gap gives a normal ray of finite Fisher length.** -/
theorem integrableOn_sqrt_raySpeedSq_of_gap (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    IntegrableOn (fun t ↦ √(raySpeedSq S ν θ u t)) (Ioi 0) := by
  obtain ⟨_, K, hK⟩ := bdd_dirLoss hS u
  have hD : ∀ x, |β - dirLoss S u x| ≤ |β| + K := fun x ↦
    (abs_sub _ _).trans (add_le_add le_rfl (hK x))
  have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-(δ / 2 * t))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 (half_pos hδ)
    exact this.congr_fun (fun t _ ↦ by ring_nf) measurableSet_Ioi
  refine Integrable.mono' ((hexp.const_mul
    ((|β| + K) * √(offFaceMass S ν θ u β 0 / faceMass S ν θ u β))))
    ((continuous_sqrt_raySpeedSq hS ν θ u).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_raySpeedSq_le_exp hS ν θ u β hgap hp hD (le_of_lt ht)

end Decay

section FiniteRange

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hae : ∀ᵐ x ∂ν, statPoint S x ∈ V)
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hae hcharged

omit [Nonempty J] in
/-- **Every exposed face of a finitely supported model is reached in finite Fisher length** by
its normal ray, from any base point. -/
theorem integrableOn_sqrt_raySpeedSq_of_finiteRange (θ : J → ℝ) {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V) (hz₀β : dotJ u z₀ = β) :
    IntegrableOn (fun t ↦ √(raySpeedSq S ν θ u t)) (Ioi 0) :=
  integrableOn_sqrt_raySpeedSq_of_gap hS ν θ u β (faceGap_pos V u β)
    (ae_face_or_le_sub_gap ν V hae hV) (faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β)

end FiniteRange

end Laplace.Multi
