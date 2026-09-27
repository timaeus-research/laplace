/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RayTiltInvariance
import Laplace.Multi.PolyhedralCompletion

/-!
# Concentration on the face along a decomposed parameter sequence

Along a natural ray `θ − r u` towards a max-exposed face `A = {⟨u, S⟩ = β}` of positive mass the
mass of the face tends to one, `P_{θ − ru}(A) = faceMass/(faceMass + offFaceMass r) → 1`
(`tendsto_measureReal_family_ray_faceFibre`). For a sequence `v_n − r_n u` with convergent
tangential part `v_n → v_M` and diverging depth `r_n → ∞`, the law differs from the ray
`v_M − r_n u` by the tilt `−⟨v_n − v_M, S⟩`, whose size tends to zero uniformly, so the face mass
still tends to one (`tendsto_measureReal_family_faceFibre_of_components`). This is the
concentration input of the facet accessibility theorem: eventually the off-face mass is as small
as the Schur estimate requires.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Concentration

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

set_option linter.unusedFintypeInType false in
/-- A uniform bound on the statistic. -/
theorem exists_uniform_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, |S i x| ≤ B := by
  choose M hM using fun i ↦ (hS i).2
  have hM0 : ∀ i, 0 ≤ M i := fun i ↦ (abs_nonneg _).trans (hM i (Classical.arbitrary X))
  refine ⟨∑ i, M i, Finset.sum_nonneg fun i _ ↦ hM0 i, fun i x ↦ (hM i x).trans ?_⟩
  exact Finset.single_le_sum (f := M) (fun j _ ↦ hM0 j) (Finset.mem_univ i)

omit [MeasurableSpace X] [Nonempty X] hS in
/-- `|⟨w, S x⟩| ≤ (Σ|wᵢ|) B`. -/
theorem abs_dirLoss_le_sum_mul {B : ℝ} (hB : ∀ i x, |S i x| ≤ B) (w : J → ℝ) (x : X) :
    |dirLoss S w x| ≤ (∑ i, |w i|) * B := by
  calc |dirLoss S w x| = |∑ i, w i * S i x| := rfl
    _ ≤ ∑ i, |w i * S i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * B := Finset.sum_le_sum fun i _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB i x) (abs_nonneg _)
    _ = (∑ i, |w i|) * B := by rw [Finset.sum_mul]

omit [Nonempty X] hS in
/-- The mass of a set under a bounded tilt is at least `e^{−2c}` times the mass. -/
theorem exp_mul_measureReal_le_measureReal_tilted (μ : Measure X) [IsProbabilityMeasure μ]
    {g : X → ℝ} (hg : Bdd g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) {A : Set X} (hA : MeasurableSet A) :
    exp (-(2 * c)) * μ.real A ≤ (μ.tilted g).real A := by
  have hP : IsProbabilityMeasure (μ.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd μ hg)
  have hind : Bdd (A.indicator (1 : X → ℝ)) :=
    ⟨measurable_const.indicator hA, 1, fun x ↦ by by_cases hx : x ∈ A <;> simp [hx]⟩
  have h := le_integral_tilted_of_nonneg μ hg.1 hc hind fun x ↦ by
    by_cases hx : x ∈ A <;> simp [hx]
  rwa [integral_indicator_one hA, integral_indicator_one hA] at h

variable (u : J → ℝ) (β : ℝ)

omit [Nonempty X] in
/-- The face mass along the natural ray. -/
theorem measureReal_family_ray_faceFibre (θ : J → ℝ) (t : ℝ) :
    (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)).real
        {x | dirLoss S u x = β} =
      faceMass S ν θ u β / (faceMass S ν θ u β + offFaceMass S ν θ u β t) := by
  have hF := measurableSet_faceFibre hS u β
  rw [familyMeasure_eq_withDensity_famDens, measureReal_withDensity_ofReal ν
    (famDens_nonneg hS ν _) (integrable_famDens hS ν _) hF]
  have e : faceMass S ν θ u β / (faceMass S ν θ u β + offFaceMass S ν θ u β t) =
      ∫ x in {x | dirLoss S u x = β},
        famWeight S θ x / (faceMass S ν θ u β + offFaceMass S ν θ u β t) ∂ν := by
    rw [integral_div]
    rfl
  rw [e]
  refine setIntegral_congr_fun hF fun x hx ↦ ?_
  have hx' : dirLoss S u x = β := hx
  rw [famDens_ray hS ν θ u β, hx', sub_self, mul_zero, neg_zero, exp_zero, mul_one]

omit [Nonempty X] in
/-- **Concentration along the ray**: the face mass tends to one. -/
theorem tendsto_measureReal_family_ray_faceFibre (θ : J → ℝ) (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) :
    Tendsto (fun t : ℝ ↦
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ - t • u)).real
        {x | dirLoss S u x = β}) atTop (𝓝 1) := by
  simp_rw [measureReal_family_ray_faceFibre hS ν u β θ]
  have hA := faceMass_pos hS ν θ u β hp
  have h := (tendsto_const_nhds (x := faceMass S ν θ u β)).div
    ((tendsto_const_nhds (x := faceMass S ν θ u β)).add (tendsto_offFaceMass hS ν θ u β hβ))
    (by rw [add_zero]; exact hA.ne')
  rw [add_zero, div_self hA.ne'] at h
  exact h

/-- **Concentration along a decomposed sequence**: convergent tangential part and diverging depth
give face mass tending to one. -/
theorem tendsto_measureReal_family_faceFibre_of_components {ι : Type*} {l : Filter ι}
    (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {v : ι → J → ℝ} {vM : J → ℝ}
    (hv : Tendsto v l (𝓝 vM)) {r : ι → ℝ} (hr : Tendsto r l atTop) :
    Tendsto (fun n ↦ (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v n - r n • u)).real
      {x | dirLoss S u x = β}) l (𝓝 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  have hF := measurableSet_faceFibre hS u β
  -- the tilt sizes tend to zero
  have hc : Tendsto (fun n ↦ (∑ i, |(v n - vM) i|) * B) l (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ v n - vM) l (𝓝 0) := by simpa using hv.sub_const vM
    have h1 : Tendsto (fun n ↦ ∑ i, |(v n - vM) i|) l (𝓝 (∑ i, |(0 : J → ℝ) i|)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_abs.comp (continuous_apply i)).tendsto _).comp h0
    simpa using h1.mul_const B
  have hexp : Tendsto (fun n ↦ exp (-(2 * ((∑ i, |(v n - vM) i|) * B)))) l (𝓝 1) := by
    have h2 := (hc.const_mul 2).neg
    rw [mul_zero, neg_zero] at h2
    have := (Real.continuous_exp.tendsto 0).comp h2
    rw [Real.exp_zero] at this
    exact this
  -- the ray mass tends to one
  have hray := (tendsto_measureReal_family_ray_faceFibre hS ν u β vM hβ hp).comp hr
  have hPf : ∀ θ : J → ℝ,
      IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
    intro θ
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  -- squeeze
  have hlow := hexp.mul hray
  rw [mul_one] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n ↦ ?_)
    fun n ↦ ?_
  · simp only [Function.comp_apply]
    rw [familyMeasure_sub_smul_eq_tilted hS ν (v n) vM u (r n)]
    have := hPf (vM - r n • u)
    refine exp_mul_measureReal_le_measureReal_tilted _ (bdd_neg (bdd_dirLoss hS _))
      (fun x ↦ ?_) hF
    rw [abs_neg]
    exact abs_dirLoss_le_sum_mul hB _ x
  · have := hPf (v n - r n • u)
    exact measureReal_le_one

end Concentration

end Laplace.Multi
