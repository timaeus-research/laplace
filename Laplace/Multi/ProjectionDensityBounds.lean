/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralVertexSection

/-!
# Polyhedral completion III: bounded representatives and domination

Every finite-rate response projection `q_M` has a density representative `f` with
`c 1_A ≤ f ≤ C 1_A` for a measurable set `A` of positive mass (`exists_projection_density_bounds`):
this is the bounded exponential tilt on the terminal law of an exposed chain. Consequently any
feasible law `r` at `M` with bounded density `h` and finite relative entropy is **dominated** by the
projection, `δ h ≤ f` a.e. (`exists_pos_mul_le_projection_density`): Pythagoras gives
`KL(r‖q_M) < ∞`, hence `r ≪ q_M`, so `r` vanishes off `A` where `f ≥ c`. Applied to the vertex laws
this is the input of the recovery argument (`exists_pos_mul_vertexDensity_le`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Bounds

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Bounded representative of the projection density**: `q_M = f ν` with `c 1_A ≤ f ≤ C 1_A`
on a measurable set `A` of positive mass, and `f = 0` off `A`. -/
theorem exists_projection_density_bounds {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    ∃ (A : Set X) (f : X → ℝ) (c C : ℝ), MeasurableSet A ∧ 0 < ν.real A ∧ 0 < c ∧
      Measurable f ∧
      responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∀ x ∈ A, c ≤ f x ∧ f x ≤ C) ∧ ∀ x ∉ A, f x = 0 := by
  obtain ⟨A, n, hchain, hrel⟩ := exists_exposedChain hS ν hfin
  obtain ⟨θ, -, hθ⟩ := responseProjection_eq_of_exposedChain hS ν hchain hrel
  have hAm := hchain.measurableSet hS
  have hApos := hchain.pos hS
  have hA0 : ν A ≠ 0 := (ENNReal.toReal_pos_iff.1 hApos).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  obtain ⟨K, hK⟩ := (bdd_dirLoss hS θ).2
  have hm : Measurable (affLoss (fun _ ↦ (0 : ℝ)) S θ) := by
    unfold affLoss
    exact measurable_const.add (Finset.measurable_sum _ fun i _ ↦ (hS i).1.const_mul _)
  have haff : ∀ x, affLoss (fun _ ↦ (0 : ℝ)) S θ x = dirLoss S θ x := fun x ↦ by
    simp [affLoss, dirLoss]
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = priorZ (faceMeasure ν A) (fun _ ↦ (1 : ℝ))
    (affLoss (fun _ ↦ (0 : ℝ)) S θ) 1 := ⟨_, rfl⟩
  have hint : Integrable (fun x ↦ Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)))
      (faceMeasure ν A) :=
    integrable_of_bdd_prob _ ⟨(hm.const_mul 1).neg.exp, Real.exp K, fun x ↦ by
      rw [Real.abs_exp]
      exact Real.exp_le_exp.2 (by rw [one_mul, haff]; linarith [(abs_le.1 (hK x)).1])⟩
  have hZpos : 0 < Z := by
    rw [hZ]
    unfold priorZ
    simp only [mul_one]
    exact integral_exp_pos hint
  have hdens : Measurable fun x ↦ ENNReal.ofReal
      (Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) * (fun _ : X ↦ (1 : ℝ)) x / Z) :=
    (((hm.const_mul 1).neg.exp.mul measurable_const).div_const Z).ennreal_ofReal
  refine ⟨A, A.indicator fun x ↦ Real.exp (-(1 * affLoss (fun _ ↦ (0 : ℝ)) S θ x)) /
    (Z * ν.real A), Real.exp (-K) / (Z * ν.real A), Real.exp K / (Z * ν.real A), hAm, hApos,
    by positivity, ((hm.const_mul 1).neg.exp.div_const _).indicator hAm, ?_, fun x hx ↦ ?_,
    fun x hx ↦ Set.indicator_of_notMem hx _⟩
  · rw [hθ]
    unfold familyMeasure
    rw [← hZ, faceMeasure_eq_withDensity ν hAm,
      ← withDensity_mul ν (measurable_const.indicator hAm) hdens]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, mul_one]
      have e : (ν A)⁻¹ = ENNReal.ofReal (ν.real A)⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hApos, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top ν A)]
      rw [e, ← ENNReal.ofReal_mul (inv_nonneg.2 hApos.le)]
      congr 1
      field_simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, ENNReal.ofReal_zero]
  · rw [Set.indicator_of_mem hx]
    have hZA : 0 < Z * ν.real A := by positivity
    have h1 := abs_le.1 (hK x)
    constructor
    · exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by rw [one_mul, haff]; linarith)) hZA.le
    · exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by rw [one_mul, haff]; linarith)) hZA.le

/-- **Domination**: a feasible law `r = h ν` with bounded density and finite relative entropy is
dominated by the projection, `δ h ≤ f` a.e., for any representative `f ≥ c 1_A` of `q_M` vanishing
off `A`. -/
theorem exists_pos_mul_le_projection_density {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    {A : Set X} {f : X → ℝ} {c : ℝ} (hA : MeasurableSet A) (hc : 0 < c)
    (hf : responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hfc : ∀ x ∈ A, c ≤ f x) (hf0 : ∀ x ∉ A, f x = 0)
    {h : X → ℝ} (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x) {H : ℝ} (hhH : ∀ x, h x ≤ H)
    (hP : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (h x)))
    (hmean : (fun i ↦ ∫ x, S i x ∂ν.withDensity (fun x ↦ ENNReal.ofReal (h x))) = M)
    (hkl : klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (h x)) ν ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂ν, δ * h x ≤ f x := by
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have hkq : klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (h x))
      (responseProjection hS ν M) ≠ ⊤ := by
    intro htop
    apply hkl
    rw [hpyth _ hP hmean, htop, top_add]
  have hrq := (klDiv_ne_top_iff.1 hkq).1
  have hqA : responseProjection hS ν M Aᶜ = 0 := by
    rw [hf, withDensity_apply _ hA.compl]
    refine (setLIntegral_congr_fun hA.compl (g := fun _ ↦ 0) fun x hx ↦ ?_).trans lintegral_zero
    rw [hf0 x hx, ENNReal.ofReal_zero]
  have hrA := hrq hqA
  have hh_zero : ∀ᵐ x ∂ν, x ∉ A → h x = 0 := by
    rw [withDensity_apply _ hA.compl, lintegral_eq_zero_iff hhm.ennreal_ofReal] at hrA
    have hrA' : ∀ᵐ x ∂ν.restrict Aᶜ, ENNReal.ofReal (h x) = 0 := hrA
    rw [ae_restrict_iff' hA.compl] at hrA'
    filter_upwards [hrA'] with x hx hxA
    have := hx hxA
    rw [ENNReal.ofReal_eq_zero] at this
    exact le_antisymm this (hh0 x)
  have hH0 : 0 ≤ H := (hh0 (Classical.arbitrary X)).trans (hhH _)
  have hδ : 0 < c / (H + 1) := div_pos hc (by linarith)
  refine ⟨c / (H + 1), hδ, ?_⟩
  filter_upwards [hh_zero] with x hx
  by_cases hxA : x ∈ A
  · calc c / (H + 1) * h x ≤ c / (H + 1) * H := mul_le_mul_of_nonneg_left (hhH x) hδ.le
      _ ≤ c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      _ ≤ f x := hfc x hxA
  · rw [hx hxA, mul_zero, hf0 x hxA]

end Bounds

section Vertex

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) (hV : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hV

/-- **The vertex laws are dominated by the projection**: for simplex weights `a` with barycentre
`M`, `δ h_a ≤ f` a.e. for any bounded-below representative `f` of `dq_M/dν`. -/
theorem exists_pos_mul_vertexDensity_le {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    {A : Set X} {f : X → ℝ} {c : ℝ} (hA : MeasurableSet A) (hc : 0 < c)
    (hf : responseProjection hS ν M = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hfc : ∀ x ∈ A, c ≤ f x) (hf0 : ∀ x ∉ A, f x = 0) {a : V → ℝ} (ha : a ∈ stdSimplex ℝ V)
    (haM : ∑ v : V, a v • (v : J → ℝ) = M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂ν, δ * vertexDensity S ν V a x ≤ f x := by
  have ha1 : ∀ v, a v ≤ 1 := fun v ↦ by
    rw [← ha.2]
    exact Finset.single_le_sum (fun w _ ↦ ha.1 w) (Finset.mem_univ v)
  refine exists_pos_mul_le_projection_density hS ν hfin hA hc hf hfc hf0
    (measurable_vertexDensity hS ν V a) (vertexDensity_nonneg ν V hV ha.1)
    (vertexDensity_le ν V hV ha1) (isProbabilityMeasure_vertexLaw hS ν V hV ha) ?_
    (klDiv_vertexLaw_ne_top hS ν V hV ha)
  funext j
  rw [show (ν.withDensity fun x ↦ ENNReal.ofReal (vertexDensity S ν V a x)) = vertexLaw S ν V a
    from rfl, integral_stat_vertexLaw hS ν V hV ha.1, ← haM, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [Pi.smul_apply, smul_eq_mul]

end Vertex

end Laplace.Multi
