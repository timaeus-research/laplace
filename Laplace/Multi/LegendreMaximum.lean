/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DualPotential
import Laplace.Multi.AffinityKL

/-!
# The Legendre identity and constrained entropy minimisation

* **The Legendre identity on the response space.** The dual objective `θ ↦ −t⟨θ, m(a₀)⟩ − A(θ)` is
  maximal at `θ = a₀` (`dual_objective_le_at_mean`, `legendre_isMaxOn_aff`), so the dual potential
  of `DualPotential` is the Legendre transform of the free energy evaluated at the realised
  response:
  `I(m(a₀)) = sup_θ (−t⟨θ, m(a₀)⟩ − A(θ))`. Under nondegeneracy the maximiser is unique
  (`eq_of_isMaxOn_dual_objective`).
* **Constrained entropy minimisation.** For every probability density `q` (w.r.t. `μ`) whose
  contrast means agree with those of `P_a`,
  `KL(q ‖ P_0) = KL(q ‖ P_a) + I(m(a)) + A(0)` (`relEnt_eq_relEnt_gibbs_add`), hence
  `I(m(a)) + A(0) ≤ KL(q ‖ P_0)` with `P_a` the minimiser (`dual_add_le_relEnt`): the response chart
  assigns to each response the least-informative distribution realising it. This extends the
  family-internal Pythagoras theorem of `SegmentDivergence` to all admissible distributions, and it
  identifies `I` (normalised by `A(0)`) as the entropy cost of a response.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Legendre

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit ht in
/-- **The tangent inequality of the free energy at a realised response**:
`−t⟨θ, m(a₀)⟩ − A(θ) ≤ −t⟨a₀, m(a₀)⟩ − A(a₀)`. -/
theorem dual_objective_le_at_mean (a₀ θ : ι → ℝ) :
    -t * dotJ θ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t θ ≤
      -t * dotJ a₀ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t a₀ := by
  obtain ⟨M, hT⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR a₀ (θ - a₀) t
  have hconv := hT.mixLogZ_convexOn
  have hd := hT.hasDerivAt_mixLogZ 0
  have h := hconv.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ 1) zero_lt_one hd
  rw [slope_def_field, sub_zero, div_one, mixExp_zero_eq_dot hR a₀ θ hT.ν_int] at h
  simp only [affLogZ_line, one_smul, zero_smul, add_zero, add_sub_cancel] at h
  unfold dotJ
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum] at h ⊢
  linarith

omit ht in
/-- **The Legendre identity**: the dual objective at the response `m(a₀)` is maximal at `θ = a₀`. -/
theorem legendre_isMaxOn_aff (a₀ : ι → ℝ) :
    IsMaxOn (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t θ) univ a₀ :=
  fun θ _ ↦ dual_objective_le_at_mean hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a₀ θ

/-- The maximiser of the dual objective is unique under nondegeneracy. -/
theorem eq_of_isMaxOn_dual_objective
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ θ : ι → ℝ)
    (hmax : IsMaxOn (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t θ) univ θ) :
    θ = a₀ := by
  classical
  -- first-order condition: `m(θ) = m(a₀)`
  have hlin : HasFDerivAt (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀))
      ((-t) • dotCLM (meanMap μ π L₀ R t a₀)) θ := by
    have h := (dotCLM (meanMap μ π L₀ R t a₀)).hasFDerivAt (x := θ)
    have e : (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀)) =
        fun θ ↦ -t * dotCLM (meanMap μ π L₀ R t a₀) θ := by
      funext θ; rw [dotCLM_apply]
    rw [e]
    exact h.const_mul (-t)
  have hF := hlin.sub (hasFDerivAt_affLogZ hπm hπi hπ hπpos hL₀m hL₀ hR ht θ)
  have hloc : IsLocalMax (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t θ) θ :=
    Filter.Eventually.of_forall fun ϑ ↦ hmax (mem_univ ϑ)
  have h0 := hloc.hasFDerivAt_eq_zero hF
  have hmean : meanMap μ π L₀ R t θ = meanMap μ π L₀ R t a₀ := by
    funext j
    have := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ ↦ L (Pi.single j 1)) h0
    simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      dotCLM_apply, _root_.zero_apply] at this
    rw [dotJ_single_left, dotJ_single_left] at this
    have h1 : (-t) * (meanMap μ π L₀ R t a₀ j - meanMap μ π L₀ R t θ j) = 0 := by linarith
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (by linarith)
    · linarith
  exact meanMap_injective hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hmean

/-- **The dual potential is the Legendre transform at the realised response.** -/
theorem dualPotential_isMaxOn
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a₀ : ι → ℝ) :
    IsMaxOn (fun θ ↦ -t * dotJ θ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t θ) univ a₀ ∧
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t a₀) =
        -t * dotJ a₀ (meanMap μ π L₀ R t a₀) - affLogZ μ π L₀ R t a₀ :=
  ⟨legendre_isMaxOn_aff hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a₀,
    dualPotential_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀⟩

end Legendre

section Entropy

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem affLoss_zero_eq (x : X) : affLoss L₀ R 0 x = L₀ x := by simp [affLoss]

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem affLoss_sub_affLoss_zero (a : ι → ℝ) (x : X) :
    affLoss L₀ R a x - affLoss L₀ R 0 x = dirLoss R a x := by
  simp [affLoss, dirLoss]

omit [Nonempty X] in
/-- `log (p_a / p_0) = −t R_a − A(a) + A(0)` pointwise. -/
theorem log_gibbsDensity_div_zero (a : ι → ℝ) (x : X) :
    Real.log (gibbsDensity μ π (affLoss L₀ R a) t x / gibbsDensity μ π (affLoss L₀ R 0) t x) =
      -t * dirLoss R a x - affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t 0 := by
  have hZa := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hZ0 := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  rw [Real.log_div (gibbsDensity_pos (fun x ↦ (hπ x).le) hZa (hπ x).ne').ne'
    (gibbsDensity_pos (fun x ↦ (hπ x).le) hZ0 (hπ x).ne').ne', log_gibbsDensity_eq hπ hZa,
    log_gibbsDensity_eq hπ hZ0]
  unfold affLogZ
  have := affLoss_sub_affLoss_zero (L₀ := L₀) (R := R) a x
  linarith [congrArg (fun y ↦ t * y) this]

omit [Nonempty X] in
/-- **Constrained entropy identity**: for a probability density `q` with the contrast means of
`P_a`, `KL(q ‖ P_0) = KL(q ‖ P_a) + (−t⟨a, m(a)⟩ − A(a) + A(0))`. -/
theorem relEnt_eq_relEnt_gibbs_add (a : ι → ℝ) {q : X → ℝ}
    (hq1 : ∫ x, q x ∂μ = 1) (hqi : Integrable q μ)
    (hmean : ∀ i, ∫ x, q x * R i x ∂μ = meanMap μ π L₀ R t a i)
    (hint : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ) :
    relEnt μ q (gibbsDensity μ π (affLoss L₀ R 0) t) =
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R a) t) +
        (-t * dotJ a (meanMap μ π L₀ R t a) - affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t 0) := by
  have hZa := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hZ0 := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  -- the pointwise identity
  have hpt : ∀ x, q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R 0) t x) =
      q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x) +
        q x * (-t * dirLoss R a x - affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t 0) := by
    intro x
    by_cases hq : q x = 0
    · simp [hq]
    · have hga := (gibbsDensity_pos (fun x ↦ (hπ x).le) hZa (hπ x).ne' (x := x)).ne'
      have hg0 := (gibbsDensity_pos (fun x ↦ (hπ x).le) hZ0 (hπ x).ne' (x := x)).ne'
      rw [← log_gibbsDensity_div_zero hπm hπi hπ hπpos hL₀m hL₀ hR a x, ← mul_add,
        Real.log_div hq hg0, Real.log_div hq hga, Real.log_div hga hg0]
      ring
  -- integrability of the affine term
  obtain ⟨ham, Ma, hab⟩ := bdd_dirLoss hR a
  have hqR : Integrable (fun x ↦ q x * dirLoss R a x) μ := by
    have := hqi.bdd_mul ham.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hab x))
    exact this.congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
  have haff : Integrable (fun x ↦ q x * (-t * dirLoss R a x - affLogZ μ π L₀ R t a +
      affLogZ μ π L₀ R t 0)) μ := by
    have := (hqR.const_mul (-t)).sub (hqi.const_mul (affLogZ μ π L₀ R t a)) |>.add
      (hqi.const_mul (affLogZ μ π L₀ R t 0))
    exact this.congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [Pi.add_apply, Pi.sub_apply]; ring)
  -- integrate
  unfold relEnt
  simp_rw [hpt]
  rw [integral_add hint haff]
  congr 1
  have e : (fun x ↦ q x * (-t * dirLoss R a x - affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t 0)) =
      fun x ↦ -t * (q x * dirLoss R a x) - affLogZ μ π L₀ R t a * q x +
        affLogZ μ π L₀ R t 0 * q x := by
    funext x; ring
  have h3 : Integrable (fun x ↦ -t * (q x * dirLoss R a x)) μ := hqR.const_mul _
  have h4 : Integrable (fun x ↦ affLogZ μ π L₀ R t a * q x) μ := hqi.const_mul _
  have h1 : Integrable (fun x ↦ -t * (q x * dirLoss R a x) - affLogZ μ π L₀ R t a * q x) μ :=
    h3.sub h4
  have h2 : Integrable (fun x ↦ affLogZ μ π L₀ R t 0 * q x) μ := hqi.const_mul _
  rw [e, integral_add h1 h2, integral_sub h3 h4, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hq1]
  have hsum : (∫ x, q x * dirLoss R a x ∂μ) = dotJ a (meanMap μ π L₀ R t a) := by
    have e2 : (fun x ↦ q x * dirLoss R a x) = fun x ↦ ∑ i, a i * (q x * R i x) := by
      funext x; simp only [dirLoss, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e2, integral_finsetSum _ fun i _ ↦ ?_]
    · unfold dotJ
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [MeasureTheory.integral_const_mul, hmean i]
    · have := hqi.bdd_mul (hR i).1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le ((hR i).2.choose_spec x))
      exact (this.congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)).const_mul _
  rw [hsum]
  ring

omit [Nonempty X] in
/-- **Constrained entropy minimisation**: among all probability densities with the contrast means
of `P_a`, the family member `P_a` minimises the relative entropy to the prior `P_0`, and the minimum
is the dual potential: `−t⟨a, m(a)⟩ − A(a) + A(0) ≤ KL(q ‖ P_0)`. -/
theorem dual_add_le_relEnt (a : ι → ℝ) {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∫ x, q x ∂μ = 1) (hqi : Integrable q μ)
    (hmean : ∀ i, ∫ x, q x * R i x ∂μ = meanMap μ π L₀ R t a i)
    (hint : Integrable (fun x ↦ q x * Real.log (q x / gibbsDensity μ π (affLoss L₀ R a) t x)) μ) :
    -t * dotJ a (meanMap μ π L₀ R t a) - affLogZ μ π L₀ R t a + affLogZ μ π L₀ R t 0 ≤
      relEnt μ q (gibbsDensity μ π (affLoss L₀ R 0) t) := by
  rw [relEnt_eq_relEnt_gibbs_add hπm hπi hπ hπpos hL₀m hL₀ hR a hq1 hqi hmean hint]
  have hZa := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hZint : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have := relEnt_gibbsDensity_nonneg (μ := μ) (fun x ↦ (hπ x).le) hZa hZint hq0
    (fun x _ ↦ (hπ x).ne') hq1 hqi hint
  linarith

end Entropy

end Laplace.Multi
