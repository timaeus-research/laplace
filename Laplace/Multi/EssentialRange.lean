/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MomentPolytope

/-!
# The essential range of a bounded statistic and the moment body

For a bounded statistic `S : J → X → ℝ` under the prior `π·μ` on a general measurable space, the
**essential range** is the support of the law of `x ↦ (S j x)_j` under the prior (`essRange`), and
the **moment body** is the closed convex hull of the essential range (`momentBody`).

* `ae_statPoint_mem_essRange`: the statistic lies in its essential range almost everywhere (the
  support of a measure on a second-countable space is conull).
* `mean_mem_momentBody`: the mean map lands in the moment body (Hahn–Banach separation and the
  a.e. membership).
* `cap_lemma`: for `x` in the interior of the moment body there are `c, m > 0` such that for
  every unit direction `e` the cap `{⟨e, x − S⟩ ≥ c}` has prior mass at least `m` (a point of the
  essential range far in the direction `−e`, a small ball around it of positive mass, stability
  under perturbing `e` by boundedness of `S`, and compactness of the unit sphere). This is the
  ingredient that replaces the minimal prior weight of the finite alphabet in the coercivity
  argument of `MomentBody`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : Type*} [Fintype J] [Nonempty J]

/-- The prior measure `π·μ`. -/
noncomputable def priorMeasure (μ : Measure X) (π : X → ℝ) : Measure X :=
  μ.withDensity fun x ↦ ENNReal.ofReal (π x)

/-- The essential range of the statistic under the prior: the support of its law. -/
noncomputable def essRange (μ : Measure X) (π : X → ℝ) (S : J → X → ℝ) : Set (J → ℝ) :=
  ((priorMeasure μ π).map (statPoint S)).support

/-- The moment body: the closed convex hull of the essential range. -/
noncomputable def momentBody (μ : Measure X) (π : X → ℝ) (S : J → X → ℝ) : Set (J → ℝ) :=
  closure (convexHull ℝ (essRange μ π S))

omit [Fintype J] [Nonempty J] in
theorem measurable_statPoint {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) :
    Measurable (statPoint S) :=
  measurable_pi_lambda _ fun j ↦ (hS j).1

omit [Fintype J] [Nonempty J] in
theorem isClosed_momentBody (S : J → X → ℝ) : IsClosed (momentBody μ π S) := isClosed_closure

omit [Fintype J] [Nonempty J] in
theorem convex_momentBody (S : J → X → ℝ) : Convex ℝ (momentBody μ π S) :=
  (convex_convexHull ℝ _).closure

omit [Fintype J] [Nonempty J] in
theorem essRange_subset_momentBody (S : J → X → ℝ) : essRange μ π S ⊆ momentBody μ π S :=
  (subset_convexHull ℝ _).trans subset_closure

variable {π : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 < π x) {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hπm hπ hS

omit [Fintype J] [Nonempty J] hS in
/-- The prior measure of a set vanishes iff the set is `μ`-null (positive density). -/
theorem priorMeasure_eq_zero_iff {A : Set X} : priorMeasure μ π A = 0 ↔ μ A = 0 := by
  unfold priorMeasure
  rw [withDensity_apply_eq_zero' (by fun_prop)]
  have : {x | ENNReal.ofReal (π x) ≠ 0} = univ := by
    ext x
    simp [ENNReal.ofReal_eq_zero, not_le, hπ x]
  rw [this, univ_inter]

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The statistic lies in its essential range almost everywhere.** -/
theorem ae_statPoint_mem_essRange : ∀ᵐ x ∂μ, statPoint S x ∈ essRange μ π S := by
  have hm := measurable_statPoint hS
  have h0 : ((priorMeasure μ π).map (statPoint S)) (essRange μ π S)ᶜ = 0 :=
    Measure.measure_compl_support
  unfold essRange at h0 ⊢
  rw [Measure.map_apply hm Measure.isOpen_compl_support.measurableSet,
    priorMeasure_eq_zero_iff hπm hπ] at h0
  rw [ae_iff]
  exact h0

omit [Nonempty J] in
/-- A point of the essential range has positive prior mass in every ball around it. -/
theorem mem_essRange_iff {y : J → ℝ} :
    y ∈ essRange μ π S ↔ ∀ r > 0, 0 < μ (statPoint S ⁻¹' Metric.ball y r) := by
  unfold essRange
  rw [Metric.nhds_basis_ball.mem_measureSupport]
  refine forall_congr' fun r ↦ forall_congr' fun _ ↦ ?_
  rw [Measure.map_apply (measurable_statPoint hS) measurableSet_ball, pos_iff_ne_zero,
    pos_iff_ne_zero, Ne, Ne, priorMeasure_eq_zero_iff hπm hπ]

omit [Fintype J] [Nonempty J] hπm hS in
/-- Positive `μ`-measure means positive prior mass (real integral of `π`). -/
theorem setIntegral_pi_pos (hπi : Integrable π μ) {A : Set X} (hA : 0 < μ A) :
    0 < ∫ x in A, π x ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ (hπ x).le)
    hπi.integrableOn]
  have : Function.support π = univ := by
    ext x; simp [(hπ x).ne']
  rwa [this, univ_inter]

omit [Nonempty J] hπm hπ hS in
theorem continuous_dotJ_right (e : J → ℝ) : Continuous (fun y : J → ℝ ↦ dotJ e y) :=
  continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_apply j)

omit [Nonempty J] hπm hπ hS in
/-- `|⟨e, y⟩| ≤ (∑ |e_j|) ‖y‖`. -/
theorem abs_dotJ_le (e y : J → ℝ) : |dotJ e y| ≤ (∑ j, |e j|) * ‖y‖ := by
  unfold dotJ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm y j))
    (abs_nonneg _)

omit [Nonempty J] hπm hπ hS in
/-- On the unit sphere of the sup norm, `∑ |e_j| ≥ 1`. -/
theorem one_le_sum_abs_of_norm_eq_one {e : J → ℝ} (he : ‖e‖ = 1) : 1 ≤ ∑ j, |e j| := by
  rw [← he]
  exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)).2 fun j ↦ by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j ↦ |e j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)

omit [Nonempty J] hπm hπ hS in
theorem sum_abs_le_card_of_norm_le_one {e : J → ℝ} (he : ‖e‖ ≤ 1) :
    ∑ j, |e j| ≤ Fintype.card J := by
  calc ∑ j, |e j| ≤ ∑ _j : J, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ by
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm e j).trans he
    _ = Fintype.card J := by simp

omit [Nonempty J] hπm hπ hS in
/-- **A far point of the essential range in every direction**: for `x` interior and `‖e‖ = 1`
there is `y₀` in the essential range with `⟨e, x − y₀⟩ ≥ δ/2`, where `ball x δ ⊆ momentBody`. -/
theorem exists_far_point {x : J → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball x δ ⊆ momentBody μ π S) {e : J → ℝ} (he : ‖e‖ = 1) :
    ∃ y₀ ∈ essRange μ π S, δ / 2 ≤ dotJ e (x - y₀) := by
  classical
  by_contra h
  push Not at h
  have hlin := isLinearMap_dotJ e
  set H : Set (J → ℝ) := {y | dotJ e x - δ / 2 ≤ dotJ e y} with hH
  have hsub : essRange μ π S ⊆ H := fun y hy ↦ by
    have := h y hy
    rw [hlin.map_sub] at this
    change dotJ e x - δ / 2 ≤ dotJ e y
    linarith
  have hconv : Convex ℝ H := convex_halfSpace_ge hlin _
  have hclosed : IsClosed H := isClosed_le continuous_const (continuous_dotJ_right e)
  have hC : momentBody μ π S ⊆ H := closure_minimal (convexHull_min hsub hconv) hclosed
  -- the test point `z = x − (3δ/4) u`, `u = sign e` coordinatewise
  set u : J → ℝ := fun j ↦ if 0 ≤ e j then 1 else -1 with hu
  have hu1 : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ by
    simp only [hu, Real.norm_eq_abs]
    split_ifs <;> simp
  have hz : x - (3 * δ / 4) • u ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    nlinarith
  have hzH := hC (hball hz)
  have hdot : dotJ e ((3 * δ / 4) • u) = 3 * δ / 4 * ∑ j, |e j| := by
    rw [hlin.map_smul, smul_eq_mul]
    congr 1
    simp only [dotJ, hu]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with hj
    · rw [abs_of_nonneg hj]; ring
    · rw [abs_of_neg (not_le.1 hj)]; ring
  have hone := one_le_sum_abs_of_norm_eq_one (J := J) he
  have : dotJ e x - δ / 2 ≤ dotJ e (x - (3 * δ / 4) • u) := hzH
  rw [hlin.map_sub, hdot] at this
  nlinarith

/-- **The cap lemma**: for `x` in the interior of the moment body there are `c, m > 0` such that
every unit direction `e` has a cap `{⟨e, x − S⟩ ≥ c}` of prior mass at least `m`. -/
theorem cap_lemma (hπi : Integrable π μ) {x : J → ℝ} (hx : x ∈ interior (momentBody μ π S)) :
    ∃ c > 0, ∃ m > 0, ∀ e : J → ℝ, ‖e‖ = 1 →
      m ≤ ∫ y in {y | c ≤ dotJ e (x - statPoint S y)}, π y ∂μ := by
  classical
  -- a uniform bound on the statistic
  obtain ⟨K, hK0, hK⟩ : ∃ K, 0 ≤ K ∧ ∀ j y, |S j y| ≤ K := by
    choose M hM using fun j ↦ (hS j).2
    refine ⟨∑ j, |M j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j y ↦ (hM j y).trans ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |M j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))
  have hSx : ∀ y, ‖x - statPoint S y‖ ≤ ‖x‖ + K := fun y ↦
    (norm_sub_le _ _).trans (add_le_add le_rfl ((pi_norm_le_iff_of_nonneg hK0).2 fun j ↦ by
      rw [Real.norm_eq_abs]; exact hK j y))
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨δ, hδ, hball⟩ := hx
  set n : ℝ := (Fintype.card J : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set r : ℝ := δ / (4 * n) with hr
  have hr0 : 0 < r := by positivity
  set ρ : ℝ := δ / (8 * n * (‖x‖ + K + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  -- Step 2/3: for each unit `e` a far point and its small ball
  have far : ∀ e ∈ Metric.sphere (0 : J → ℝ) 1, ∃ y₀ ∈ essRange μ π S, δ / 2 ≤ dotJ e (x - y₀) :=
    fun e he ↦ exists_far_point hδ hball (mem_sphere_zero_iff_norm.1 he)
  choose! y₀ hy₀ hfar using far
  -- the cap of a nearby direction contains the small ball around `y₀ e`
  have hcap : ∀ e ∈ Metric.sphere (0 : J → ℝ) 1, ∀ e' ∈ Metric.ball e ρ, ∀ y,
      statPoint S y ∈ Metric.ball (y₀ e) r → δ / 8 ≤ dotJ e' (x - statPoint S y) := by
    intro e he e' he' y hy
    have hlin := isLinearMap_dotJ e
    have he1 : ‖e‖ = 1 := mem_sphere_zero_iff_norm.1 he
    have hee' : ‖e' - e‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at he'
    have hyr : ‖statPoint S y - y₀ e‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    -- `⟨e, x − S y⟩ ≥ δ/2 − n r = δ/4`
    have h1 : δ / 4 ≤ dotJ e (x - statPoint S y) := by
      have e1 : dotJ e (x - statPoint S y) = dotJ e (x - y₀ e) - dotJ e (statPoint S y - y₀ e) := by
        rw [← hlin.map_sub]; congr 1; abel
      have h2 : |dotJ e (statPoint S y - y₀ e)| ≤ n * r := by
        refine (abs_dotJ_le _ _).trans ?_
        exact mul_le_mul (sum_abs_le_card_of_norm_le_one he1.le) hyr.le (norm_nonneg _) hnpos.le
      have h3 : n * r = δ / 4 := by rw [hr]; field_simp
      have := hfar e he
      rw [e1]
      have := abs_le.1 h2
      linarith
    -- perturbing the direction costs at most `n ρ (‖x‖ + K) ≤ δ/8`
    have h4 : |dotJ (e' - e) (x - statPoint S y)| ≤ n * ρ * (‖x‖ + K) := by
      refine (abs_dotJ_le _ _).trans ?_
      have : ∑ j, |(e' - e) j| ≤ n * ρ := by
        calc ∑ j, |(e' - e) j| ≤ ∑ _j : J, ρ := Finset.sum_le_sum fun j _ ↦ by
              rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (e' - e) j).trans hee'.le
          _ = n * ρ := by simp [hn]
      exact mul_le_mul this (hSx y) (norm_nonneg _) (by positivity)
    have h5 : n * ρ * (‖x‖ + K) ≤ δ / 8 := by
      rw [hρ]
      have hpos : 0 < ‖x‖ + K + 1 := by positivity
      have e3 : n * (δ / (8 * n * (‖x‖ + K + 1))) * (‖x‖ + K) =
          δ / 8 * ((‖x‖ + K) / (‖x‖ + K + 1)) := by
        field_simp
      rw [e3]
      have : (‖x‖ + K) / (‖x‖ + K + 1) ≤ 1 := by
        rw [div_le_one hpos]; linarith
      nlinarith
    have e2 : dotJ e' (x - statPoint S y) =
        dotJ e (x - statPoint S y) + dotJ (e' - e) (x - statPoint S y) := by
      simp only [dotJ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
    have := abs_le.1 h4
    rw [e2]
    linarith
  -- Step 5: compactness of the unit sphere
  have hcompact : IsCompact (Metric.sphere (0 : J → ℝ) 1) := isCompact_sphere 0 1
  obtain ⟨t, ht⟩ := hcompact.elim_nhds_subcover' (fun e _ ↦ Metric.ball e ρ)
    fun e _ ↦ Metric.ball_mem_nhds e hρ0
  -- the masses of the small balls
  set mass : (J → ℝ) → ℝ := fun e ↦ ∫ y in statPoint S ⁻¹' Metric.ball (y₀ e) r, π y ∂μ
    with hmass
  have hmass_pos : ∀ e ∈ Metric.sphere (0 : J → ℝ) 1, 0 < mass e := fun e he ↦
    setIntegral_pi_pos hπ hπi
      ((mem_essRange_iff hπm hπ hS).1 (hy₀ e he) r hr0)
  -- the sphere is nonempty, hence so is the finite subcover
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have hsph : (Pi.single j₀ (1 : ℝ) : J → ℝ) ∈ Metric.sphere (0 : J → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, Pi.norm_single, norm_one]
  have htne : t.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have := ht hsph
    simp [hemp] at this
  refine ⟨δ / 8, by positivity, t.inf' htne (fun e ↦ mass (e : J → ℝ)), ?_, fun e' he' ↦ ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun e _ ↦ hmass_pos (e : J → ℝ) e.2
  · obtain ⟨e, het, he'e⟩ : ∃ e ∈ t, e' ∈ Metric.ball (e : J → ℝ) ρ := by
      have := ht (mem_sphere_zero_iff_norm.2 he')
      simpa using this
    calc t.inf' htne (fun e ↦ mass (e : J → ℝ)) ≤ mass (e : J → ℝ) := Finset.inf'_le _ het
      _ ≤ ∫ y in {y | δ / 8 ≤ dotJ e' (x - statPoint S y)}, π y ∂μ := by
          refine setIntegral_mono_set hπi.integrableOn
            (Filter.Eventually.of_forall fun y ↦ (hπ y).le)
            (Filter.Eventually.of_forall fun y hy ↦ hcap e e.2 e' he'e y hy)

end

end Laplace.Multi
