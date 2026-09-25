/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.NullFace
import Laplace.Multi.MeanJourney

/-!
# The boundary-barrier criterion

The extended Cramér rate `𝓘 = rateFun` of the empirical response is finite on the response space
`interior K` (`rateFun_meanMap`), infinite off the moment body `K` (`rateFun_eq_top_of_not_mem`),
and lower semicontinuous. This file settles its behaviour **on the boundary** `∂K`.

* **Compactness.** The moment body of a bounded statistic is compact (`isCompact_momentBody`), and
  it lies in every closed half-space that contains the statistic almost surely
  (`momentBody_subset_halfspace`).
* **Supporting directions.** Every point outside the (nonempty) interior of the convex body `K` has
  a nonzero direction `u` with `u·y ≤ u·M` on `K` (`exists_supporting_direction`, Hahn–Banach).
* **The criterion.** If every supporting face `{u·R = β}` (`u ≠ 0`, `u·R ≤ β` a.s.) is `μ`-null,
  the rate is `+∞` on the whole boundary (`rateFun_eq_top_of_mem_frontier`), hence everywhere off
  the interior (`rateFun_eq_top_of_not_mem_interior`). Conversely a positive-mass supporting face
  puts a boundary point of finite rate at its conditional mean (`exists_frontier_rateFun_lt_top`):
  `rateFun_frontier_eq_top_iff`.
* **Uniform blow-up.** Boundary infinity makes every finite sublevel set a compact subset of the
  interior (`isCompact_rateFun_sublevel`, `rateFun_sublevel_subset_interior`), so the rate exceeds
  any threshold within a positive distance of the boundary
  (`exists_pos_forall_infDist_lt_imp_lt_rateFun`) and tends to `⊤` along every family of points
  whose distance to the boundary tends to zero (`tendsto_rateFun_nhds_top`).

No compactness of the unit sphere is needed: compactness of the moment body and lower
semicontinuity do all the uniformity work.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Body

variable {π : X → ℝ} {R : ι → X → ℝ}

/-- **A supporting direction at every point outside the interior** of the moment body (assumed to
have nonempty interior): `u ≠ 0` with `u·y ≤ u·M` for all `y ∈ K`. -/
theorem exists_supporting_direction (hint : (interior (momentBody μ π R)).Nonempty) {M : ι → ℝ}
    (hMi : M ∉ interior (momentBody μ π R)) :
    ∃ u : ι → ℝ, u ≠ 0 ∧ ∀ y ∈ momentBody μ π R, dotJ u y ≤ dotJ u M := by
  classical
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_momentBody R).interior
    isOpen_interior hMi
  set u : ι → ℝ := fun j ↦ f (Pi.single j 1) with hu
  have hfu : ∀ y : ι → ℝ, f y = dotJ u y := fun y ↦ by
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨u, fun h0 ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hint
    have h := hf a ha
    rw [hfu, hfu, h0, dotJ_zero_left, dotJ_zero_left] at h
    exact lt_irrefl _ h
  · have hy' : y ∈ closure (interior (momentBody μ π R)) := by
      rw [(convex_momentBody R).closure_interior_eq_closure_of_nonempty_interior hint,
        (isClosed_momentBody R).closure_eq]
      exact hy
    rw [← hfu, ← hfu]
    exact closure_minimal (t := {z : ι → ℝ | f z ≤ f M}) (fun a ha ↦ (hf a ha).le)
      (isClosed_le f.continuous continuous_const) hy'

variable (hπm : Measurable π) (hπ : ∀ x, 0 < π x) (hR : ∀ i, Bdd (R i))
include hπm hπ hR

/-- The essential range of a bounded statistic lies in a closed ball. -/
theorem essRange_subset_closedBall : ∃ r : ℝ, essRange μ π R ⊆ Metric.closedBall 0 r := by
  choose M hM using fun i ↦ (hR i).2
  refine ⟨∑ i, |M i|, fun y hy ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hbound : ∀ x, ‖statPoint R x‖ ≤ ∑ i, |M i| := fun x ↦ by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact (hM i x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j ↦ |M j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [mem_essRange_iff hπm hπ hR] at hy
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hy ε hε).ne'
  have hx' : dist (statPoint R x) y < ε := Metric.mem_ball.1 hx
  have h1 := norm_sub_norm_le y (statPoint R x)
  rw [← dist_eq_norm, dist_comm] at h1
  linarith [hbound x]

/-- The moment body of a bounded statistic lies in a closed ball. -/
theorem momentBody_subset_closedBall : ∃ r : ℝ, momentBody μ π R ⊆ Metric.closedBall 0 r := by
  obtain ⟨r, hr⟩ := essRange_subset_closedBall hπm hπ hR
  exact ⟨r, closure_minimal (convexHull_min hr (convex_closedBall 0 r)) Metric.isClosed_closedBall⟩

set_option linter.unusedFintypeInType false in
/-- **The moment body of a bounded statistic is compact.** -/
theorem isCompact_momentBody : IsCompact (momentBody μ π R) := by
  obtain ⟨r, hr⟩ := momentBody_subset_closedBall hπm hπ hR
  exact (isCompact_closedBall (0 : ι → ℝ) r).of_isClosed_subset (isClosed_momentBody R) hr

/-- **An almost-sure half-space bound on the statistic contains the moment body.** -/
theorem momentBody_subset_halfspace {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β) :
    momentBody μ π R ⊆ {y | dotJ u y ≤ β} := by
  have hclosed : IsClosed {y : ι → ℝ | dotJ u y ≤ β} :=
    isClosed_le (continuous_dotJ_right u) continuous_const
  refine closure_minimal (convexHull_min ?_ (convex_halfSpace_le (isLinearMap_dotJ u) β)) hclosed
  intro y hy
  by_contra hcon
  have hopen : IsOpen {z : ι → ℝ | β < dotJ u z} :=
    isOpen_lt continuous_const (continuous_dotJ_right u)
  have hmem : β < dotJ u y := not_le.1 hcon
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen y hmem
  rw [mem_essRange_iff hπm hπ hR] at hy
  refine (hy ε hε).ne' (measure_mono_null (fun x hx ↦ ?_) (ae_iff.1 hβ))
  have h1 : β < dotJ u (statPoint R x) := hball hx
  have e : dotJ u (statPoint R x) = dirLoss R u x := rfl
  rw [e] at h1
  exact not_le.2 h1

end Body

section Family

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] ht in
/-- A family member has the same null sets as the base measure (positive density). -/
theorem familyMeasure_eq_zero_iff (a : ι → ℝ) {A : Set X} :
    familyMeasure μ π L₀ R t a A = 0 ↔ μ A = 0 := by
  have hZ := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  unfold familyMeasure
  rw [withDensity_apply_eq_zero' (measurable_familyDensity hπm hL₀m hL₀ hR a).aemeasurable]
  have : {x | ENNReal.ofReal (Real.exp (-(t * affLoss L₀ R a x)) * π x /
      priorZ μ π (affLoss L₀ R a) t) ≠ 0} = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    change ENNReal.ofReal _ ≠ 0
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (mul_pos (Real.exp_pos _) (hπ x)) hZ
  rw [this, univ_inter]

omit ht in
/-- A `μ`-non-null set has positive mass under every family member. -/
theorem familyMeasure_real_pos_of_ne_zero (a : ι → ℝ) {A : Set X} (hA : μ A ≠ 0) :
    0 < (familyMeasure μ π L₀ R t a).real A := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  exact ENNReal.toReal_pos ((familyMeasure_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR (t := t)
    a).not.2 hA) (measure_ne_top _ _)

/-- **Null supporting faces force an infinite rate on the whole boundary.** -/
theorem rateFun_eq_top_of_mem_frontier [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (hnull : ∀ u : ι → ℝ, u ≠ 0 → ∀ β : ℝ, (∀ᵐ x ∂μ, dirLoss R u x ≤ β) →
      μ {x | dirLoss R u x = β} = 0)
    {M : ι → ℝ} (hM : M ∈ frontier (momentBody μ π R)) : rateFun μ π L₀ R t M = ⊤ := by
  rw [(isClosed_momentBody R).frontier_eq] at hM
  obtain ⟨u, hu, hsup⟩ := exists_supporting_direction
    ⟨_, meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0⟩ hM.2
  have hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ dotJ u M := by
    filter_upwards [ae_statPoint_mem_essRange hπm hπ hR] with x hx
    exact hsup _ (essRange_subset_momentBody R hx)
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hac : familyMeasure μ π L₀ R t 0 ≪ μ := withDensity_absolutelyContinuous _ _
  exact genRate_eq_top_of_null_face (familyMeasure μ π L₀ R t 0) hR (hac hβ)
    (hac (hnull u hu _ hβ)) rfl

/-- Under null supporting faces the rate is infinite everywhere off the response space. -/
theorem rateFun_eq_top_of_not_mem_interior [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (hnull : ∀ u : ι → ℝ, u ≠ 0 → ∀ β : ℝ, (∀ᵐ x ∂μ, dirLoss R u x ≤ β) →
      μ {x | dirLoss R u x = β} = 0)
    {M : ι → ℝ} (hM : M ∉ interior (momentBody μ π R)) : rateFun μ π L₀ R t M = ⊤ := by
  by_cases hK : M ∈ momentBody μ π R
  · refine rateFun_eq_top_of_mem_frontier hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hnull ?_
    rw [(isClosed_momentBody R).frontier_eq]
    exact ⟨hK, hM⟩
  · exact rateFun_eq_top_of_not_mem hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hK

omit ht in
/-- **A positive supporting face puts a boundary point of finite rate at its conditional mean.** -/
theorem exists_frontier_rateFun_lt_top [Nonempty ι] {u : ι → ℝ} (hu : u ≠ 0) {β : ℝ}
    (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β) (hp : μ {x | dirLoss R u x = β} ≠ 0) :
    ∃ M ∈ frontier (momentBody μ π R), rateFun μ π L₀ R t M < ⊤ := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hac : familyMeasure μ π L₀ R t 0 ≪ μ := withDensity_absolutelyContinuous _ _
  have hQp : 0 < (familyMeasure μ π L₀ R t 0).real {x | dirLoss R u x = β} :=
    familyMeasure_real_pos_of_ne_zero hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0 hp
  obtain ⟨M, hMdef⟩ : ∃ M : ι → ℝ, M = fun i ↦
      ∫ x, R i x ∂faceMeasure (familyMeasure μ π L₀ R t 0) {x | dirLoss R u x = β} := ⟨_, rfl⟩
  have hrate : rateFun μ π L₀ R t M = ENNReal.ofReal
      (-Real.log ((familyMeasure μ π L₀ R t 0).real {x | dirLoss R u x = β})) := by
    rw [hMdef]
    exact genRate_condMean (familyMeasure μ π L₀ R t 0) hR (hac hβ) hQp
  have hlt : rateFun μ π L₀ R t M < ⊤ := by
    rw [hrate]
    exact ENNReal.ofReal_lt_top
  have hMK : M ∈ momentBody μ π R := by
    by_contra h
    exact hlt.ne (rateFun_eq_top_of_not_mem hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) h)
  have hMβ : dotJ u M = β := by
    rw [hMdef]
    exact dotJ_condMean (familyMeasure μ π L₀ R t 0) hR hQp
  refine ⟨M, ?_, hlt⟩
  rw [(isClosed_momentBody R).frontier_eq]
  refine ⟨hMK, fun hMi ↦ ?_⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hMi
  obtain ⟨ε, hε, hball⟩ := hMi
  have hnorm : 0 < dotJ u u := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hu
    exact Finset.sum_pos' (fun i _ ↦ mul_self_nonneg _)
      ⟨j, Finset.mem_univ _, mul_self_pos.2 hj⟩
  have hu1 : 0 < ‖u‖ + 1 := by positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ε / (2 * (‖u‖ + 1)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcu : c * (‖u‖ + 1) = ε / 2 := by
    rw [hcdef, div_mul_eq_mul_div, mul_div_mul_right _ _ hu1.ne']
  have hd : dist (M + c • u) M < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc c * ‖u‖ ≤ c * (‖u‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = ε / 2 := hcu
      _ < ε := by linarith
  have h1 : dotJ u (M + c • u) ≤ β :=
    momentBody_subset_halfspace hπm hπ hR hβ (hball (Metric.mem_ball.2 hd))
  rw [(isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul, smul_eq_mul, hMβ] at h1
  nlinarith [mul_pos hc hnorm]

/-- **The boundary-barrier criterion**: the rate is infinite on the whole boundary of the moment
body iff every supporting face is null. -/
theorem rateFun_frontier_eq_top_iff [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) :
    (∀ M ∈ frontier (momentBody μ π R), rateFun μ π L₀ R t M = ⊤) ↔
      ∀ u : ι → ℝ, u ≠ 0 → ∀ β : ℝ, (∀ᵐ x ∂μ, dirLoss R u x ≤ β) →
        μ {x | dirLoss R u x = β} = 0 := by
  refine ⟨fun hbar u hu β hβ ↦ ?_, fun hnull M hM ↦
    rateFun_eq_top_of_mem_frontier hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hnull hM⟩
  by_contra hp
  obtain ⟨M, hM, hlt⟩ :=
    exists_frontier_rateFun_lt_top hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hu hβ hp
  exact hlt.ne (hbar M hM)

/-- The moment body has nonempty boundary. -/
theorem frontier_momentBody_nonempty [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) :
    (frontier (momentBody μ π R)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
  rcases h with h | h
  · have hm := interior_subset (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0)
    rw [h] at hm
    exact (Set.mem_empty_iff_false _).1 hm
  · have hK := isCompact_momentBody (μ := μ) hπm hπ hR
    rw [h] at hK
    exact noncompact_univ (ι → ℝ) hK

omit ht in
/-- Finite sublevel sets of the rate are compact. -/
theorem isCompact_rateFun_sublevel [Nonempty ι] {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    IsCompact {M | rateFun μ π L₀ R t M ≤ B} := by
  refine (isCompact_momentBody (μ := μ) hπm hπ hR).of_isClosed_subset
    ((lowerSemicontinuous_rateFun (μ := μ) (π := π) (L₀ := L₀) (R := R) (t := t)).isClosed_preimage
      B) fun M hM ↦ ?_
  have hM' : rateFun μ π L₀ R t M ≤ B := hM
  by_contra hK
  rw [rateFun_eq_top_of_not_mem hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hK] at hM'
  exact hB (top_le_iff.1 hM')

omit ht in
/-- Under boundary infinity the finite sublevel sets lie in the response space. -/
theorem rateFun_sublevel_subset_interior [Nonempty ι]
    (hbar : ∀ M ∈ frontier (momentBody μ π R), rateFun μ π L₀ R t M = ⊤) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) : {M | rateFun μ π L₀ R t M ≤ B} ⊆ interior (momentBody μ π R) := by
  intro M hM
  have hM' : rateFun μ π L₀ R t M ≤ B := hM
  by_contra hMi
  have hK : M ∈ momentBody μ π R := by
    by_contra hK
    rw [rateFun_eq_top_of_not_mem hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hK] at hM'
    exact hB (top_le_iff.1 hM')
  have hfr : M ∈ frontier (momentBody μ π R) := by
    rw [(isClosed_momentBody R).frontier_eq]
    exact ⟨hK, hMi⟩
  rw [hbar M hfr] at hM'
  exact hB (top_le_iff.1 hM')

/-- **Uniform blow-up**: under boundary infinity, every threshold is exceeded within a positive
distance of the boundary. -/
theorem exists_pos_forall_infDist_lt_imp_lt_rateFun [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (hbar : ∀ M ∈ frontier (momentBody μ π R), rateFun μ π L₀ R t M = ⊤) (B : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ι → ℝ, Metric.infDist M (frontier (momentBody μ π R)) < δ →
      (B : ℝ≥0∞) < rateFun μ π L₀ R t M := by
  have hCc := isCompact_rateFun_sublevel hπm hπi hπ hπpos hL₀m hL₀ hR (t := t)
    (B := B) ENNReal.coe_ne_top
  have hCi := rateFun_sublevel_subset_interior hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hbar
    (B := B) ENNReal.coe_ne_top
  have hfr := frontier_momentBody_nonempty hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
  have hpos : ∀ M ∈ {M | rateFun μ π L₀ R t M ≤ B},
      0 < Metric.infDist M (frontier (momentBody μ π R)) := fun M hM ↦ by
    rw [← Metric.infDist_pos_iff_notMem_closure hfr, isClosed_frontier.closure_eq]
    exact Set.disjoint_left.1 disjoint_interior_frontier (hCi hM)
  rcases Set.eq_empty_or_nonempty {M | rateFun μ π L₀ R t M ≤ B} with hemp | hne
  · refine ⟨1, one_pos, fun M _ ↦ not_le.1 fun hle ↦ ?_⟩
    have : M ∈ {M | rateFun μ π L₀ R t M ≤ B} := hle
    rw [hemp] at this
    exact (Set.mem_empty_iff_false _).1 this
  · obtain ⟨M₀, hM₀, hmin⟩ := hCc.exists_isMinOn hne
      (Metric.continuous_infDist_pt (frontier (momentBody μ π R))).continuousOn
    refine ⟨_, hpos M₀ hM₀, fun M hM ↦ not_le.1 fun hle ↦ ?_⟩
    exact hM.not_ge (isMinOn_iff.1 hmin M hle)

/-- **The rate tends to `⊤` along any family approaching the boundary** (target `𝓝 ⊤`, not
`atTop`). -/
theorem tendsto_rateFun_nhds_top [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (hbar : ∀ M ∈ frontier (momentBody μ π R), rateFun μ π L₀ R t M = ⊤)
    {α : Type*} {l : Filter α} {M : α → ι → ℝ}
    (hM : Tendsto (fun n ↦ Metric.infDist (M n) (frontier (momentBody μ π R))) l (𝓝 0)) :
    Tendsto (fun n ↦ rateFun μ π L₀ R t (M n)) l (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro B
  obtain ⟨δ, hδ, h⟩ :=
    exists_pos_forall_infDist_lt_imp_lt_rateFun hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hbar B
  filter_upwards [hM.eventually (gt_mem_nhds hδ)] with n hn
  exact h _ hn

/-- **Null supporting faces give the uniform blow-up directly.** -/
theorem exists_pos_forall_infDist_lt_imp_lt_rateFun_of_null [Nonempty ι]
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
    (hnull : ∀ u : ι → ℝ, u ≠ 0 → ∀ β : ℝ, (∀ᵐ x ∂μ, dirLoss R u x ≤ β) →
      μ {x | dirLoss R u x = β} = 0) (B : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ι → ℝ, Metric.infDist M (frontier (momentBody μ π R)) < δ →
      (B : ℝ≥0∞) < rateFun μ π L₀ R t M :=
  exists_pos_forall_infDist_lt_imp_lt_rateFun hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
    ((rateFun_frontier_eq_top_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).2 hnull) B

end Family

end Laplace.Multi
