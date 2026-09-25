/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProfileGeometry
import Laplace.Multi.HalfspaceProjection
import Laplace.Multi.MomentBody

/-!
# The extended rate function on the whole moment body

The Cramér rate of the empirical response under the featureless member `Q = P_{t,0}` is the
Legendre transform of the cumulant generating function `Λ(q) = log E_Q e^{q·R}` (`baseCgf`):

  `𝓘(M) = sup_q (q·M − Λ(q))`   (`rateFun`, as a supremum of `ENNReal.ofReal` of the Chernoff
  scores `chernoffScore M q = q·M − Λ(q)`; the score at `q = 0` is `0`, so nothing is lost).

Three facts describe it on the whole feature space:

* **on the response space it is the information distance to the featureless member**:
  `𝓘(m_t(a)) = KL(P_{t,a} ‖ P_{t,0})` (`rateFun_meanMap`), because the Chernoff score at
  `q = −t b` is the dual objective `−t b·m − A_t(b) + A_t(0)`, maximal at `b = a`
  (`dual_objective_le_at_mean`);
  in particular `𝓘(m_t(0)) = 0` (`rateFun_meanMap_zero`) and on the response space `𝓘` is the
  convex function `I_t + A_t(0)` (`rateFun_meanMap_toReal`, `convexOn_dualPotential_add`);
* **off the moment body it is `+∞`** (`rateFun_eq_top_of_not_mem`): a point outside the closed
  convex hull of the essential range is separated from it by a direction `w` with `w·M > sup_K w·y`,
  and along the ray `λ w` the cumulant generating function grows at most like `λ sup_K w·y`
  (`baseCgf_smul_le`), so the Chernoff scores are unbounded;
* **it is lower semicontinuous** (`lowerSemicontinuous_rateFun`), as a supremum of continuous
  functions.

Together with the compact-cover and tilt bounds this is the object of the full Cramér theorem: its
boundary values on `∂K` are not determined by the two clauses above and are the subject of the
exposed-face analysis.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The cumulant generating function of the features under the featureless member `P_{t,0}`. -/
noncomputable def baseCgf (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (q : ι → ℝ) :
    ℝ :=
  featCgf (familyMeasure μ π L₀ R t 0) R q

/-- The Chernoff score `q·M − Λ(q)`. -/
noncomputable def chernoffScore (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (M q : ι → ℝ) : ℝ :=
  dotJ q M - baseCgf μ π L₀ R t q

/-- **The extended rate function** `𝓘(M) = sup_q (q·M − Λ(q))`, valued in `ℝ≥0∞`. -/
noncomputable def rateFun (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (M : ι → ℝ) :
    ℝ≥0∞ :=
  ⨆ q : ι → ℝ, ENNReal.ofReal (chernoffScore μ π L₀ R t M q)

omit [MeasurableSpace X] in
theorem dotJ_neg_left (u v : ι → ℝ) : dotJ (-u) v = -dotJ u v := by
  simp only [dotJ, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

omit [MeasurableSpace X] in
/-- `t ∑ (0 − aᵢ) mᵢ = −t ⟨a, m⟩`. -/
theorem mul_sum_zero_sub_mul (t : ℝ) (a m : ι → ℝ) :
    t * ∑ i, ((0 : ι → ℝ) i - a i) * m i = -t * dotJ a m := by
  simp only [dotJ, Pi.zero_apply, zero_sub, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] in
/-- `Λ(q) = A_t(−q/t) − A_t(0)`. -/
theorem baseCgf_eq (q : ι → ℝ) :
    baseCgf μ π L₀ R t q = affLogZ μ π L₀ R t (-(t⁻¹ • q)) - affLogZ μ π L₀ R t 0 := by
  unfold baseCgf
  rw [featCgf_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht.ne' 0 q, zero_sub]

/-- Every Chernoff score at a response `m_t(a)` is at most `KL(P_{t,a} ‖ P_{t,0})`. -/
theorem chernoffScore_le_famKL (a q : ι → ℝ) :
    chernoffScore μ π L₀ R t (meanMap μ π L₀ R t a) q ≤ famKL μ π L₀ R t a 0 := by
  unfold chernoffScore
  rw [baseCgf_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  have h := dual_objective_le_at_mean hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR (t := t) a
    (-(t⁻¹ • q))
  have e : dotJ q (meanMap μ π L₀ R t a) = -t * dotJ (-(t⁻¹ • q)) (meanMap μ π L₀ R t a) := by
    rw [dotJ_neg_left, dotJ_smul_left]
    have ht' := ht.ne'
    field_simp
  rw [e, mul_sum_zero_sub_mul]
  linarith

/-- The Chernoff score at `q = −t a` is exactly `KL(P_{t,a} ‖ P_{t,0})`. -/
theorem chernoffScore_neg_smul (a : ι → ℝ) :
    chernoffScore μ π L₀ R t (meanMap μ π L₀ R t a) (-(t • a)) = famKL μ π L₀ R t a 0 := by
  unfold chernoffScore
  rw [baseCgf_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  have e : -(t⁻¹ • -(t • a)) = a := by
    rw [smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [e, dotJ_neg_left, dotJ_smul_left, mul_sum_zero_sub_mul]
  ring

/-- **The rate at a response is the information distance to the featureless member**:
`𝓘(m_t(a)) = KL(P_{t,a} ‖ P_{t,0})`. -/
theorem rateFun_meanMap (a : ι → ℝ) :
    rateFun μ π L₀ R t (meanMap μ π L₀ R t a) = ENNReal.ofReal (famKL μ π L₀ R t a 0) := by
  refine le_antisymm (iSup_le fun q ↦ ENNReal.ofReal_le_ofReal
    (chernoffScore_le_famKL hπm hπi hπ hπpos hL₀m hL₀ hR ht a q)) ?_
  exact le_iSup_of_le (-(t • a)) (le_of_eq (by
    rw [chernoffScore_neg_smul hπm hπi hπ hπpos hL₀m hL₀ hR ht a]))

/-- The rate vanishes at the featureless response. -/
theorem rateFun_meanMap_zero : rateFun μ π L₀ R t (meanMap μ π L₀ R t 0) = 0 := by
  rw [rateFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht 0, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  simp

/-- On the response space the rate is the real convex function `I_t + A_t(0)`. -/
theorem rateFun_meanMap_toReal
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) (a : ι → ℝ) :
    (rateFun μ π L₀ R t (meanMap μ π L₀ R t a)).toReal =
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) + affLogZ μ π L₀ R t 0 := by
  rw [rateFun_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    ENNReal.toReal_ofReal (famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht a 0),
    dualPotential_add_affLogZ_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a]

/-- `I_t + A_t(0)` is convex on the response space. -/
theorem convexOn_dualPotential_add
    (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) [Nonempty ι] :
    ConvexOn ℝ (Set.range (meanMap μ π L₀ R t))
      (fun M ↦ dualPotential μ π L₀ R t M + affLogZ μ π L₀ R t 0) :=
  (dualPotential_convexOn hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).add_const _

omit ht in
/-- The cumulant generating function along a ray is bounded by the essential bound of the
feature combination: if `w·R ≤ c` a.e. (prior), then `Λ(λ w) ≤ λ c` for `λ ≥ 0`. -/
theorem baseCgf_smul_le {w : ι → ℝ} {c : ℝ} (hw : ∀ᵐ x ∂μ, dirLoss R w x ≤ c) {lam : ℝ}
    (hlam : 0 ≤ lam) : baseCgf μ π L₀ R t (lam • w) ≤ lam * c := by
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hint : Integrable (fun x ↦ Real.exp (dirLoss R (lam • w) x))
      (familyMeasure μ π L₀ R t 0) := by
    have := integrable_exp_mul_of_bdd (familyMeasure μ π L₀ R t 0) (bdd_dirLoss hR w) lam
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    rw [dirLoss_smul]
  have hae : ∀ᵐ x ∂(familyMeasure μ π L₀ R t 0), Real.exp (dirLoss R (lam • w) x) ≤
      Real.exp (lam * c) := by
    have hac : familyMeasure μ π L₀ R t 0 ≪ μ := withDensity_absolutelyContinuous _ _
    filter_upwards [hac hw] with x hx
    rw [dirLoss_smul]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx hlam)
  unfold baseCgf featCgf
  rw [Real.log_le_iff_le_exp (integral_exp_pos hint)]
  calc ∫ x, Real.exp (dirLoss R (lam • w) x) ∂familyMeasure μ π L₀ R t 0
      ≤ ∫ _x, Real.exp (lam * c) ∂familyMeasure μ π L₀ R t 0 :=
        integral_mono_ae hint (integrable_const _) hae
    _ = Real.exp (lam * c) := by simp

omit ht in
/-- **Off the moment body the rate is infinite.** -/
theorem rateFun_eq_top_of_not_mem [Nonempty ι] {M : ι → ℝ} (hM : M ∉ momentBody μ π R) :
    rateFun μ π L₀ R t M = ⊤ := by
  classical
  obtain ⟨f, u, hfu, hC⟩ := geometric_hahn_banach_point_closed (convex_momentBody R)
    (isClosed_momentBody R) hM
  set v : ι → ℝ := fun j ↦ f (Pi.single j 1) with hv
  have hf : ∀ y : ι → ℝ, f y = dotJ v y := fun y ↦ by
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
  -- the separating direction `w = −v`: `w·M > −u > w·y` on `K`
  have hae : ∀ᵐ x ∂μ, dirLoss R (-v) x ≤ -u := by
    filter_upwards [ae_statPoint_mem_essRange hπm hπ hR] with x hx
    have h := hC _ (essRange_subset_momentBody R hx)
    rw [hf] at h
    have e : dirLoss R (-v) x = -dotJ v (statPoint R x) := by
      simp only [dirLoss, dotJ, statPoint, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [e]
    linarith
  have hgap : 0 < dotJ (-v) M + u := by
    rw [hf] at hfu
    rw [dotJ_neg_left]
    linarith
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  set lam : ℝ := (r + 1) / (dotJ (-v) M + u) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by positivity) hgap.le
  have hscore : (r : ℝ) ≤ chernoffScore μ π L₀ R t M (lam • -v) := by
    unfold chernoffScore
    have h1 := baseCgf_smul_le hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) hae hlam0
    rw [dotJ_smul_left]
    have e : lam * (dotJ (-v) M + u) = r + 1 := by rw [hlam]; field_simp
    nlinarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (chernoffScore μ π L₀ R t M (lam • -v)) := ENNReal.ofReal_le_ofReal hscore
    _ ≤ rateFun μ π L₀ R t M := le_iSup (fun q ↦ ENNReal.ofReal (chernoffScore μ π L₀ R t M q)) _

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
/-- **The rate function is lower semicontinuous.** -/
theorem lowerSemicontinuous_rateFun : LowerSemicontinuous (rateFun μ π L₀ R t) := by
  refine lowerSemicontinuous_iSup fun q ↦ (ENNReal.continuous_ofReal.comp ?_).lowerSemicontinuous
  have : Continuous fun M : ι → ℝ ↦ chernoffScore μ π L₀ R t M q := by
    unfold chernoffScore dotJ
    fun_prop
  exact this

end

end Laplace.Multi
