/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedTaylor
import Laplace.Multi.CutoffRemoval

/-!
# Cutoff independence of the localized temperature-level data

Two admissible localization regions `U ⊆ U'` give superpolynomially equal localized
normalized moments, so the `SuperPoly` hypotheses of the weighted-jet theorems do not depend
on the choice of cutoff. The two ingredients are

* an exponential tail estimate: on `U' \ U` the loss has a positive gap `η`, so the
  difference of the unnormalized integrals is `O(e^{-tη/2})` (`abs_tail_integral_le`);
* a polynomial lower bound on the partition function of the smaller region: `L ≤ 2P` on `U`
  (from the domination of the corrections), and the dilation law puts
  `∫_U e^{-2tP} = ε^{∑a} ∫_{mask} e^{-2P}` with `ε^D = t^{-1}`, which is at least
  `κ (t⁻¹)^{∑a}` for large `t` (`exists_lower_bound_partition`).

Headline: `superPoly_tempMoment_sub_of_cutoff`.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)
variable {P L : (ι → ℝ) → ℝ} {U U' : Set (ι → ℝ)}

/-! ### Integrability of the localized integrands -/

/-- A localized Boltzmann integrand with a bounded observable is integrable once the loss
dominates a multiple of the leading part on the region. -/
theorem integrable_indicator_mul_exp (_hPm : Measurable P)
    (hintP : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    (hU : MeasurableSet U) (hLm : Measurable L) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hLlow : ∀ x ∈ U, c₀ * P x ≤ L x) {A : (ι → ℝ) → ℝ} (hAm : Measurable A) {M : ℝ}
    (hM0 : 0 ≤ M) (hAM : ∀ x ∈ U, |A x| ≤ M) {t : ℝ} (ht : 0 < t) :
    Integrable fun x ↦ U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x := by
  refine ((hintP (t * c₀) (by positivity)).const_mul M).mono'
    ((hAm.mul (Real.measurable_exp.comp ((hLm.const_mul t).neg))).indicator hU).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := hAM x hx
    have h2 : Real.exp (-(t * L x)) ≤ Real.exp (-(t * c₀ * P x)) := by
      apply Real.exp_le_exp.mpr
      have := hLlow x hx
      nlinarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hM0
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-! ### The partition-function lower bound -/

/-- The masked reference partition function `∫ 1_{mask ε} e^{-2P}` converges to `∫ e^{-2P}`. -/
theorem tendsto_integral_indicator_mask_exp (hPm : Measurable P) (hU : MeasurableSet U)
    (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-(2 * P u))) :
    Tendsto (fun ε : ℝ ↦ ∫ u, (W.mask U ε).indicator (fun u ↦ Real.exp (-(2 * P u))) u)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, Real.exp (-(2 * P u)))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ Real.exp (-(2 * P u))) ?_ ?_
    hint ?_
  · filter_upwards with ε
    exact ((Real.measurable_exp.comp ((hPm.const_mul 2).neg)).indicator
      (W.measurableSet_mask hU ε)).aestronglyMeasurable
  · filter_upwards with ε
    refine Filter.Eventually.of_forall fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _)]
    exact Set.indicator_le_self' (fun _ _ ↦ (Real.exp_pos _).le) u
  · refine Filter.Eventually.of_forall fun u ↦ ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [W.eventually_mem_mask hU0 u] with ε hε
    rw [Set.indicator_of_mem hε]

/-- **Polynomial lower bound on the partition function of the smaller region**: with
`c₀ P ≤ L ≤ 2P` on `U`, `∫_U e^{-tL} ≥ κ (t⁻¹)^{∑ a}` for large `t`. -/
theorem exists_lower_bound_partition (hPm : Measurable P)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hintP : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hLm : Measurable L) {c₀ : ℝ} (hc₀ : 0 < c₀) (hLlow : ∀ x ∈ U, c₀ * P x ≤ L x)
    (hL2 : ∀ x ∈ U, L x ≤ 2 * P x) :
    ∃ κ T₀ : ℝ, 0 < κ ∧ 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      κ * (t⁻¹) ^ W.total ≤ ∫ x, U.indicator (fun x ↦ Real.exp (-(t * L x))) x := by
  have hint2 := hintP 2 two_pos
  set Z₂ : ℝ := ∫ u, Real.exp (-(2 * P u)) with hZ₂_def
  have hZ₂ : 0 < Z₂ := by
    have := integral_exp_neg_pos (P := fun u ↦ 2 * P u) hint2
    simpa using this
  -- eventually the masked reference integral exceeds `Z₂ / 2`
  have hev := (W.tendsto_integral_indicator_mask_exp hPm hU hU0 hint2).eventually_const_le
    (half_lt_self hZ₂)
  obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Z₂ / 2 ≤ ∫ u, (W.mask U ε).indicator (fun u ↦ Real.exp (-(2 * P u))) u := by
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨ε₀, hε₀, h⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε₀ / 2, half_pos hε₀, fun ε hε hεle ↦ ?_⟩
    refine h ?_ hε
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    linarith
  refine ⟨Z₂ / 2, max 1 ((ε₀⁻¹) ^ W.D), half_pos hZ₂, le_max_left _ _, fun t ht ↦ ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  -- the scale `ε = t^{-1/D}`
  set ε : ℝ := t ^ (-(W.D : ℝ)⁻¹) with hε_def
  have hε : 0 < ε := Real.rpow_pos_of_pos ht0 _
  have hεD : ε ^ W.D = t⁻¹ := by
    rw [hε_def, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, neg_mul,
      inv_mul_cancel₀ (by exact_mod_cast W.D_pos.ne'), Real.rpow_neg_one]
  have hεle : ε ≤ ε₀ := by
    have h1 : (ε₀⁻¹) ^ W.D ≤ t := (le_max_right _ _).trans ht
    have h2 : ε ^ W.D ≤ ε₀ ^ W.D := by
      rw [hεD]
      calc t⁻¹ ≤ ((ε₀⁻¹) ^ W.D)⁻¹ := inv_anti₀ (pow_pos (inv_pos.mpr hε₀) _) h1
        _ = ε₀ ^ W.D := by rw [inv_pow, inv_inv]
    exact le_of_pow_le_pow_left₀ W.D_pos.ne' hε₀.le h2
  have hεge : t⁻¹ ≤ ε := by
    rw [hε_def, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le ht1
    have hD : (1 : ℝ) ≤ W.D := by exact_mod_cast W.D_pos
    have : (W.D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
    linarith
  -- change of variables in the reference integral
  have hcov : ∫ x, U.indicator (fun x ↦ Real.exp (-(t * (2 * P x)))) x =
      ε ^ W.total * ∫ u, (W.mask U ε).indicator (fun u ↦ Real.exp (-(2 * P u))) u := by
    rw [W.integral_dil hε (f := U.indicator (fun x ↦ Real.exp (-(t * (2 * P x)))))
      ((Real.measurable_exp.comp (((hPm.const_mul 2).const_mul t).neg)).indicator
        hU).aestronglyMeasurable]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    beta_reduce
    by_cases hmem : W.dil ε u ∈ U
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show u ∈ W.mask U ε from hmem),
        hPqh ε hε, hεD]
      congr 1
      field_simp
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show u ∉ W.mask U ε from hmem)]
  -- monotonicity `e^{-tL} ≥ e^{-2tP}` on `U`
  have hint2t : Integrable fun x ↦ U.indicator (fun x ↦ Real.exp (-(t * (2 * P x)))) x := by
    refine Integrable.indicator ?_ hU
    exact (hintP (t * 2) (by positivity)).congr (Filter.Eventually.of_forall fun u ↦ by
      simp only []; ring_nf)
  have hintL : Integrable fun x ↦ U.indicator (fun x ↦ Real.exp (-(t * L x))) x := by
    have := integrable_indicator_mul_exp hPm hintP hU hLm hc₀ hLlow (A := fun _ ↦ (1 : ℝ))
      measurable_const (M := 1) zero_le_one (fun x _ ↦ by simp) ht0
    simpa using this
  have hmono : ∫ x, U.indicator (fun x ↦ Real.exp (-(t * (2 * P x)))) x ≤
      ∫ x, U.indicator (fun x ↦ Real.exp (-(t * L x))) x := by
    refine integral_mono hint2t hintL fun x ↦ ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      have := hL2 x hx
      nlinarith
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  calc Z₂ / 2 * (t⁻¹) ^ W.total ≤ Z₂ / 2 * ε ^ W.total :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr ht0).le hεge _) (half_pos hZ₂).le
    _ ≤ (∫ u, (W.mask U ε).indicator (fun u ↦ Real.exp (-(2 * P u))) u) * ε ^ W.total :=
        mul_le_mul_of_nonneg_right (hε₀le ε hε hεle) (pow_pos hε _).le
    _ = ∫ x, U.indicator (fun x ↦ Real.exp (-(t * (2 * P x)))) x := by rw [hcov]; ring
    _ ≤ _ := hmono

/-! ### The exponential tail -/

omit [Fintype ι] in
/-- Indicators of nested sets differ by the indicator of the difference. -/
theorem indicator_sub_indicator (hUU' : U ⊆ U') (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    U'.indicator f x - U.indicator f x = (U' \ U).indicator f x := by
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hUU' hx),
      Set.indicator_of_notMem (fun h ↦ h.2 hx), sub_self]
  · rw [Set.indicator_of_notMem hx, sub_zero]
    by_cases hx' : x ∈ U'
    · rw [Set.indicator_of_mem hx', Set.indicator_of_mem (show x ∈ U' \ U from ⟨hx', hx⟩)]
    · rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem (fun h ↦ hx' h.1)]

/-- **The exponential tail**: the difference of the localized integrals over nested regions is
`O(e^{-tη/2})` when the loss has gap `η` on the difference of the regions. -/
theorem abs_tail_integral_le (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hintP : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    (hUU' : U ⊆ U') (hU : MeasurableSet U) (hU' : MeasurableSet U') (hLm : Measurable L)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hLlow : ∀ x ∈ U', c₀ * P x ≤ L x)
    {η : ℝ} (hη : 0 < η) (hgap : ∀ x ∈ U' \ U, η ≤ L x)
    {A : (ι → ℝ) → ℝ} (hAm : Measurable A) {M : ℝ} (hM0 : 0 ≤ M) (hAM : ∀ x ∈ U', |A x| ≤ M)
    {t : ℝ} (ht : 1 ≤ t) :
    |(∫ x, U'.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x) -
        ∫ x, U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x| ≤
      M * (∫ u, Real.exp (-(c₀ / 2 * P u))) * Real.exp (-(η / 2 * t)) := by
  have ht0 : 0 < t := by linarith
  have hint' := integrable_indicator_mul_exp hPm hintP hU' hLm hc₀ hLlow hAm hM0 hAM ht0
  have hint := integrable_indicator_mul_exp hPm hintP hU hLm hc₀ (fun x hx ↦ hLlow x (hUU' hx))
    hAm hM0 (fun x hx ↦ hAM x (hUU' hx)) ht0
  rw [← integral_sub hint' hint]
  have hdiff : (fun x ↦ U'.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x -
      U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x) =
      fun x ↦ (U' \ U).indicator (fun x ↦ A x * Real.exp (-(t * L x))) x :=
    funext fun x ↦ indicator_sub_indicator hUU' _ x
  rw [hdiff]
  have hg : Integrable fun u : ι → ℝ ↦ M * Real.exp (-(η / 2 * t)) * Real.exp (-(c₀ / 2 * P u)) :=
    (hintP (c₀ / 2) (by positivity)).const_mul _
  have hbound := norm_integral_le_of_norm_le hg
    (f := fun x ↦ (U' \ U).indicator (fun x ↦ A x * Real.exp (-(t * L x))) x)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · rw [integral_const_mul] at hbound
    rw [Real.norm_eq_abs] at hbound
    calc _ ≤ M * Real.exp (-(η / 2 * t)) * ∫ u, Real.exp (-(c₀ / 2 * P u)) := hbound
      _ = _ := by ring
  · by_cases hx : x ∈ U' \ U
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hA := hAM x hx.1
      have hL := hgap x hx
      have hLP := hLlow x hx.1
      have hcP : 0 ≤ c₀ * P x := mul_nonneg hc₀.le (hP0 x)
      have hexp : Real.exp (-(t * L x)) ≤ Real.exp (-(η / 2 * t)) * Real.exp (-(c₀ / 2 * P x)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc |A x| * Real.exp (-(t * L x))
          ≤ M * (Real.exp (-(η / 2 * t)) * Real.exp (-(c₀ / 2 * P x))) :=
            mul_le_mul hA hexp (Real.exp_pos _).le hM0
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity

/-! ### Cutoff independence -/

/-- `t^N e^{-ηt/2} ≤ C e^{-ηt/4}` for `t ≥ 1`. -/
theorem exists_pow_mul_exp_neg_half_le {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      t ^ N * Real.exp (-(η / 2 * t)) ≤ C * Real.exp (-(η / 4 * t)) := by
  refine ⟨(N.factorial : ℝ) * (4 / η) ^ N, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have h := Real.pow_div_factorial_le_exp (η / 4 * t) (by positivity) N
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have h4 : (4 / η) ^ N * (η / 4) ^ N = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm (4 : ℝ) η, div_self (by positivity), one_pow]
  have h2 : t ^ N ≤ (N.factorial : ℝ) * (4 / η) ^ N * Real.exp (η / 4 * t) := by
    calc t ^ N = (4 / η) ^ N * ((η / 4) ^ N * t ^ N) := by rw [← mul_assoc, h4, one_mul]
      _ ≤ (4 / η) ^ N * (Real.exp (η / 4 * t) * N.factorial) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have hcancel : Real.exp (η / 4 * t) * Real.exp (-(η / 4 * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexp : Real.exp (-(η / 2 * t)) = Real.exp (-(η / 4 * t)) * Real.exp (-(η / 4 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc t ^ N * Real.exp (-(η / 2 * t))
      ≤ ((N.factorial : ℝ) * (4 / η) ^ N * Real.exp (η / 4 * t)) * Real.exp (-(η / 2 * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (N.factorial : ℝ) * (4 / η) ^ N *
        (Real.exp (η / 4 * t) * Real.exp (-(η / 4 * t))) * Real.exp (-(η / 4 * t)) := by
        rw [hexp]
        ring
    _ = _ := by rw [hcancel, mul_one]

/-- **Cutoff independence**: for nested admissible localization regions `U ⊆ U'` (both
neighbourhoods of the origin, with the loss dominating and dominated by the leading part on
`U'` and having a positive gap on `U' \ U`) and a bounded observable, the localized normalized
moments agree beyond all orders in the temperature. -/
theorem superPoly_tempMoment_sub_of_cutoff (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hintP : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    (hUU' : U ⊆ U') (hU : MeasurableSet U) (hU' : MeasurableSet U') (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hLm : Measurable L) {c₀ : ℝ} (hc₀ : 0 < c₀) (hLlow : ∀ x ∈ U', c₀ * P x ≤ L x)
    (hL2 : ∀ x ∈ U', L x ≤ 2 * P x)
    {η : ℝ} (hη : 0 < η) (hgap : ∀ x ∈ U' \ U, η ≤ L x)
    {A : (ι → ℝ) → ℝ} (hAm : Measurable A) {M : ℝ} (hM0 : 0 ≤ M) (hAM : ∀ x ∈ U', |A x| ≤ M) :
    Laplace.SuperPoly fun t : ℝ ↦ tempMoment U' L A t - tempMoment U L A t := by
  obtain ⟨κ, T₀, hκ, hT₀, hZlow⟩ := W.exists_lower_bound_partition hPm hPqh hintP hU hU0 hLm
    hc₀ (fun x hx ↦ hLlow x (hUU' hx)) (fun x hx ↦ hL2 x (hUU' hx))
  set K₀ : ℝ := ∫ u, Real.exp (-(c₀ / 2 * P u)) with hK₀_def
  have hK₀0 : 0 ≤ K₀ := integral_nonneg fun u ↦ (Real.exp_pos _).le
  obtain ⟨Cη, hCη0, hCη⟩ := exists_pow_mul_exp_neg_half_le hη W.total
  refine superPoly_of_eventually_abs_le_exp (K := 2 * M * K₀ * Cη / κ) (δ := η / 4)
    (by positivity) ?_
  filter_upwards [eventually_ge_atTop T₀] with t ht
  have ht1 : 1 ≤ t := hT₀.trans ht
  have ht0 : 0 < t := by linarith
  -- the four integrals
  set Z : ℝ := ∫ x, U.indicator (fun x ↦ Real.exp (-(t * L x))) x with hZ_def
  set Z' : ℝ := ∫ x, U'.indicator (fun x ↦ Real.exp (-(t * L x))) x with hZ'_def
  set N : ℝ := ∫ x, U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x with hN_def
  set N' : ℝ := ∫ x, U'.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x with hN'_def
  have hZκ : κ * (t⁻¹) ^ W.total ≤ Z := hZlow t ht
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZκ
  have hintZ := integrable_indicator_mul_exp hPm hintP hU hLm hc₀ (fun x hx ↦ hLlow x (hUU' hx))
    (A := fun _ ↦ (1 : ℝ)) measurable_const zero_le_one (fun x _ ↦ by simp) ht0
  have hintZ' := integrable_indicator_mul_exp hPm hintP hU' hLm hc₀ hLlow
    (A := fun _ ↦ (1 : ℝ)) measurable_const zero_le_one (fun x _ ↦ by simp) ht0
  simp only [one_mul] at hintZ hintZ'
  have hZZ' : Z ≤ Z' := by
    refine integral_mono hintZ hintZ' fun x ↦ ?_
    exact Set.indicator_le_indicator_of_subset hUU' (fun _ ↦ (Real.exp_pos _).le) x
  have hZ'pos : 0 < Z' := lt_of_lt_of_le hZpos hZZ'
  -- `|N| ≤ M Z`
  have hN : |N| ≤ M * Z := by
    have hb := norm_integral_le_of_norm_le (hintZ.const_mul M)
      (f := fun x ↦ U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · rwa [integral_const_mul, Real.norm_eq_abs] at hb
    · by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hAM x (hUU' hx)) (Real.exp_pos _).le
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero, mul_zero]
  -- the tails
  have hΔN : |N' - N| ≤ M * K₀ * Real.exp (-(η / 2 * t)) :=
    abs_tail_integral_le hPm hP0 hintP hUU' hU hU' hLm hc₀ hLlow hη hgap hAm hM0 hAM ht1
  have hΔZ : |Z' - Z| ≤ K₀ * Real.exp (-(η / 2 * t)) := by
    have := abs_tail_integral_le hPm hP0 hintP hUU' hU hU' hLm hc₀ hLlow hη hgap
      (A := fun _ ↦ (1 : ℝ)) measurable_const (M := 1) zero_le_one (fun x _ ↦ by simp) ht1
    simpa using this
  -- the quotient estimate
  have hkey : tempMoment U' L A t - tempMoment U L A t =
      ((N' - N) * Z - N * (Z' - Z)) / (Z * Z') := by
    unfold tempMoment
    rw [← hN'_def, ← hN_def, ← hZ'_def, ← hZ_def]
    field_simp
    ring
  set E : ℝ := Real.exp (-(η / 2 * t)) with hE_def
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hnum : |(N' - N) * Z - N * (Z' - Z)| ≤ 2 * M * K₀ * E * Z := by
    calc |(N' - N) * Z - N * (Z' - Z)| ≤ |(N' - N) * Z| + |N * (Z' - Z)| := abs_sub _ _
      _ = |N' - N| * Z + |N| * |Z' - Z| := by rw [abs_mul, abs_mul, abs_of_pos hZpos]
      _ ≤ (M * K₀ * E) * Z + (M * Z) * (K₀ * E) :=
          add_le_add (mul_le_mul_of_nonneg_right hΔN hZpos.le)
            (mul_le_mul hN hΔZ (abs_nonneg _) (by positivity))
      _ = 2 * M * K₀ * E * Z := by ring
  have hinvZ : 1 / Z ≤ t ^ W.total / κ := by
    rw [div_le_div_iff₀ hZpos hκ, one_mul]
    calc κ = κ * (t⁻¹) ^ W.total * t ^ W.total := by
          rw [inv_pow, mul_assoc, inv_mul_cancel₀ (pow_pos ht0 _).ne', mul_one]
      _ ≤ Z * t ^ W.total := mul_le_mul_of_nonneg_right hZκ (by positivity)
      _ = t ^ W.total * Z := mul_comm _ _
  rw [hkey, abs_div, abs_of_pos (mul_pos hZpos hZ'pos), div_le_iff₀ (mul_pos hZpos hZ'pos)]
  calc |(N' - N) * Z - N * (Z' - Z)| ≤ 2 * M * K₀ * E * Z := hnum
    _ = (2 * M * K₀ * E * (1 / Z)) * (Z * Z) := by field_simp
    _ ≤ (2 * M * K₀ * E * (t ^ W.total / κ)) * (Z * Z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinvZ (by positivity))
          (by positivity)
    _ ≤ (2 * M * K₀ * E * (t ^ W.total / κ)) * (Z * Z') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZZ' hZpos.le) (by positivity)
    _ = (2 * M * K₀ / κ) * (t ^ W.total * E) * (Z * Z') := by ring
    _ ≤ (2 * M * K₀ / κ) * (Cη * Real.exp (-(η / 4 * t))) * (Z * Z') := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact hCη t ht1
    _ = 2 * M * K₀ * Cη / κ * Real.exp (-(η / 4 * t)) * (Z * Z') := by ring

end IntWeights

end Laplace.Multi
