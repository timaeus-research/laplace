/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.NormalizedClosure

/-!
# The germ–expectation correspondence, with `1/Z`

The two halves of the germbij correspondence in the singular case, packaged as one `iff`.

*Forward.* If `L₁` and `L₂` have the same zero set and agree on an open neighbourhood `U` of it
(the same germs along the zero set), then for every bounded compactly supported test `φ` the
normalized expectations `∫ φ e^{-tL_j} / ∫ χ e^{-tL_j}` agree beyond all orders. The
unnormalized differences are exponentially small: the integrands agree on `U`, and off `U` both
losses are bounded below by a positive constant on the compact support
(`abs_integral_mul_exp_sub_le_of_eqOn`); the partition values are bounded below polynomially
by the anchor at a zero where the window equals `1`, and the bounded-test transfer
(`superPoly_normalized_difference_of_bounded`) does the rest.

*Inverse.* This is the closure theorem `normalized_expectations_closure`: agreement beyond all
orders on smooth compactly supported tests forces equal zero sets and equal germs along them.

Headline: `germ_eq_iff_normalized_expectations`.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- A constant times a decaying exponential is beyond all orders. -/
theorem superPoly_const_mul_exp_neg {η : ℝ} (hη : 0 < η) (C : ℝ) :
    SuperPoly fun t ↦ C * Real.exp (-(η * t)) := by
  intro N
  have h1 : Tendsto (fun t : ℝ ↦ (η * t) ^ N * Real.exp (-(η * t))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp (tendsto_id.const_mul_atTop hη)
  have h2 : Tendsto (fun t : ℝ ↦ (C / η ^ N) * ((η * t) ^ N * Real.exp (-(η * t)))) atTop
      (𝓝 0) := by
    simpa using h1.const_mul (C / η ^ N)
  refine Asymptotics.isLittleO_of_tendsto' ?_ (h2.congr' ?_)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht h0
    exact absurd h0 (Real.rpow_pos_of_pos ht _).ne'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hηN : η ^ N ≠ 0 := pow_ne_zero _ hη.ne'
    rw [Real.rpow_neg ht.le, Real.rpow_natCast, div_eq_mul_inv _ (t ^ N)⁻¹, inv_inv, mul_pow]
    field_simp

omit [Fintype ι] in
/-- A continuous nonnegative function whose zeros in a compact set lie in an open set is
bounded below by a positive constant on the rest of the compact set. -/
theorem exists_pos_le_on_diff {L : (ι → ℝ) → ℝ} (hLc : Continuous L) (hL0 : ∀ w, 0 ≤ L w)
    {K U : Set (ι → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hzero : ∀ w ∈ K, L w = 0 → w ∈ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ w ∈ K \ U, η ≤ L w := by
  by_cases hne : (K \ U).Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := (hK.diff hU).exists_isMinOn hne hLc.continuousOn
    refine ⟨L w₀, ?_, fun w hw ↦ hmin hw⟩
    rcases (hL0 w₀).lt_or_eq with h | h
    · exact h
    · exact absurd (hzero w₀ hw₀.1 h.symm) hw₀.2
  · exact ⟨1, one_pos, fun w hw ↦ absurd ⟨w, hw⟩ hne⟩

/-- Bounded compactly supported tests against a nonnegative loss are integrable. -/
theorem integrable_mul_exp_neg_of_bounded {L φ : (ι → ℝ) → ℝ} (hLc : Continuous L)
    (hL0 : ∀ w, 0 ≤ L w) (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Integrable fun w ↦ φ w * Real.exp (-(t * L w)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hφM 0)
  refine integrable_of_bounded_of_hasCompactSupport
    (hφm.mul (Real.continuous_exp.comp ((continuous_const.mul hLc).neg)).aestronglyMeasurable)
    hφs.mul_right (M := M) fun w ↦ ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-(t * L w)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ht (hL0 w))
  calc |φ w| * Real.exp (-(t * L w)) ≤ M * 1 :=
        mul_le_mul (hφM w) this (Real.exp_pos _).le hM0
    _ = M := mul_one _

/-- **Exponentially small unnormalized differences from equal germs.** If the losses agree on
an open set `U` containing their zeros within the support of a bounded test `φ`, the
difference of the two integrals is `O(e^{-ηt})`. -/
theorem abs_integral_mul_exp_sub_le_of_eqOn {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1c : Continuous L₁) (h2c : Continuous L₂) (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hEq : ∀ w ∈ U, L₁ w = L₂ w)
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M)
    (hz1 : ∀ w ∈ tsupport φ, L₁ w = 0 → w ∈ U) (hz2 : ∀ w ∈ tsupport φ, L₂ w = 0 → w ∈ U) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |(∫ w, φ w * Real.exp (-(t * L₂ w))) - ∫ w, φ w * Real.exp (-(t * L₁ w))| ≤
        C * Real.exp (-(η * t)) := by
  have hK : IsCompact (tsupport φ) := hφs
  obtain ⟨η₁, hη₁, hb1⟩ := exists_pos_le_on_diff h1c hL1 hK hU hz1
  obtain ⟨η₂, hη₂, hb2⟩ := exists_pos_le_on_diff h2c hL2 hK hU hz2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hφM 0)
  set η := min η₁ η₂ with hη_def
  have hη : 0 < η := lt_min hη₁ hη₂
  refine ⟨η, 2 * M * volume.real (tsupport φ), hη, by positivity, fun t ht ↦ ?_⟩
  have hint1 := integrable_mul_exp_neg_of_bounded h1c hL1 hφm hφs hφM ht
  have hint2 := integrable_mul_exp_neg_of_bounded h2c hL2 hφm hφs hφM ht
  rw [← integral_sub hint2 hint1]
  have hKm : MeasurableSet (tsupport φ) := hK.isClosed.measurableSet
  have hind : Integrable ((tsupport φ).indicator fun _ ↦ 2 * M * Real.exp (-(η * t))) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hK.measure_lt_top.ne)
  have hpt : ∀ w, ‖φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))‖ ≤
      (tsupport φ).indicator (fun _ ↦ 2 * M * Real.exp (-(η * t))) w := by
    intro w
    rw [Real.norm_eq_abs]
    by_cases hw : w ∈ tsupport φ
    · rw [Set.indicator_of_mem hw]
      by_cases hwU : w ∈ U
      · rw [hEq w hwU, sub_self, abs_zero]
        positivity
      · have hb1' : η ≤ L₁ w := le_trans (min_le_left _ _) (hb1 w ⟨hw, hwU⟩)
        have hb2' : η ≤ L₂ w := le_trans (min_le_right _ _) (hb2 w ⟨hw, hwU⟩)
        have he1 : Real.exp (-(t * L₁ w)) ≤ Real.exp (-(η * t)) := by
          rw [Real.exp_le_exp]
          nlinarith
        have he2 : Real.exp (-(t * L₂ w)) ≤ Real.exp (-(η * t)) := by
          rw [Real.exp_le_exp]
          nlinarith
        calc |φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))|
            = |φ w| * |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| := by
              rw [← mul_sub, abs_mul]
          _ ≤ M * (Real.exp (-(t * L₂ w)) + Real.exp (-(t * L₁ w))) := by
              refine mul_le_mul (hφM w) ?_ (abs_nonneg _) hM0
              calc |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))|
                  ≤ |Real.exp (-(t * L₂ w))| + |Real.exp (-(t * L₁ w))| := abs_sub _ _
                _ = Real.exp (-(t * L₂ w)) + Real.exp (-(t * L₁ w)) := by
                  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          _ ≤ M * (Real.exp (-(η * t)) + Real.exp (-(η * t))) := by gcongr
          _ = 2 * M * Real.exp (-(η * t)) := by ring
    · rw [Set.indicator_of_notMem hw, image_eq_zero_of_notMem_tsupport hw, zero_mul, zero_mul,
        sub_zero, abs_zero]
  calc |∫ w, φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))|
      = ‖∫ w, φ w * Real.exp (-(t * L₂ w)) - φ w * Real.exp (-(t * L₁ w))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ w, (tsupport φ).indicator (fun _ ↦ 2 * M * Real.exp (-(η * t))) w :=
        norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hpt)
    _ = 2 * M * volume.real (tsupport φ) * Real.exp (-(η * t)) := by
        rw [integral_indicator_const _ hKm, smul_eq_mul]
        ring

/-- Equal germs along the zeros give unnormalized agreement beyond all orders. -/
theorem superPoly_difference_of_eqOn {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1c : Continuous L₁) (h2c : Continuous L₂) (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hEq : ∀ w ∈ U, L₁ w = L₂ w)
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M)
    (hz1 : ∀ w ∈ tsupport φ, L₁ w = 0 → w ∈ U) (hz2 : ∀ w ∈ tsupport φ, L₂ w = 0 → w ∈ U) :
    SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w))) -
      ∫ w, φ w * Real.exp (-(t * L₁ w)) := by
  obtain ⟨η, C, hη, hC, hb⟩ :=
    abs_integral_mul_exp_sub_le_of_eqOn h1c h2c hL1 hL2 hU hEq hφm hφs hφM hz1 hz2
  refine (superPoly_const_mul_exp_neg hη C).of_abs_le (M := 1) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [one_mul, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  exact hb t ht

/-- **Forward half of the correspondence, with `1/Z`.** Two smooth nonnegative losses with the
same zero set, agreeing on an open neighbourhood `U` of it, have normalized expectations
agreeing beyond all orders for every bounded compactly supported test. The window `χ` is
`1` near a zero `p₀` where `L₁` is `C²`, which anchors both partition values. -/
theorem superPoly_normalized_difference_of_germ_eq {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hzero : ∀ w, L₁ w = 0 ↔ L₂ w = 0) {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hUz : {w | L₁ w = 0} ⊆ U) (hEq : ∀ w ∈ U, L₁ w = L₂ w)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hC1 : ContDiffAt ℝ 2 L₁ p₀) (hχ1 : ∀ᶠ w in 𝓝 p₀, χ w = 1)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w)))
    {φ : (ι → ℝ) → ℝ} (hφm : AEStronglyMeasurable φ (volume : Measure (ι → ℝ)))
    (hφs : HasCompactSupport φ) {M : ℝ} (hφM : ∀ w, |φ w| ≤ M) :
    SuperPoly fun t ↦
      (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
      - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))) := by
  have hz1 : ∀ w, L₁ w = 0 → w ∈ U := fun w hw ↦ hUz hw
  have hz2 : ∀ w, L₂ w = 0 → w ∈ U := fun w hw ↦ hUz ((hzero w).mpr hw)
  -- exact agreement on smooth tests
  have hexact : ∀ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      SuperPoly fun t ↦ (∫ w, ψ w * Real.exp (-(t * L₂ w)))
        - ∫ w, ψ w * Real.exp (-(t * L₁ w)) := by
    intro ψ hψ hψs
    obtain ⟨Mψ, hMψ⟩ := hψ.continuous.bounded_above_of_compact_support hψs
    exact superPoly_difference_of_eqOn h1.continuous h2.continuous hL1 hL2 hU hEq
      hψ.continuous.aestronglyMeasurable hψs (fun w ↦ by simpa [Real.norm_eq_abs] using hMψ w)
      (fun w _ hw ↦ hz1 w hw) (fun w _ hw ↦ hz2 w hw)
  -- the anchors
  have hC2 : ContDiffAt ℝ 2 L₂ p₀ :=
    hC1.congr_of_eventuallyEq ((hU.eventually_mem (hz1 p₀ hp₀)).mono fun w hw ↦ (hEq w hw).symm)
  have hp₀2 : L₂ p₀ = 0 := (hzero p₀).mp hp₀
  obtain ⟨κ₁, hκ₁, hlow1⟩ :=
    anchor_lower_bound_eventually h1.continuous hL1 hp₀ hC1 hχc hχs hχ0 hχ1
  obtain ⟨κ₂, hκ₂, hlow2⟩ :=
    anchor_lower_bound_eventually h2.continuous hL2 hp₀2 hC2 hχc hχs hχ0 hχ1
  -- the ratio of partition values
  have hratio : SuperPoly fun t ↦ (∫ w, χ w * Real.exp (-(t * L₂ w))) /
      (∫ w, χ w * Real.exp (-(t * L₁ w))) - 1 := by
    obtain ⟨Mχ, hMχ⟩ := hχc.bounded_above_of_compact_support hχs
    have hd := superPoly_difference_of_eqOn h1.continuous h2.continuous hL1 hL2 hU hEq
      hχc.aestronglyMeasurable hχs (fun w ↦ by simpa [Real.norm_eq_abs] using hMχ w)
      (fun w _ hw ↦ hz1 w hw) (fun w _ hw ↦ hz2 w hw)
    have hB : ∀ᶠ t in atTop, |(∫ w, χ w * Real.exp (-(t * L₁ w)))⁻¹| ≤
        κ₁⁻¹ * t ^ (Fintype.card ι) := by
      filter_upwards [hlow1, eventually_gt_atTop (0 : ℝ)] with t hlt htpos
      rw [abs_of_pos (inv_pos.mpr (hZ1 t))]
      have hpos : 0 < κ₁ * t ^ (-(Fintype.card ι : ℝ)) := by positivity
      calc (∫ w, χ w * Real.exp (-(t * L₁ w)))⁻¹ ≤ (κ₁ * t ^ (-(Fintype.card ι : ℝ)))⁻¹ := by
            gcongr
        _ = κ₁⁻¹ * t ^ (Fintype.card ι) := by
            rw [mul_inv, Real.rpow_neg htpos.le, inv_inv, Real.rpow_natCast]
    refine (hd.polyBounded_mul (B := fun t ↦ (∫ w, χ w * Real.exp (-(t * L₁ w)))⁻¹) hB).congr
      (Filter.Eventually.of_forall fun t ↦ ?_)
    beta_reduce
    rw [inv_mul_eq_div, sub_div, div_self (hZ1 t).ne']
  exact superPoly_normalized_difference_of_bounded h1 h2 hL1 hL2 hexact
    (Z₁ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (Z₂ := fun t ↦ ∫ w, χ w * Real.exp (-(t * L₂ w))) hZ1 hZ2 hκ₁ hκ₂ hlow1 hlow2 hratio hφm hφs hφM

/-- **The germ–expectation correspondence, with `1/Z`.** For smooth nonnegative losses analytic
at their zeros, a window `χ` equal to `1` near a zero `p₀` of `L₁`, and `L₂` with at least one
zero: the losses have the same zero set and agree on a neighbourhood of it (the same germs along
the zero set) if and only if their normalized expectations
`∫ φ e^{-tL} / ∫ χ e^{-tL}` agree beyond all orders for every smooth compactly supported `φ`. -/
theorem germ_eq_iff_normalized_expectations {L₁ L₂ χ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hA1 : ∀ p, L₁ p = 0 → AnalyticAt ℝ L₁ p) (hA2 : ∀ p, L₂ p = 0 → AnalyticAt ℝ L₂ p)
    (hne2 : ∃ q, L₂ q = 0)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {p₀ : ι → ℝ} (hp₀ : L₁ p₀ = 0) (hχ1 : ∀ᶠ w in 𝓝 p₀, χ w = 1)
    (hZ1 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₁ w)))
    (hZ2 : ∀ t : ℝ, 0 < ∫ w, χ w * Real.exp (-(t * L₂ w))) :
    ((∀ w, L₁ w = 0 ↔ L₂ w = 0) ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ {w | L₁ w = 0} ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w) ↔
    ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦
        (∫ w, φ w * Real.exp (-(t * L₂ w))) / (∫ w, χ w * Real.exp (-(t * L₂ w)))
        - (∫ w, φ w * Real.exp (-(t * L₁ w))) / (∫ w, χ w * Real.exp (-(t * L₁ w))) := by
  constructor
  · rintro ⟨hzero, U, hU, hUz, hEq⟩ φ hφ hφs
    obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφs
    exact superPoly_normalized_difference_of_germ_eq h1 h2 hL1 hL2 hzero hU hUz hEq hχc hχs hχ0
      hp₀ (hA1 p₀ hp₀).contDiffAt hχ1 hZ1 hZ2 hφ.continuous.aestronglyMeasurable hφs
      (fun w ↦ by simpa [Real.norm_eq_abs] using hM w)
  · intro hfam
    have h := normalized_expectations_closure h1 h2 hL1 hL2 hA1 hA2 ⟨p₀, hp₀⟩ hne2 hχc hχs hχ0
      hZ1 hZ2 hfam
    exact ⟨h.1, h.2.1⟩

end Laplace.Multi
