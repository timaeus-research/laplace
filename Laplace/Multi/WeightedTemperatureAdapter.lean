/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedPolynomialComparison
import Laplace.Multi.ExpansionBridge

/-!
# Temperature-level data for the weighted-jet induction

The public form of the semi-quasi-homogeneous polynomial recovery theorem. The loss is
`wLoss P S c = P + ∑_{α ∈ S} c α x^α`, localized to a region `U ∋ 0` by an indicator; the
data are the temperature-level normalized moments

  `tempMoment U L A t = (∫_U A e^{-tL}) / (∫_U e^{-tL})`.

The change of variables `x = dil ε u` at `t = ε^{-D}` (`tempMoment_dil`) turns these into
`ε^{wdeg α}` times the masked rescaled moments of `WeightedPolynomialComparison`, and a
superpolynomial agreement `SuperPoly` in the temperature becomes `o(ε^{k−D})` at every
grade (`isLittleO_pow_of_superPoly_pow`). The lower bound needed for domination follows
from the corrections being dominated by the leading part on `U`
(`lower_of_dominated`). Headline: `weightedPolynomial_coefficients_eq_of_superPoly`.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

/-! ### Superpolynomial data along `t = ε^{-D}` -/

theorem tendsto_pow_inv_atTop {D : ℕ} (hD : 0 < D) :
    Tendsto (fun ε : ℝ ↦ (ε ^ D)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have := ((continuous_pow D).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [zero_pow hD.ne'] at this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_pos (Set.mem_Ioi.mp hε) D

/-- **Superpolynomial in the temperature ⇒ superpolynomial in the scale** along
`t = ε^{-D}`: the rescaled function divided by any fixed power of `ε` is smaller than every
power of `ε` at `0⁺`. -/
theorem isLittleO_pow_of_superPoly_pow {f : ℝ → ℝ} (hf : Laplace.SuperPoly f) {D : ℕ}
    (hD : 0 < D) (m r : ℕ) :
    (fun ε : ℝ ↦ f ((ε ^ D)⁻¹) / ε ^ m) =o[𝓝[>] (0 : ℝ)] fun ε : ℝ ↦ ε ^ r := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m + r ≤ D * N := ⟨m + r, by nlinarith⟩
  have hcomp := (hf N).comp_tendsto (tendsto_pow_inv_atTop hD)
  have hev : (fun ε : ℝ ↦ (((ε ^ D)⁻¹ : ℝ)) ^ (-(N : ℝ))) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε : ℝ ↦ ε ^ (D * N) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : (0 : ℝ) < ε ^ D := pow_pos (Set.mem_Ioi.mp hε) D
    rw [Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv, Real.rpow_natCast, ← pow_mul]
  have h1 : (fun ε : ℝ ↦ f ((ε ^ D)⁻¹)) =o[𝓝[>] (0 : ℝ)] fun ε : ℝ ↦ ε ^ (D * N) :=
    hcomp.congr' (Filter.EventuallyEq.refl _ _) hev
  have h2 : (fun ε : ℝ ↦ f ((ε ^ D)⁻¹) / ε ^ m) =o[𝓝[>] (0 : ℝ)]
      fun ε : ℝ ↦ ε ^ (D * N) * (ε ^ m)⁻¹ := by
    have := h1.mul_isBigO (isBigO_refl (fun ε : ℝ ↦ ((ε ^ m)⁻¹ : ℝ)) (𝓝[>] (0 : ℝ)))
    refine this.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with ε
    rw [div_eq_mul_inv]
  refine h2.trans_isBigO ?_
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hεm : (0 : ℝ) < ε ^ m := pow_pos hε0 m
  have hkey : ε ^ (D * N) * (ε ^ m)⁻¹ = ε ^ r * ε ^ (D * N - m - r) := by
    have hDN : D * N = r + (D * N - m - r) + m := by omega
    calc ε ^ (D * N) * (ε ^ m)⁻¹ = ε ^ (r + (D * N - m - r) + m) * (ε ^ m)⁻¹ := by rw [← hDN]
      _ = ε ^ r * ε ^ (D * N - m - r) * ε ^ m * (ε ^ m)⁻¹ := by rw [pow_add, pow_add]
      _ = ε ^ r * ε ^ (D * N - m - r) := mul_inv_cancel_right₀ hεm.ne' _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hkey, abs_mul, abs_of_pos (pow_pos hε0 r),
    abs_of_pos (pow_pos hε0 _), one_mul]
  calc ε ^ r * ε ^ (D * N - m - r) ≤ ε ^ r * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_pos hε0 r).le
        exact pow_le_one₀ hε0.le hε1.le
    _ = ε ^ r := mul_one _

/-- The `o(1)` form: the divided rescaled difference tends to zero. -/
theorem tendsto_div_pow_of_superPoly_pow {f : ℝ → ℝ} (hf : Laplace.SuperPoly f) {D : ℕ}
    (hD : 0 < D) (m : ℕ) :
    Tendsto (fun ε : ℝ ↦ f ((ε ^ D)⁻¹) / ε ^ m) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have := isLittleO_pow_of_superPoly_pow hf hD m 0
  simp only [pow_zero] at this
  rwa [isLittleO_one_iff] at this

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)

/-! ### The localized temperature-level moment and its rescaling -/

/-- The semi-quasi-homogeneous polynomial loss `P + ∑ c α x^α`. -/
noncomputable def wLoss (P : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (x : ι → ℝ) : ℝ :=
  P x + wpoly S c x

/-- The localized normalized moment at temperature `t`. -/
noncomputable def tempMoment (U : Set (ι → ℝ)) (L A : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (∫ x, U.indicator (fun x ↦ A x * Real.exp (-(t * L x))) x) /
    ∫ x, U.indicator (fun x ↦ Real.exp (-(t * L x))) x

/-- Along the dilation, the localized integrand becomes `ε^{wdeg α}` times the masked
rescaled integrand. -/
theorem indicator_dil_eq {P : (ι → ℝ) → ℝ}
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u) {U : Set (ι → ℝ)}
    (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    (α : ι → ℕ) {ε : ℝ} (hε : 0 < ε) (u : ι → ℝ) :
    U.indicator (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * wLoss P S c x)))
        (W.dil ε u) =
      ε ^ W.wdeg α * (mvMonomial α u * maskedKernel (W.mask U) P (W.corr S c) ε u) := by
  have hne : (ε ^ W.D : ℝ) ≠ 0 := (pow_pos hε _).ne'
  by_cases hmem : W.dil ε u ∈ U
  · rw [Set.indicator_of_mem hmem, maskedKernel_of_mem (show u ∈ W.mask U ε from hmem),
      W.mvMonomial_dil]
    unfold wLoss
    rw [hPqh ε hε, W.wpoly_dil S c hS]
    have : (ε ^ W.D)⁻¹ * (ε ^ W.D * P u + ε ^ W.D * W.corr S c ε u) = P u + W.corr S c ε u := by
      field_simp
    rw [this]
    ring
  · rw [Set.indicator_of_notMem hmem, maskedKernel_of_notMem (show u ∉ W.mask U ε from hmem)]
    ring

/-- **The temperature adapter**: at `t = ε^{-D}` the localized normalized moment of `x^α`
is `ε^{wdeg α}` times the masked rescaled moment. -/
theorem tempMoment_dil {P : (ι → ℝ) → ℝ} (hPm : Measurable P)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ α ∈ S, W.D < W.wdeg α) (α : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    tempMoment U (wLoss P S c) (mvMonomial α) (ε ^ W.D)⁻¹ =
      ε ^ W.wdeg α * W.maskedMoment U P S c (mvMonomial α) ε := by
  have hLm : Measurable (wLoss P S c) :=
    hPm.add (Finset.measurable_sum _ fun β _ ↦ (mvMonomial_measurable β).const_mul _)
  have hnum := W.integral_dil hε (f := U.indicator
    (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * wLoss P S c x))))
    (((mvMonomial_measurable α).mul
      (Real.measurable_exp.comp ((hLm.const_mul _).neg))).indicator hU).aestronglyMeasurable
  have hden := W.integral_dil hε (f := U.indicator
    (fun x ↦ Real.exp (-((ε ^ W.D)⁻¹ * wLoss P S c x))))
    ((Real.measurable_exp.comp ((hLm.const_mul _).neg)).indicator hU).aestronglyMeasurable
  have hnum' : (∫ u, U.indicator
      (fun x ↦ mvMonomial α x * Real.exp (-((ε ^ W.D)⁻¹ * wLoss P S c x))) (W.dil ε u)) =
      ε ^ W.wdeg α * ∫ u, mvMonomial α u * maskedKernel (W.mask U) P (W.corr S c) ε u := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦
      W.indicator_dil_eq hPqh S c hS α hε u)
  have hden' : (∫ u, U.indicator (fun x ↦ Real.exp (-((ε ^ W.D)⁻¹ * wLoss P S c x)))
      (W.dil ε u)) = ∫ u, maskedKernel (W.mask U) P (W.corr S c) ε u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have h := W.indicator_dil_eq hPqh S c hS (fun _ ↦ 0) hε u (U := U)
    simp only [mvMonomial, Finset.prod_const_one, wdeg, mul_zero, Finset.sum_const_zero,
      pow_zero, one_mul] at h
    exact h
  unfold tempMoment maskedMoment
  rw [hnum, hden, hnum', hden']
  have hpos : (ε ^ W.total : ℝ) ≠ 0 := (pow_pos hε _).ne'
  rw [mul_div_mul_left _ _ hpos, mul_div_assoc]

/-! ### The lower bound from domination of the corrections by the leading part -/

/-- If `|wpoly S c x| ≤ (1 − c₀) P x` on `U`, the rescaled energy satisfies
`c₀ P ≤ P + corr` on the mask. -/
theorem lower_of_dominated {P : (ι → ℝ) → ℝ}
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    {U : Set (ι → ℝ)} (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    {c₀ : ℝ} (hdom : ∀ x ∈ U, |wpoly S c x| ≤ (1 - c₀) * P x) {ε : ℝ} (hε : 0 < ε) :
    ∀ u ∈ W.mask U ε, c₀ * P u ≤ P u + W.corr S c ε u := by
  intro u hu
  have h := hdom _ hu
  rw [W.wpoly_dil S c hS, hPqh ε hε, abs_mul, abs_of_pos (pow_pos hε _)] at h
  have hpos : (0 : ℝ) < ε ^ W.D := pow_pos hε _
  have h2 : ε ^ W.D * |W.corr S c ε u| ≤ ε ^ W.D * ((1 - c₀) * P u) := by
    have : (1 - c₀) * (ε ^ W.D * P u) = ε ^ W.D * ((1 - c₀) * P u) := by ring
    linarith [h, this]
  have h' : |W.corr S c ε u| ≤ (1 - c₀) * P u := le_of_mul_le_mul_left h2 hpos
  have := (abs_le.mp h').1
  linarith

/-! ### The headline for polynomial losses -/

/-- **Semi-quasi-homogeneous polynomial recovery beyond all orders** (germbij §7.4(b),
polynomial case): two losses `P + ∑_{α∈S} c_j α x^α` with the same quasi-homogeneous leading
part `P` (of integerized weights `W`, positive, quasi-homogeneous of degree `D`, with
`e^{-cP}` integrable for every `c > 0` and coercive in the natural-power sense), whose
corrections are dominated by `P` on a localization region `U ∈ 𝓝 0`, and whose localized
normalized monomial moments agree beyond all orders in the temperature for every `x^α`,
`α ∈ S`, have equal coefficients. -/
theorem weightedPolynomial_coefficients_eq_of_superPoly {P : (ι → ℝ) → ℝ}
    (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdom₁ : ∀ x ∈ U, |wpoly S c₁ x| ≤ (1 - c₀) * P x)
    (hdom₂ : ∀ x ∈ U, |wpoly S c₂ x| ≤ (1 - c₀) * P x)
    (hdata : ∀ α ∈ S, Laplace.SuperPoly fun t : ℝ ↦
      tempMoment U (wLoss P S c₂) (mvMonomial α) t -
        tempMoment U (wLoss P S c₁) (mvMonomial α) t) :
    ∀ α ∈ S, c₁ α = c₂ α := by
  refine W.weightedPolynomial_coefficients_eq_of_rates hPm hP0 hint hκ hcoer hU hU0 S c₁ c₂ hS
    hc₀ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact W.lower_of_dominated hPqh S c₁ hS hdom₁ hε
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact W.lower_of_dominated hPqh S c₂ hS hdom₂ hε
  · intro k hk α hα hαk
    have hlim := tendsto_div_pow_of_superPoly_pow (hdata α hα) W.D_pos (W.wdeg α + (k - W.D))
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    rw [W.tempMoment_dil hPm hPqh hU S c₂ hS α hε0, W.tempMoment_dil hPm hPqh hU S c₁ hS α hε0,
      pow_add, ← mul_sub, mul_div_mul_left _ _ (pow_pos hε0 _).ne']

end IntWeights

end Laplace.Multi
