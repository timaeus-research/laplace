/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.NegativeChamberLaw
import Laplace.Multi.ProfileFamily

/-!
# The global wall chart

The mean map of the two-monomial wall profile, `m(c) = ⟨y^q⟩_c` for `ν_c ∝ e^{-(y^p + c y^q)}` on
`(0,∞)`, extends across the wall: it is differentiable on all of `ℝ` with
`m'(c) = −Var_c(y^q) < 0` (`hasDerivAt_profilePosterior_all`, `profileVar_pos'`), strictly
decreasing (`profileMean_strictAnti`),
continuous, with `m(c) → 0` as `c → +∞` (the `1/q` chamber) and `m(c) → +∞` as `c → −∞` (the
interior-minimiser chamber). Hence

  `m : ℝ → (0, ∞)` is a decreasing homeomorphism   (`profileMean_bijOn`, `profileMeanHomeomorph`),

so the response `⟨y^q⟩` is a **global chart** of the wall: every positive response value is realised
by exactly one coupling, on either side of the wall (Astra round 27 item 5, chart half).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Derivative

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

/-- `d/dc ∫₀^∞ ψ e^{-(y^p + c y^q)} = −∫₀^∞ ψ y^q e^{-(y^p + c y^q)}` for every real `c`, for
observables of polynomial growth. -/
theorem hasDerivAt_profileNum_all {ψ : ℝ → ℝ} (hψm : Measurable ψ) {Mψ r : ℝ} (hr : 0 ≤ r)
    (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) (c₀ : ℝ) :
    HasDerivAt (fun c ↦ profileNum p q ψ c)
      (-∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q))) c₀ := by
  have hp : 0 < p := by linarith
  set b₁ : ℝ := |c₀| + 2 with hb₁def
  have hb₁ : 0 < b₁ := by positivity
  have hball : Metric.ball c₀ 1 ∈ 𝓝 c₀ := Metric.ball_mem_nhds c₀ one_pos
  have hcge : ∀ c ∈ Metric.ball c₀ 1, -b₁ ≤ c := fun c hc ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
    linarith [hc.1, neg_abs_le c₀]
  have hmeasF : ∀ c : ℝ, AEStronglyMeasurable (fun y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) := fun c ↦
    (hψm.mul (Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg)).aestronglyMeasurable
  have hmeasF' : ∀ c : ℝ, AEStronglyMeasurable
      (fun y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) (volume.restrict (Ioi 0)) :=
    fun c ↦ (hψm.mul ((Real.measurable_exp.comp ((measurable_id.pow_const p).add
      ((measurable_id.pow_const q).const_mul c)).neg).mul
      (measurable_id.pow_const q).neg)).aestronglyMeasurable
  have hint : Integrable (fun y ↦ ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)))
      (volume.restrict (Ioi 0)) := integrableOn_profile' hq hqp c₀ hψm hr hψ
  -- the derivative integrand is the profile integrand of `ψ y^q`, of growth `r + q`
  have hψ' : ∀ y, 0 < y → |ψ y * y ^ q| ≤ Mψ * y ^ (r + q) := fun y hy ↦ by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy q), Real.rpow_add hy, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hψ y hy) (Real.rpow_pos_of_pos hy q).le
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ 1,
      ‖ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))‖ ≤
        Mψ * Real.exp (b₁ * (2 * b₁) ^ (q / (p - q))) *
          (y ^ (r + q) * Real.exp (-(1 / 2) * y ^ p)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy c hc ↦ ?_)
    have hy0 : (0 : ℝ) < y := hy
    have e : ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q))) =
        -((ψ y * y ^ q) * Real.exp (-(y ^ p + c * y ^ q))) := by ring
    rw [e, norm_neg, Real.norm_eq_abs]
    exact abs_profile_integrand_le hq hqp hψ' hb₁ (hcge c hc) hy0
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ c ∈ Metric.ball c₀ 1,
      HasDerivAt (fun c ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
        (ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q)))) c := by
    refine Filter.Eventually.of_forall fun y c _ ↦ ?_
    have h1 : HasDerivAt (fun c ↦ -(y ^ p + c * y ^ q)) (-(y ^ q)) c := by
      have h0 := ((hasDerivAt_id c).mul_const (y ^ q)).const_add (y ^ p)
      simp only [id, one_mul] at h0
      exact h0.neg
    exact h1.exp.const_mul (ψ y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c y ↦ ψ y * Real.exp (-(y ^ p + c * y ^ q)))
    (F' := fun c y ↦ ψ y * (Real.exp (-(y ^ p + c * y ^ q)) * (-(y ^ q))))
    hball (Filter.Eventually.of_forall hmeasF) hint (hmeasF' c₀) hbound
    ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := r + q) (b := 1 / 2) (by linarith) hp
      (by norm_num)).const_mul _) hdiff
  unfold profileNum
  refine key.2.congr_deriv ?_
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  ring

/-- **The wall response across the wall**: `∂_c ⟨ψ⟩_c = −Cov_c(ψ, y^q)` for every real `c`. -/
theorem hasDerivAt_profilePosterior_all {ψ : ℝ → ℝ} (hψm : Measurable ψ) {Mψ r : ℝ}
    (hr : 0 ≤ r) (hψ : ∀ y, 0 < y → |ψ y| ≤ Mψ * y ^ r) (c₀ : ℝ) :
    HasDerivAt (fun c ↦ profilePosterior p q ψ c)
      (-(profilePosterior p q (fun y ↦ ψ y * y ^ q) c₀ -
        profilePosterior p q ψ c₀ * profilePosterior p q (fun y ↦ y ^ q) c₀)) c₀ := by
  have hZ := (profileNum_one_pos' hq hqp c₀).ne'
  have hN := hasDerivAt_profileNum_all hq hqp hψm hr hψ c₀
  have hZ' := hasDerivAt_profileNum_all hq hqp (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (r := 0) le_rfl (fun y _ ↦ by simp) c₀
  have hdiv := hN.div hZ' hZ
  refine hdiv.congr_deriv ?_
  unfold profilePosterior profileNum
  simp only [one_mul]
  set N := ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(y ^ p + c₀ * y ^ q)) with hN'
  set NS := ∫ y in Ioi (0 : ℝ), ψ y * y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hNS
  set ZS := ∫ y in Ioi (0 : ℝ), y ^ q * Real.exp (-(y ^ p + c₀ * y ^ q)) with hZS
  set Z := ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ p + c₀ * y ^ q)) with hZ''
  clear_value N NS ZS Z
  field_simp
  ring

/-- **The sufficient statistic is never degenerate, on either side of the wall**:
`Var_c(y^q) > 0` for every real `c`. -/
theorem profileVar_pos' (c : ℝ) :
    0 < profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
      profilePosterior p q (fun y ↦ y ^ q) c ^ 2 := by
  have hp : 0 < p := by linarith
  have hZpos := profileNum_one_pos' hq hqp c
  set m := profilePosterior p q (fun y ↦ y ^ q) c with hm
  have hI2 : Integrable (fun y ↦ y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile' hq hqp c ((measurable_id.pow_const q).mul (measurable_id.pow_const q))
      (Mψ := 1) (r := q + q) (by linarith) fun y hy ↦ by
        rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hy q) (Real.rpow_pos_of_pos hy q)),
          Real.rpow_add hy, one_mul]
  have hI1 : Integrable (fun y ↦ y ^ q * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile' hq hqp c (measurable_id.pow_const q) (Mψ := 1) (r := q) hq.le
      (abs_rpow_le_self_rpow q)
  have hI0 : Integrable (fun y ↦ (1 : ℝ) * Real.exp (-(y ^ p + c * y ^ q)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_profile' hq hqp c measurable_const (Mψ := 1) (r := 0) le_rfl
      (fun y hy ↦ by simp)
  -- the variance is the normalised centred second moment
  have hvar : profilePosterior p q (fun y ↦ y ^ q * y ^ q) c - m ^ 2 =
      (∫ y in Ioi (0 : ℝ), (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q))) /
        profileNum p q (fun _ ↦ 1) c := by
    have hint : IntegrableOn (fun y ↦ (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q)))
        (Ioi 0) := by
      refine ((hI2.sub (hI1.const_mul (2 * m))).add (hI0.const_mul (m ^ 2))).congr
        (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have e : ∀ y, (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q)) =
        y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)) -
          2 * m * (y ^ q * Real.exp (-(y ^ p + c * y ^ q))) +
          m ^ 2 * (1 * Real.exp (-(y ^ p + c * y ^ q))) := fun y ↦ by ring
    simp_rw [e]
    have h21 : Integrable (fun y ↦ y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)) -
        2 * m * (y ^ q * Real.exp (-(y ^ p + c * y ^ q)))) (volume.restrict (Ioi 0)) :=
      hI2.sub (hI1.const_mul _)
    rw [integral_add h21 (hI0.const_mul _), integral_sub hI2 (hI1.const_mul _),
      integral_const_mul, integral_const_mul]
    unfold profilePosterior profileNum at hm ⊢
    simp only [one_mul] at hm ⊢
    set N2 := ∫ y in Ioi (0 : ℝ), y ^ q * y ^ q * Real.exp (-(y ^ p + c * y ^ q)) with hN2
    set N1 := ∫ y in Ioi (0 : ℝ), y ^ q * Real.exp (-(y ^ p + c * y ^ q)) with hN1
    set Z := ∫ y in Ioi (0 : ℝ), Real.exp (-(y ^ p + c * y ^ q)) with hZ
    have hZ0 : Z ≠ 0 := by
      unfold profileNum at hZpos
      simp only [one_mul] at hZpos
      exact hZpos.ne'
    clear_value N2 N1 Z
    rw [hm]
    field_simp
    ring
  rw [hvar]
  refine div_pos ?_ hZpos
  have hint : IntegrableOn (fun y ↦ (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) := by
    refine ((hI2.sub (hI1.const_mul (2 * m))).add (hI0.const_mul (m ^ 2))).congr
      (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ by
      simp only [Pi.zero_apply]
      exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hint]
  have hsub : Ioi (max (m ^ q⁻¹) 0 + 1) ⊆
      Function.support (fun y ↦ (y ^ q - m) ^ 2 * Real.exp (-(y ^ p + c * y ^ q))) ∩ Ioi 0 := by
    intro y hy
    have hy1 : max (m ^ q⁻¹) 0 + 1 < y := hy
    have hy0 : (0 : ℝ) < y := by linarith [le_max_right (m ^ q⁻¹) 0]
    refine ⟨?_, hy0⟩
    rw [Function.mem_support]
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · have hyq : y ^ q = m := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
        linarith
      have : y = m ^ q⁻¹ := by rw [← hyq, Real.rpow_rpow_inv hy0.le hq.ne']
      linarith [le_max_left (m ^ q⁻¹) 0]
    · exact (Real.exp_pos _).ne' h0
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioi]
  simp

/-- **The mean map is strictly decreasing on all of `ℝ`.** -/
theorem profileMean_strictAnti :
    StrictAnti (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) := by
  have hd : ∀ c, HasDerivAt (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c)
      (-(profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
        profilePosterior p q (fun y ↦ y ^ q) c * profilePosterior p q (fun y ↦ y ^ q) c)) c :=
    fun c ↦ hasDerivAt_profilePosterior_all hq hqp (ψ := fun y ↦ y ^ q)
      (measurable_id.pow_const q) (Mψ := 1) (r := q) hq.le (abs_rpow_le_self_rpow q) c
  refine strictAnti_of_deriv_neg fun c ↦ ?_
  rw [(hd c).deriv, ← sq]
  linarith [profileVar_pos' hq hqp c]

theorem continuous_profileMean :
    Continuous (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) := by
  have h0 := continuous_profileNum hq hqp (ψ := fun _ ↦ (1 : ℝ)) measurable_const (Mψ := 1)
    (r := 0) le_rfl (fun y _ ↦ by simp)
  have h1 := continuous_profileNum hq hqp (ψ := fun y ↦ y ^ q) (measurable_id.pow_const q)
    (Mψ := 1) (r := q) hq.le (abs_rpow_le_self_rpow q)
  unfold profilePosterior
  exact h1.div h0 fun c ↦ (profileNum_one_pos' hq hqp c).ne'

theorem profileMean_pos (c : ℝ) : 0 < profilePosterior p q (fun y ↦ y ^ q) c := by
  have hp : 0 < p := by linarith
  unfold profilePosterior
  refine div_pos ?_ (profileNum_one_pos' hq hqp c)
  have hint : IntegrableOn (fun y ↦ y ^ q * Real.exp (-(y ^ p + c * y ^ q))) (Ioi 0) :=
    integrableOn_profile' hq hqp c (measurable_id.pow_const q) (Mψ := 1) (r := q) hq.le
      (abs_rpow_le_self_rpow q)
  unfold profileNum
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy ↦ by
      have hy0 : (0 : ℝ) < y := hy
      simp only [Pi.zero_apply]
      exact mul_nonneg (Real.rpow_pos_of_pos hy0 _).le (Real.exp_pos _).le)) hint]
  have hsub : Ioi (1 : ℝ) ⊆
      Function.support (fun y ↦ y ^ q * Real.exp (-(y ^ p + c * y ^ q))) ∩ Ioi 0 := by
    intro y hy
    have hy1 : (1 : ℝ) < y := hy
    refine ⟨?_, show (0 : ℝ) < y by linarith⟩
    rw [Function.mem_support]
    exact (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioi]
  simp

end Derivative

section Endpoints

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p)
include hq hqp

/-- `m(c) → 0` as `c → +∞` (the `1/q` chamber). -/
theorem tendsto_profileMean_atTop :
    Tendsto (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) atTop (𝓝 0) := by
  have hp : 0 < p := by linarith
  have h := (tendsto_mul_profileMean hp hq).div_atTop tendsto_id
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simp only [id_eq]
  rw [mul_div_cancel_left₀ _ hc.ne']

/-- `⟨y^q⟩_{-b} = y_b^q · ⟨z^q⟩_B`, and `⟨z^q⟩_B → 1`. -/
theorem tendsto_profileMean_neg_div :
    Tendsto (fun b ↦ profilePosterior p q (fun y ↦ y ^ q) (-b) / negScale p q b ^ q) atTop
      (𝓝 1) := by
  have hκ : 0 < p * (p - q) := mul_pos (by linarith) (by linarith)
  set κ := p * (p - q) with hκdef
  set L0 := ∫ w : ℝ, Real.exp (-(κ / 2 * w ^ 2)) with hL0
  have hL0pos : 0 < L0 := by
    rw [hL0, integral_exp_neg_half_mul_sq hκ]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr two_pos) (Real.sqrt_pos.mpr Real.pi_pos))
      (Real.sqrt_pos.mpr hκ)
  have h0 : Tendsto (fun B ↦ negA p q 0 B) atTop (𝓝 L0) := by
    have := tendsto_negA hq hqp 0
    simpa only [pow_zero, one_mul] using this
  have h1 : Tendsto (fun B ↦ negA p q 1 B) atTop (𝓝 0) := by
    have := tendsto_negA hq hqp 1
    have e : (∫ w : ℝ, (q * w) ^ 1 * Real.exp (-(κ / 2 * w ^ 2))) = 0 := by
      simp_rw [pow_one, mul_assoc]
      rw [MeasureTheory.integral_const_mul, integral_mul_exp_neg_half_mul_sq, mul_zero]
    rwa [e] at this
  -- `⟨z^q⟩_B − 1 = A₁/(√B A₀) → 0`
  have hratio : Tendsto (fun B ↦ negA p q 1 B / negA p q 0 B / Real.sqrt B) atTop (𝓝 0) := by
    have := (h1.div h0 hL0pos.ne').div_atTop Real.tendsto_sqrt_atTop
    simpa [zero_div] using this
  have hB := tendsto_negB hq hqp
  have hcomp := (hratio.comp hB).const_add 1
  rw [add_zero] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  simp only [Function.comp_apply]
  have hy := negScale_pos hq hqp hb
  have hBpos := negB_pos hq hqp hb
  have hN0 := zNum_one_pos hq hqp hBpos
  rw [profilePosterior_neg_eq hq hqp hb, zNum_rpow_scale hy, negA_eq, negA_eq]
  have hs : 0 < Real.sqrt (negB p q b) := Real.sqrt_pos.mpr hBpos
  have h0' : zNum p q (fun z ↦ (z ^ q - 1) ^ 0) (negB p q b) =
      zNum p q (fun _ ↦ 1) (negB p q b) := by
    simp only [pow_zero]
  have h1' : zNum p q (fun z ↦ (z ^ q - 1) ^ 1) (negB p q b) =
      zNum p q (fun z ↦ z ^ q - 1) (negB p q b) := by
    simp only [pow_one]
  rw [h0', h1', zNum_sub_one hq hqp hBpos, pow_zero, pow_one, mul_one]
  set s := Real.sqrt (negB p q b)
  set N0 := zNum p q (fun _ ↦ 1) (negB p q b)
  set N1 := zNum p q (fun z ↦ z ^ q) (negB p q b)
  set Y := negScale p q b ^ q
  have hY : Y ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  field_simp
  ring

/-- `m(c) → +∞` as `c → −∞` (the interior-minimiser chamber). -/
theorem tendsto_profileMean_atBot :
    Tendsto (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) atBot atTop := by
  have hy : Tendsto (fun b ↦ negScale p q b ^ q) atTop atTop := by
    have hp : 0 < p := by linarith
    have h1 : Tendsto (fun b : ℝ ↦ q * b / p) atTop atTop :=
      (tendsto_id.const_mul_atTop hq).atTop_div_const hp
    have h2 := (tendsto_rpow_atTop (one_div_pos.mpr (sub_pos.mpr hqp))).comp h1
    exact (tendsto_rpow_atTop hq).comp h2
  have hprod := hy.atTop_mul_pos one_pos (tendsto_profileMean_neg_div hq hqp)
  have : Tendsto (fun b ↦ profilePosterior p q (fun y ↦ y ^ q) (-b)) atTop atTop := by
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    have hY : negScale p q b ^ q ≠ 0 := (Real.rpow_pos_of_pos (negScale_pos hq hqp hb) _).ne'
    field_simp
  have hneg : Tendsto (fun c : ℝ ↦ -c) atBot atTop := tendsto_neg_atBot_atTop
  have := this.comp hneg
  refine this.congr' (Filter.Eventually.of_forall fun c ↦ ?_)
  simp only [Function.comp_apply, neg_neg]

/-- **The mean map is a bijection `ℝ → (0, ∞)`.** -/
theorem profileMean_bijOn :
    BijOn (fun c ↦ profilePosterior p q (fun y ↦ y ^ q) c) univ (Ioi 0) := by
  refine ⟨fun c _ ↦ profileMean_pos hq hqp c, (profileMean_strictAnti hq hqp).injective.injOn,
    fun m hm ↦ ?_⟩
  -- surjectivity through the logarithm
  have hm0 : 0 < m := hm
  have hcont : Continuous (fun c ↦ Real.log (profilePosterior p q (fun y ↦ y ^ q) c)) :=
    (continuous_profileMean hq hqp).log fun c ↦ (profileMean_pos hq hqp c).ne'
  have htop : Tendsto (fun c ↦ Real.log (profilePosterior p q (fun y ↦ y ^ q) c)) atBot atTop :=
    Real.tendsto_log_atTop.comp (tendsto_profileMean_atBot hq hqp)
  have hbot : Tendsto (fun c ↦ Real.log (profilePosterior p q (fun y ↦ y ^ q) c)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_profileMean_atTop hq hqp, Filter.Eventually.of_forall fun c ↦
        profileMean_pos hq hqp c⟩)
  obtain ⟨c, hc⟩ := hcont.surjective' htop hbot (Real.log m)
  refine ⟨c, mem_univ _, ?_⟩
  have := Real.exp_log (profileMean_pos hq hqp c)
  simp only at hc
  rw [hc, Real.exp_log hm0] at this
  exact this.symm

/-- The mean map as a map into `(0, ∞)`. -/
noncomputable def profileMeanPos (p q : ℝ) (hq : 0 < q) (hqp : q < p) : ℝ → Ioi (0 : ℝ) :=
  fun c ↦ ⟨profilePosterior p q (fun y ↦ y ^ q) c, profileMean_pos hq hqp c⟩

/-- **The global wall chart as an order isomorphism** `ℝ ≃o (0, ∞)ᵒᵈ`. -/
noncomputable def profileMeanOrderIso : ℝ ≃o (Ioi (0 : ℝ))ᵒᵈ :=
  StrictMono.orderIsoOfSurjective (fun c ↦ OrderDual.toDual (profileMeanPos p q hq hqp c))
    (fun a b hab ↦ by
      rw [OrderDual.toDual_lt_toDual]
      exact Subtype.mk_lt_mk.mpr (profileMean_strictAnti hq hqp hab))
    (fun d ↦ by
      obtain ⟨c, _, hc⟩ := (profileMean_bijOn hq hqp).surjOn (OrderDual.ofDual d).2
      exact ⟨c, OrderDual.ofDual.injective (Subtype.ext hc)⟩)

/-- **The global wall chart as a homeomorphism** `ℝ ≃ₜ (0, ∞)`: the response `⟨y^q⟩` and the
coupling determine each other continuously across the wall. -/
noncomputable def profileMeanHomeomorph : ℝ ≃ₜ Ioi (0 : ℝ) :=
  (profileMeanOrderIso hq hqp).toHomeomorph.trans
    ⟨OrderDual.ofDual, continuous_ofDual, continuous_toDual⟩

theorem profileMeanHomeomorph_apply (c : ℝ) :
    (profileMeanHomeomorph hq hqp c : ℝ) = profilePosterior p q (fun y ↦ y ^ q) c := rfl

/-- The inverse chart (response ↦ coupling) is continuous. -/
theorem continuous_profileMeanHomeomorph_symm :
    Continuous (profileMeanHomeomorph hq hqp).symm :=
  (profileMeanHomeomorph hq hqp).symm.continuous

end Endpoints

end Laplace.Multi
