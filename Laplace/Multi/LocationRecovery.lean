/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.ExpansionBridge

/-!
# Location recovery

The germbij note's Theorem 3.1 recovers the location of the minimum
as well as the jet; everything merged so far anchors the minimum at
the origin. This file removes the mismatch. The anchored coordinate
moments tend to zero (`tendsto_posteriorMoment_coord`, from the
merged first-moment rate); a loss located at `c` has moments equal
to anchored moments of translated observables (`locatedMoment`, with
the honest translated-integral form recorded via translation
invariance of Lebesgue measure), and its coordinate moments tend to
the location. Two losses whose located first-moment families agree
beyond all orders in the temperature therefore have the same
minimum (`location_eq_of_superPoly_first_moments`) — the note's
"the expansions determine `w*`" clause, in the expansion-bridge
data language.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

namespace LocalLaplaceDomain

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Integrability of the rescaled integrand at each positive scale,
for continuous polynomial-growth observables (the Local-level mirror
of the merged slice integrability). -/
theorem integrable_integrand (A : LocalLaplaceDomain L H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) {q : ℝ} (hq : 0 < q) :
    Integrable (fun x : EuclidD d ↦ A.integrand P q x) := by
  have hdom : Integrable (fun x : EuclidD d ↦
      |P x| * Real.exp (-A.c * ‖x‖ ^ 2)) := by
    refine integrable_mul_exp_neg_mul_sq_of_polynomialGrowth A.c_pos
      hP_cont.abs.aestronglyMeasurable ?_
    obtain ⟨C, n, hC, h⟩ := hP_growth
    exact ⟨C, n, hC, fun x ↦ by rw [abs_abs]; exact h x⟩
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · have hset : MeasurableSet {x : EuclidD d | q • x ∈ A.U} :=
      (measurable_const_smul q) A.measurableSet_U
    have hmL : Measurable fun x : EuclidD d ↦
        Real.exp (-((L (q • x) - L 0) / q ^ 2)) := by
      have hm : Measurable fun x : EuclidD d ↦ L (q • x) :=
        A.measurable_L.comp (measurable_const_smul q)
      exact Real.measurable_exp.comp
        (((hm.sub measurable_const).div_const _).neg)
    exact ((hP_cont.measurable.mul hmL).aestronglyMeasurable).indicator
      hset
  · unfold integrand
    by_cases hmem : x ∈ {x : EuclidD d | q • x ∈ A.U}
    · rw [Set.indicator_of_mem hmem]
      have hlow := A.rescaled_lower hq hmem
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      positivity

/-- The rescaled integrand is additive in the observable. -/
theorem integrand_add (A : LocalLaplaceDomain L H)
    (g h : EuclidD d → ℝ) (q : ℝ) (x : EuclidD d) :
    A.integrand (fun y ↦ g y + h y) q x =
      A.integrand g q x + A.integrand h q x := by
  unfold integrand
  by_cases hm : x ∈ {x : EuclidD d | q • x ∈ A.U}
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm,
      Set.indicator_of_mem hm]
    ring
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      Set.indicator_of_notMem hm, add_zero]

/-- **Anchored coordinate moments vanish**: the localized normalized
first moment tends to the (origin-anchored) minimum. -/
theorem tendsto_posteriorMoment_coord (A : LocalLaplaceDomain L H)
    (i : Fin d) :
    Tendsto (fun q : ℝ ↦ A.posteriorMoment (fun w ↦ w i) q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hM := A.tendsto_normalized_first_moment i
  have hq0 : Tendsto (fun q : ℝ ↦ q) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmul := hM.mul hq0
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq
  unfold posteriorMoment
  field_simp

/-! ## Located moments -/

/-- The localized moment of a loss located at `c`: by definition the
anchored moment of the translated observable. -/
noncomputable def locatedMoment (A : LocalLaplaceDomain L H)
    (c : EuclidD d) (f : EuclidD d → ℝ) (q : ℝ) : ℝ :=
  A.posteriorMoment (fun y ↦ f (c + y)) q

/-- The located moment parametrized by the temperature. -/
noncomputable def locatedMomentT (A : LocalLaplaceDomain L H)
    (c : EuclidD d) (f : EuclidD d → ℝ) (t : ℝ) : ℝ :=
  A.posteriorMomentT (fun y ↦ f (c + y)) t

theorem locatedMomentT_inv_sq (A : LocalLaplaceDomain L H)
    (c : EuclidD d) (f : EuclidD d → ℝ) {q : ℝ} (hq : 0 < q) :
    A.locatedMomentT c f ((q ^ 2)⁻¹) = A.locatedMoment c f q :=
  A.posteriorMomentT_inv_sq _ hq

/-- **Located coordinate moments recover the location.** -/
theorem tendsto_locatedMoment_coord (A : LocalLaplaceDomain L H)
    (c : EuclidD d) (i : Fin d) :
    Tendsto (fun q : ℝ ↦ A.locatedMoment c (fun w ↦ w i) q)
      (𝓝[>] (0 : ℝ)) (𝓝 (c i)) := by
  have hcoord := A.tendsto_posteriorMoment_coord i
  have hev : (fun q : ℝ ↦ c i + A.posteriorMoment (fun w ↦ w i) q)
      =ᶠ[𝓝[>] (0 : ℝ)]
      fun q : ℝ ↦ A.locatedMoment c (fun w ↦ w i) q := by
    filter_upwards [A.eventually_integrand_one_pos,
      self_mem_nhdsWithin] with q hpos hq
    unfold locatedMoment posteriorMoment
    have hsplit : (fun y : EuclidD d ↦ (c + y) i) =
        fun y : EuclidD d ↦ c i + y i := by
      funext y
      simp [PiLp.add_apply]
    rw [hsplit]
    rw [A.posteriorIntegral_eq _ hq, A.posteriorIntegral_eq _ hq,
      A.posteriorIntegral_eq _ hq]
    have hadd : (fun x : EuclidD d ↦ A.integrand
        (fun x ↦ (fun y : EuclidD d ↦ c i + y i) (q • x)) q x) =
        fun x : EuclidD d ↦
          A.integrand (fun _ ↦ c i) q x +
            A.integrand (fun y ↦ (q • y) i) q x := by
      funext x
      rw [← A.integrand_add]
    have hconst : (fun x : EuclidD d ↦ A.integrand
        (fun _ ↦ c i) q x) =
        fun x : EuclidD d ↦ c i * A.integrand (fun _ ↦ 1) q x := by
      funext x
      rw [show (fun _ : EuclidD d ↦ c i) =
        fun y : EuclidD d ↦ c i * (fun _ : EuclidD d ↦ (1:ℝ)) y from
        funext fun y ↦ (mul_one _).symm]
      exact A.integrand_const_mul (c i) _ q x
    have hcoordmul : (fun x : EuclidD d ↦ A.integrand
        (fun y ↦ (q • y) i) q x) =
        fun x : EuclidD d ↦ q * A.integrand (fun y ↦ y i) q x := by
      funext x
      rw [show (fun y : EuclidD d ↦ (q • y) i) =
        fun y : EuclidD d ↦ q * y i from
        funext fun y ↦ by simp [PiLp.smul_apply]]
      exact A.integrand_const_mul q _ q x
    have hint1 : Integrable (fun x : EuclidD d ↦
        A.integrand (fun _ ↦ 1) q x) :=
      A.integrable_integrand continuous_const
        ⟨1, 0, zero_le_one, fun x ↦ by norm_num⟩ hq
    have hinti : Integrable (fun x : EuclidD d ↦
        A.integrand (fun y ↦ y i) q x) := by
      refine A.integrable_integrand
        (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) i) ?_ hq
      exact ⟨1, 1, zero_le_one, fun x ↦ by
        rw [pow_one, one_mul]
        have := euclid_abs_coord_le_norm x i
        linarith [norm_nonneg x]⟩
    have hI1 : Integrable (fun x : EuclidD d ↦
        A.integrand (fun _ : EuclidD d ↦ c i) q x) := by
      rw [hconst]
      exact hint1.const_mul (c i)
    have hI2 : Integrable (fun x : EuclidD d ↦
        A.integrand (fun y ↦ (q • y) i) q x) := by
      rw [hcoordmul]
      exact hinti.const_mul q
    rw [hadd, integral_add hI1 hI2]
    rw [hconst, hcoordmul, integral_const_mul, integral_const_mul]
    have hq0 : (0 : ℝ) < q := Set.mem_Ioi.mp hq
    have hprefne : (q ^ d * Real.exp (-(L 0 / q ^ 2))) ≠ 0 :=
      (mul_pos (pow_pos hq0 d) (Real.exp_pos _)).ne'
    have hdenne : (∫ x : EuclidD d,
        A.integrand (fun _ ↦ 1) q x) ≠ 0 := hpos.ne'
    rw [mul_div_mul_left _ _ hprefne, mul_div_mul_left _ _ hprefne,
      add_div, mul_div_cancel_right₀ _ hdenne]
  have hlim : Tendsto (fun q : ℝ ↦
      c i + A.posteriorMoment (fun w ↦ w i) q)
      (𝓝[>] (0 : ℝ)) (𝓝 (c i)) := by
    have := (tendsto_const_nhds (α := ℝ)
      (x := c i) (f := 𝓝[>] (0:ℝ))).add hcoord
    rw [add_zero] at this
    exact this
  exact hlim.congr' hev

/-! ## Two-loss location equality -/

/-- The temperature substitution sends `t → ∞` to `q → 0⁺`. -/
theorem tendsto_inv_sqrt_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ ((Real.sqrt t)⁻¹ : ℝ)) atTop
      (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact Set.mem_Ioi.mpr (inv_pos.mpr (Real.sqrt_pos.mpr ht))

end LocalLaplaceDomain

/-- **Location recovery** (the `w*` clause of germbij Theorem 3.1):
two located losses whose localized first-moment families agree
beyond all orders in the temperature have the same minimum. -/
theorem location_eq_of_superPoly_first_moments
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (A : LocalLaplaceDomain L₁ H₁) (B : LocalLaplaceDomain L₂ H₂)
    (c₁ c₂ : EuclidD d)
    (hdata : ∀ i : Fin d, Laplace.SuperPoly (fun t : ℝ ↦
      A.locatedMomentT c₁ (fun w ↦ w i) t -
        B.locatedMomentT c₂ (fun w ↦ w i) t)) :
    c₁ = c₂ := by
  ext i
  have h₁ : Tendsto
      (fun t : ℝ ↦ A.locatedMomentT c₁ (fun w ↦ w i) t)
      atTop (𝓝 (c₁ i)) :=
    (A.tendsto_locatedMoment_coord c₁ i).comp
      LocalLaplaceDomain.tendsto_inv_sqrt_nhdsGT_zero
  have h₂ : Tendsto
      (fun t : ℝ ↦ B.locatedMomentT c₂ (fun w ↦ w i) t)
      atTop (𝓝 (c₂ i)) :=
    (B.tendsto_locatedMoment_coord c₂ i).comp
      LocalLaplaceDomain.tendsto_inv_sqrt_nhdsGT_zero
  have hdiff : Tendsto (fun t : ℝ ↦
      A.locatedMomentT c₁ (fun w ↦ w i) t -
        B.locatedMomentT c₂ (fun w ↦ w i) t)
      atTop (𝓝 0) := by
    refine ((hdata i) 1).isBigO.trans_tendsto ?_
    have := tendsto_rpow_neg_atTop (y := ((1 : ℕ) : ℝ))
      (by norm_num)
    simpa using this
  have huniq := tendsto_nhds_unique (h₁.sub h₂) hdiff
  linarith [huniq]

end Laplace.Multi
