/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.NumeratorExpansion

/-!
# The numerator tails and the expansion package

Stage 5c-ii-b of the forward-expansion programme, completing the
numerator stage: the two outer tails (the true integrand's, via the
stage-2 coercivity transfer; the coefficient polynomial's, via the
Gaussian mesoscopic tail after a binomial split), the eventual
decomposition of the numerator into window piece plus tails, and the
packaging `numerator_hasExpansion`: for continuous observables of
polynomial growth, the rescaled numerator is an order-`N` asymptotic
polynomial at `0⁺` with coefficients `∫ P·e^{-T₂}·P_j`.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d N : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The integrand's absolute value factors through the observable. -/
theorem abs_integrand_eq (A : LocalLaplaceDomain L H)
    (P : EuclidD d → ℝ) (q : ℝ) (z : EuclidD d) :
    |A.integrand P q z| = |P z| * |A.integrand (fun _ ↦ 1) q z| := by
  unfold LocalLaplaceDomain.integrand
  by_cases hm : z ∈ {x : EuclidD d | q • x ∈ A.U}
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul,
      abs_mul]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      abs_zero, mul_zero]

namespace ForwardExpansionDomain

/-- **The true integrand's outer tail is beyond all orders**, with any
polynomial-growth observable. -/
theorem observable_integrand_tail_isLittleO
    (D : ForwardExpansionDomain N L H) {P : EuclidD d → ℝ}
    (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P)
    (M : ℕ) :
    (fun q : ℝ ↦ ∫ z in (mesoscopicSet d q)ᶜ,
      |D.toLocalLaplaceDomain.integrand P q z|)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ M := by
  obtain ⟨CP, n, hCP0, hCP⟩ := hP_growth
  have hB : (fun q : ℝ ↦ CP *
      ((∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ 0 *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) +
       ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ n *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|))
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ M :=
    ((integrand_meso_tail_isLittleO D.toLocalLaplaceDomain 0 M).add
      (integrand_meso_tail_isLittleO D.toLocalLaplaceDomain n
        M)).const_mul_left CP
  refine (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩).trans_isLittleO hB
  filter_upwards [self_mem_nhdsWithin] with q hq0'
  have hq0 : (0 : ℝ) < q := hq0'
  have hIn : ∀ i : ℕ, Integrable (fun z : EuclidD d ↦
      ‖z‖ ^ i * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) := by
    intro i
    have h1 := (D.toLocalLaplaceDomain.integrable_integrand
      (continuous_norm.pow i) (hasPolynomialGrowth_norm_pow i) hq0).abs
    refine h1.congr (Filter.Eventually.of_forall fun z ↦ ?_)
    change |D.toLocalLaplaceDomain.integrand (fun b ↦ ‖b‖ ^ i) q z| =
      ‖z‖ ^ i * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|
    rw [abs_integrand_eq, abs_of_nonneg
      (pow_nonneg (norm_nonneg z) i)]
  have hIP : Integrable (fun z : EuclidD d ↦
      |D.toLocalLaplaceDomain.integrand P q z|) :=
    (D.toLocalLaplaceDomain.integrable_integrand hP_cont
      ⟨CP, n, hCP0, hCP⟩ hq0).abs
  have hmono : ∫ z in (mesoscopicSet d q)ᶜ,
      |D.toLocalLaplaceDomain.integrand P q z| ≤
      ∫ z in (mesoscopicSet d q)ᶜ, CP *
        (‖z‖ ^ 0 * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z| +
         ‖z‖ ^ n * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) := by
    refine setIntegral_mono_on hIP.integrableOn
      ((((hIn 0).add (hIn n)).const_mul CP).integrableOn)
      (measurableSet_mesoscopicSet q).compl fun z _ ↦ ?_
    rw [abs_integrand_eq]
    have hcollect : CP *
        (‖z‖ ^ 0 * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z| +
         ‖z‖ ^ n * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) =
        CP * (1 + ‖z‖ ^ n) *
          |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z| := by
      rw [pow_zero]
      ring
    rw [hcollect]
    exact mul_le_mul_of_nonneg_right (hCP z) (abs_nonneg _)
  have hsplit : ∫ z in (mesoscopicSet d q)ᶜ, CP *
      (‖z‖ ^ 0 * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z| +
       ‖z‖ ^ n * |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) =
      CP * ((∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ 0 *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) +
       ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ n *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
      (hIn 0).integrableOn (hIn n).integrableOn]
  have hL0 : 0 ≤ ∫ z in (mesoscopicSet d q)ᶜ,
      |D.toLocalLaplaceDomain.integrand P q z| :=
    setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
      fun z _ ↦ abs_nonneg _
  have hB0 : 0 ≤ CP *
      ((∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ 0 *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) +
       ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ n *
        |D.toLocalLaplaceDomain.integrand (fun _ ↦ 1) q z|) := by
    refine mul_nonneg hCP0 (add_nonneg ?_ ?_) <;>
      exact setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
        fun z _ ↦ mul_nonneg (by positivity) (abs_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg hB0, one_mul]
  exact le_trans hmono (le_of_eq hsplit)

/-- **The coefficient polynomial's outer tail is beyond all orders**:
the Gaussian mesoscopic tail after a binomial split. -/
theorem coeff_polynomial_tail_isLittleO
    (D : ForwardExpansionDomain N L H) {P : EuclidD d → ℝ}
    (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P)
    (M : ℕ) :
    (fun q : ℝ ↦ ∫ z in (mesoscopicSet d q)ᶜ,
      |P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j|)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ M := by
  obtain ⟨CP, n, hCP0, hCP⟩ := hP_growth
  choose Cc hCc0 hCc using abs_correctionCoeffFn_le L N
  set CW : ℝ := 2 * CP * ∑ j ∈ Finset.range (N + 1), Cc j with hCW_def
  have hCW0 : 0 ≤ CW := by
    rw [hCW_def]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ ↦ hCc0 j)
  set KW : ℕ := n + (N + 2 * N) with hKW_def
  have hlam2 : (0 : ℝ) < D.lambda / 2 := by linarith [D.lambda_pos]
  -- the o-bound function: the binomially split Gaussian tail
  have hB : (fun q : ℝ ↦ CW *
      ∑ i ∈ Finset.range (KW + 1), (KW.choose i : ℝ) *
        ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ i *
          Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2))
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ M := by
    refine IsLittleO.const_mul_left ?_ CW
    exact Asymptotics.IsLittleO.sum fun i _ ↦
      (gaussian_meso_tail_isLittleO i M hlam2).const_mul_left _
  refine (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩).trans_isLittleO hB
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
    with q hq
  obtain ⟨hq0, hq1⟩ := hq
  have hbase : ∀ z : EuclidD d, (1 : ℝ) ≤ 1 + ‖z‖ :=
    fun z ↦ by linarith [norm_nonneg z]
  -- pointwise bound by the collapsed polynomial Gaussian
  have hpt : ∀ z : EuclidD d,
      |P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j| ≤
      CW * ((1 + ‖z‖) ^ KW *
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) := by
    intro z
    have hP2 : |P z| ≤ 2 * CP * (1 + ‖z‖) ^ n := by
      calc |P z| ≤ CP * (1 + ‖z‖ ^ n) := hCP z
        _ ≤ CP * (2 * (1 + ‖z‖) ^ n) := by
            refine mul_le_mul_of_nonneg_left ?_ hCP0
            have h1 : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n := by
              gcongr
              linarith [norm_nonneg z]
            have h2 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (hbase z)
            linarith
        _ = 2 * CP * (1 + ‖z‖) ^ n := by ring
    have hgauss : Real.exp (-taylorHomogeneousTerm 2 L z) ≤
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := D.t2_lower z
      linarith
    have hsum : |∑ j ∈ Finset.range (N + 1),
        correctionCoeffFn L N j z * q ^ j| ≤
        (∑ j ∈ Finset.range (N + 1), Cc j) * (1 + ‖z‖) ^ (N + 2 * N) := by
      calc |∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|
          ≤ ∑ j ∈ Finset.range (N + 1),
            |correctionCoeffFn L N j z * q ^ j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (N + 1),
            Cc j * (1 + ‖z‖) ^ (N + 2 * N) := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            have hjN : j ≤ N := by
              have := Finset.mem_range.mp hj
              omega
            rw [abs_mul, abs_of_pos (pow_pos hq0 j)]
            calc |correctionCoeffFn L N j z| * q ^ j
                ≤ |correctionCoeffFn L N j z| * 1 :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_one₀ hq0.le hq1.le) (abs_nonneg _)
              _ = |correctionCoeffFn L N j z| := mul_one _
              _ ≤ Cc j * (1 + ‖z‖) ^ (j + 2 * N) := hCc j z
              _ ≤ Cc j * (1 + ‖z‖) ^ (N + 2 * N) := by
                  refine mul_le_mul_of_nonneg_left ?_ (hCc0 j)
                  exact pow_le_pow_right₀ (hbase z) (by omega)
        _ = (∑ j ∈ Finset.range (N + 1), Cc j) *
            (1 + ‖z‖) ^ (N + 2 * N) := by
            rw [Finset.sum_mul]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |P z| * Real.exp (-taylorHomogeneousTerm 2 L z) *
          |∑ j ∈ Finset.range (N + 1),
            correctionCoeffFn L N j z * q ^ j|
        ≤ (2 * CP * (1 + ‖z‖) ^ n) *
            Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) *
            ((∑ j ∈ Finset.range (N + 1), Cc j) *
              (1 + ‖z‖) ^ (N + 2 * N)) := by
          refine mul_le_mul ?_ hsum (abs_nonneg _) ?_
          · exact mul_le_mul hP2 hgauss (Real.exp_pos _).le
              (by positivity)
          · positivity
      _ = CW * ((1 + ‖z‖) ^ KW *
            Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) := by
          rw [hCW_def, hKW_def, pow_add]
          ring
  -- integrabilities
  have hIsum : Integrable (fun z : EuclidD d ↦
      P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j) := by
    have h1 : Integrable (fun z : EuclidD d ↦
        ∑ j ∈ Finset.range (N + 1),
          P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
            correctionCoeffFn L N j z * q ^ j) := by
      refine integrable_finset_sum _ fun j _ ↦ ?_
      exact (D.integrable_coeff_integrand hP_cont
        ⟨CP, n, hCP0, hCP⟩ j).mul_const _
    refine h1.congr (Filter.Eventually.of_forall fun z ↦ ?_)
    change ∑ j ∈ Finset.range (N + 1),
        P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
          correctionCoeffFn L N j z * q ^ j =
      P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hIW : Integrable (fun z : EuclidD d ↦
      CW * ((1 + ‖z‖) ^ KW *
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2))) :=
    (integrable_one_add_norm_pow_mul_gaussian KW hlam2).const_mul CW
  have hmono : ∫ z in (mesoscopicSet d q)ᶜ,
      |P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j| ≤
      ∫ z in (mesoscopicSet d q)ᶜ,
        CW * ((1 + ‖z‖) ^ KW *
          Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) :=
    setIntegral_mono_on hIsum.abs.integrableOn hIW.integrableOn
      (measurableSet_mesoscopicSet q).compl fun z _ ↦ hpt z
  -- binomial split of the bound integral
  have hsplit : ∫ z in (mesoscopicSet d q)ᶜ,
      CW * ((1 + ‖z‖) ^ KW *
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) =
      CW * ∑ i ∈ Finset.range (KW + 1), (KW.choose i : ℝ) *
        ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ i *
          Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hbinom : ∀ z : EuclidD d,
        (1 + ‖z‖) ^ KW * Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) =
        ∑ i ∈ Finset.range (KW + 1), (KW.choose i : ℝ) *
          (‖z‖ ^ i * Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) := by
      intro z
      rw [add_comm (1 : ℝ) ‖z‖, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [one_pow, mul_one]
      ring
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hbinom)]
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [MeasureTheory.integral_const_mul]
    · intro i _
      exact ((integrable_pow_mul_exp_neg_mul_sq hlam2
        i).const_mul _).integrableOn
  have hL0 : 0 ≤ ∫ z in (mesoscopicSet d q)ᶜ,
      |P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        ∑ j ∈ Finset.range (N + 1),
          correctionCoeffFn L N j z * q ^ j| :=
    setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
      fun z _ ↦ abs_nonneg _
  have hB0 : 0 ≤ CW *
      ∑ i ∈ Finset.range (KW + 1), (KW.choose i : ℝ) *
        ∫ z in (mesoscopicSet d q)ᶜ, ‖z‖ ^ i *
          Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) := by
    refine mul_nonneg hCW0 (Finset.sum_nonneg fun i _ ↦ ?_)
    refine mul_nonneg (by positivity) ?_
    exact setIntegral_nonneg (measurableSet_mesoscopicSet q).compl
      fun z _ ↦ mul_nonneg (by positivity) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg hB0, one_mul]
  exact le_trans hmono (le_of_eq hsplit)

end ForwardExpansionDomain

end Laplace.Multi
