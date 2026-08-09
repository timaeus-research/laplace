/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.IntegralRemainder
import Laplace.OneD.IntegralRemainder2

/-!
# Second-order `J_n` asymptotics (gamma-rung programme, stage 2b)

The quadratised counterpart of the seabed's linearised `J_n` layer. The
quadratised integrand splits exactly into six moment terms
(`quadratised_integral_decomposition`), and combining with the
cubic-order integral remainder bound of stage 2a yields the headline
(`J_n_asymptotic_order2`): with `A = cubicScale`, `B = quarticScale`,
`m_k = ∫ u^k e^(-u²/2)`,
`J_n(t) = m_n - (A/√t)·m_(n+3) - (B/t)·m_(n+4) + (A²/(2t))·m_(n+6)
          + O(1/(t·√t))`,
the second-order expansion whose `A²` coefficient drives the
fourth-cumulant limit downstream. The `AB` and `B²` cross-terms of the
square are explicit moment multiples of `1/(t·√t)` and `1/t²` and are
absorbed into the error constant.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Pointwise six-term form of the quadratised integrand. The square of
the rescaled perturbation is expanded with the `√t`-atom substitution
`t = √t·√t`, which makes the identity rational in `√t`. -/
private theorem quadratised_integrand_eq
    (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (1 - rescaledPerturbation lam alpha gamma t u +
        rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) =
    fun u : ℝ ↦
      u ^ n * Real.exp (-(u ^ 2) / 2)
      + (-(cubicScale lam alpha / Real.sqrt t) *
          (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
        + (-(quarticScale lam gamma / t) *
            (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
          + (cubicScale lam alpha ^ 2 / (2 * t) *
              (u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
            + (cubicScale lam alpha * quarticScale lam gamma /
                (t * Real.sqrt t) *
                (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
              + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
                (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2)))))) := by
  funext u
  unfold rescaledPerturbation
  set st := Real.sqrt t with hst_def
  have hst_pos : 0 < st := Real.sqrt_pos.mpr ht
  have hts : t = st * st := (Real.mul_self_sqrt ht.le).symm
  rw [hts]
  rw [show u ^ (n + 3) = u ^ n * u ^ 3 from pow_add u n 3,
    show u ^ (n + 4) = u ^ n * u ^ 4 from pow_add u n 4,
    show u ^ (n + 6) = u ^ n * u ^ 6 from pow_add u n 6,
    show u ^ (n + 7) = u ^ n * u ^ 7 from pow_add u n 7,
    show u ^ (n + 8) = u ^ n * u ^ 8 from pow_add u n 8]
  field_simp
  ring

/-- **Quadratised integral decomposition** (six moment terms): for
`t > 0`,
`∫ u^n·e^(-u²/2)·(1 - s_t + s_t²/2) =
  m_n - (A/√t)·m_(n+3) - (B/t)·m_(n+4) + (A²/(2t))·m_(n+6)
  + (AB/(t√t))·m_(n+7) + (B²/(2t²))·m_(n+8)`. -/
theorem quadratised_integral_decomposition
    (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u +
          rescaledPerturbation lam alpha gamma t u ^ 2 / 2) =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
      - cubicScale lam alpha / Real.sqrt t *
          (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
      - quarticScale lam gamma / t *
          (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
      + cubicScale lam alpha ^ 2 / (2 * t) *
          (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
      + cubicScale lam alpha * quarticScale lam gamma /
          (t * Real.sqrt t) *
          (∫ u : ℝ, u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
      + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
          (∫ u : ℝ, u ^ (n + 8) * Real.exp (-(u ^ 2) / 2)) := by
  have h0 := integrable_pow_mul_exp_neg_half_sq n
  have h3 : Integrable (fun u : ℝ ↦
      -(cubicScale lam alpha / Real.sqrt t) *
        (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 3)).const_mul _
  have h4 : Integrable (fun u : ℝ ↦
      -(quarticScale lam gamma / t) *
        (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 4)).const_mul _
  have h6 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha ^ 2 / (2 * t) *
        (u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 6)).const_mul _
  have h7 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) *
        (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 7)).const_mul _
  have h8 : Integrable (fun u : ℝ ↦
      quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
        (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 8)).const_mul _
  have h78 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) *
        (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
      + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
        (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2))) := h7.add h8
  have h678 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha ^ 2 / (2 * t) *
        (u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
      + (cubicScale lam alpha * quarticScale lam gamma /
          (t * Real.sqrt t) *
          (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
        + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
          (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2)))) := h6.add h78
  have h4678 : Integrable (fun u : ℝ ↦
      -(quarticScale lam gamma / t) *
        (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
      + (cubicScale lam alpha ^ 2 / (2 * t) *
          (u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
        + (cubicScale lam alpha * quarticScale lam gamma /
            (t * Real.sqrt t) *
            (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
          + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
            (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2))))) := h4.add h678
  have h34678 : Integrable (fun u : ℝ ↦
      -(cubicScale lam alpha / Real.sqrt t) *
        (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
      + (-(quarticScale lam gamma / t) *
          (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
        + (cubicScale lam alpha ^ 2 / (2 * t) *
            (u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
          + (cubicScale lam alpha * quarticScale lam gamma /
              (t * Real.sqrt t) *
              (u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
            + quarticScale lam gamma ^ 2 / (2 * t ^ 2) *
              (u ^ (n + 8) * Real.exp (-(u ^ 2) / 2)))))) := h3.add h4678
  rw [quadratised_integrand_eq lam alpha gamma n ht,
    integral_add h0 h34678, integral_add h3 h4678, integral_add h4 h678,
    integral_add h6 h78, integral_add h7 h8,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  ring

/-- **Second-order `J_n` asymptotic** (the gamma-rung headline for this
stage): with the notation of `J_n_asymptotic`, the expansion refined by
the `A²/(2t)` term holds with error `O(1/(t·√t))`. -/
theorem J_n_asymptotic_order2
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
            - cubicScale lam alpha / Real.sqrt t *
                (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
            - quarticScale lam gamma / t *
                (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
            + cubicScale lam alpha ^ 2 / (2 * t) *
                (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2)))| ≤
      K / (t * Real.sqrt t) := by
  obtain ⟨K₀, hK₀_nn, hrem⟩ :=
    perturbation_remainder3_integral_bound hlam hgamma hdisc n
  set m7 : ℝ := ∫ u : ℝ, u ^ (n + 7) * Real.exp (-(u ^ 2) / 2) with hm7
  set m8 : ℝ := ∫ u : ℝ, u ^ (n + 8) * Real.exp (-(u ^ 2) / 2) with hm8
  refine ⟨K₀ + |cubicScale lam alpha * quarticScale lam gamma| * |m7| +
    quarticScale lam gamma ^ 2 / 2 * |m8|,
    by positivity, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hts : (0 : ℝ) < t * Real.sqrt t := by positivity
  -- Split J_n into the quadratised part plus the cubic remainder.
  have hJ_int := integrable_J_n hlam hgamma hdisc n ht0
  have hquad_int : Integrable (fun u : ℝ ↦
      u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u +
          rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) := by
    rw [quadratised_integrand_eq lam alpha gamma n ht0]
    exact (integrable_pow_mul_exp_neg_half_sq n).add
      (((integrable_pow_mul_exp_neg_half_sq (n + 3)).const_mul _).add
        (((integrable_pow_mul_exp_neg_half_sq (n + 4)).const_mul _).add
          (((integrable_pow_mul_exp_neg_half_sq (n + 6)).const_mul _).add
            (((integrable_pow_mul_exp_neg_half_sq (n + 7)).const_mul _).add
              ((integrable_pow_mul_exp_neg_half_sq (n + 8)).const_mul
                _)))))
  have hrem_int : Integrable (fun u : ℝ ↦
      u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u +
           rescaledPerturbation lam alpha gamma t u ^ 2 / 2))) := by
    have h := hJ_int.sub hquad_int
    refine h.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  have hJ_split : (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
      Real.exp (-rescaledPerturbation lam alpha gamma t u)) =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u +
          rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) +
      ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u +
           rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) := by
    rw [← integral_add hquad_int hrem_int]
    congr 1
    funext u
    ring
  rw [hJ_split, quadratised_integral_decomposition lam alpha gamma n ht0]
  -- The difference is the two cross-terms plus the cubic remainder.
  have hgoal_eq : ∀ R : ℝ,
      ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
        - cubicScale lam alpha / Real.sqrt t *
            (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
        - quarticScale lam gamma / t *
            (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
        + cubicScale lam alpha ^ 2 / (2 * t) *
            (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
        + cubicScale lam alpha * quarticScale lam gamma /
            (t * Real.sqrt t) * m7
        + quarticScale lam gamma ^ 2 / (2 * t ^ 2) * m8
        + R)
      - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
          - cubicScale lam alpha / Real.sqrt t *
              (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
          - quarticScale lam gamma / t *
              (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
          + cubicScale lam alpha ^ 2 / (2 * t) *
              (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))) =
      cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) *
        m7 + quarticScale lam gamma ^ 2 / (2 * t ^ 2) * m8 + R :=
    fun R ↦ by ring
  rw [hgoal_eq]
  -- Triangle inequality and the three bounds.
  have hR := hrem ht
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  set X7 : ℝ := A * B / (t * Real.sqrt t) * m7 with hX7
  set X8 : ℝ := B ^ 2 / (2 * t ^ 2) * m8 with hX8
  have hst1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ht
  have hst_le : Real.sqrt t ≤ t := by
    nlinarith [Real.mul_self_sqrt ht0.le, hst1]
  have ht2 : t * Real.sqrt t ≤ t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hst_le ht0.le]
  have hb7 : |X7| = |A * B| * |m7| / (t * Real.sqrt t) := by
    rw [hX7, abs_mul, abs_div, abs_of_pos hts]
    ring
  have hnum8 : (0 : ℝ) ≤ B ^ 2 * |m8| := by positivity
  have hb8 : |X8| ≤ B ^ 2 / 2 * |m8| / (t * Real.sqrt t) := by
    rw [hX8, abs_mul, abs_div,
      abs_of_pos (show (0 : ℝ) < 2 * t ^ 2 by positivity),
      abs_of_nonneg (sq_nonneg B)]
    have h1 : B ^ 2 / (2 * t ^ 2) * |m8| = B ^ 2 * |m8| / (2 * t ^ 2) := by
      ring
    have h2 : B ^ 2 / 2 * |m8| / (t * Real.sqrt t) =
        B ^ 2 * |m8| / (2 * (t * Real.sqrt t)) := by
      ring
    rw [h1, h2]
    gcongr
  calc |X7 + X8 + ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
      (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
       (1 - rescaledPerturbation lam alpha gamma t u +
         rescaledPerturbation lam alpha gamma t u ^ 2 / 2))|
      ≤ |X7 + X8| + |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2))| :=
        abs_add_le _ _
    _ ≤ |X7| + |X8| + |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2))| := by
        linarith [abs_add_le X7 X8]
    _ ≤ |A * B| * |m7| / (t * Real.sqrt t) +
          B ^ 2 / 2 * |m8| / (t * Real.sqrt t) +
          K₀ / (t * Real.sqrt t) := by
        linarith [hb7, hb8, hR]
    _ = (K₀ + |A * B| * |m7| + B ^ 2 / 2 * |m8|) / (t * Real.sqrt t) := by
        ring

end Laplace.OneD
