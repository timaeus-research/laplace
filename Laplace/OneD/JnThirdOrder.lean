/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.IntegralRemainder3
import Laplace.OneD.JnSecondOrder

/-!
# Third-order `J_n` asymptotics and parity

The cubised counterpart of `J_n_asymptotic_order2`. The cube of the rescaled perturbation splits
into four moment terms (`cubed_integral_decomposition`); with the quartic-order integral remainder
of `IntegralRemainder3` this gives (`J_n_asymptotic_order3`)
`J_n(t) = m_n − (A/√t) m_{n+3} − (B/t) m_{n+4} + (A²/(2t)) m_{n+6} + (AB/(t√t)) m_{n+7}
          − (A³/(6t√t)) m_{n+9} + O(1/t²)`.
Odd Gaussian moments vanish, so for even `n` the *second-order* formula already holds with a `t⁻²`
remainder (`J_n_even_asymptotic_order3`), and for odd `n` the expansion is
`−(A/√t) m_{n+3} + (AB m_{n+7} − A³ m_{n+9}/6)/(t√t) + O(1/t²)` (`J_n_odd_asymptotic_order3`).
This parity bookkeeping is what upgrades the seabed's `t^{-3/2}` moment rates to `t⁻²`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- Pointwise four-term form of the cubed integrand `uⁿ e^{−u²/2} s_t³/6`. -/
private theorem cubed_integrand_eq (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) =
    fun u : ℝ ↦
      cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) * (u ^ (n + 9) * Real.exp (-(u ^ 2) / 2))
      + (cubicScale lam alpha ^ 2 * quarticScale lam gamma / (2 * t ^ 2) *
          (u ^ (n + 10) * Real.exp (-(u ^ 2) / 2))
        + (cubicScale lam alpha * quarticScale lam gamma ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) *
            (u ^ (n + 11) * Real.exp (-(u ^ 2) / 2))
          + quarticScale lam gamma ^ 3 / (6 * t ^ 3) *
            (u ^ (n + 12) * Real.exp (-(u ^ 2) / 2)))) := by
  funext u
  unfold rescaledPerturbation
  set st := Real.sqrt t with hst_def
  have hst_pos : 0 < st := Real.sqrt_pos.mpr ht
  have hst_ne : st ≠ 0 := hst_pos.ne'
  have hts : t = st * st := (Real.mul_self_sqrt ht.le).symm
  rw [hts]
  rw [show u ^ (n + 9) = u ^ n * u ^ 9 from pow_add u n 9,
    show u ^ (n + 10) = u ^ n * u ^ 10 from pow_add u n 10,
    show u ^ (n + 11) = u ^ n * u ^ 11 from pow_add u n 11,
    show u ^ (n + 12) = u ^ n * u ^ 12 from pow_add u n 12]
  field_simp
  ring

/-- **Cubed integral decomposition**: for `t > 0`,
`∫ uⁿ e^{−u²/2} s_t³/6 = A³ m_{n+9}/(6t√t) + A²B m_{n+10}/(2t²) + AB² m_{n+11}/(2t²√t)
  + B³ m_{n+12}/(6t³)`. -/
theorem cubed_integral_decomposition (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) * (rescaledPerturbation lam alpha gamma t u ^ 3 / 6) =
      cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) *
          (∫ u : ℝ, u ^ (n + 9) * Real.exp (-(u ^ 2) / 2))
      + cubicScale lam alpha ^ 2 * quarticScale lam gamma / (2 * t ^ 2) *
          (∫ u : ℝ, u ^ (n + 10) * Real.exp (-(u ^ 2) / 2))
      + cubicScale lam alpha * quarticScale lam gamma ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) *
          (∫ u : ℝ, u ^ (n + 11) * Real.exp (-(u ^ 2) / 2))
      + quarticScale lam gamma ^ 3 / (6 * t ^ 3) *
          (∫ u : ℝ, u ^ (n + 12) * Real.exp (-(u ^ 2) / 2)) := by
  have h9 : Integrable (fun u : ℝ ↦ cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) *
      (u ^ (n + 9) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 9)).const_mul _
  have h10 : Integrable (fun u : ℝ ↦ cubicScale lam alpha ^ 2 * quarticScale lam gamma /
      (2 * t ^ 2) * (u ^ (n + 10) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 10)).const_mul _
  have h11 : Integrable (fun u : ℝ ↦ cubicScale lam alpha * quarticScale lam gamma ^ 2 /
      (2 * (t ^ 2 * Real.sqrt t)) * (u ^ (n + 11) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 11)).const_mul _
  have h12 : Integrable (fun u : ℝ ↦ quarticScale lam gamma ^ 3 / (6 * t ^ 3) *
      (u ^ (n + 12) * Real.exp (-(u ^ 2) / 2))) :=
    (integrable_pow_mul_exp_neg_half_sq (n + 12)).const_mul _
  have h1112 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha * quarticScale lam gamma ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) *
        (u ^ (n + 11) * Real.exp (-(u ^ 2) / 2))
      + quarticScale lam gamma ^ 3 / (6 * t ^ 3) * (u ^ (n + 12) * Real.exp (-(u ^ 2) / 2))) :=
    h11.add h12
  have h101112 : Integrable (fun u : ℝ ↦
      cubicScale lam alpha ^ 2 * quarticScale lam gamma / (2 * t ^ 2) *
        (u ^ (n + 10) * Real.exp (-(u ^ 2) / 2))
      + (cubicScale lam alpha * quarticScale lam gamma ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) *
          (u ^ (n + 11) * Real.exp (-(u ^ 2) / 2))
        + quarticScale lam gamma ^ 3 / (6 * t ^ 3) *
          (u ^ (n + 12) * Real.exp (-(u ^ 2) / 2)))) := h10.add h1112
  rw [cubed_integrand_eq lam alpha gamma n ht, integral_add h9 h101112, integral_add h10 h1112,
    integral_add h11 h12, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

/-- **Third-order `J_n` asymptotic**: with `A = cubicScale`, `B = quarticScale`,
`m_k = ∫ u^k e^{−u²/2}`,
`|J_n − (m_n − (A/√t) m_{n+3} − (B/t) m_{n+4} + (A²/(2t)) m_{n+6} + (AB/(t√t)) m_{n+7}
        − (A³/(6t√t)) m_{n+9})| ≤ K/t²` for `t ≥ 1`. -/
theorem J_n_asymptotic_order3 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma n t
        - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
            - cubicScale lam alpha / Real.sqrt t *
                (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
            - quarticScale lam gamma / t *
                (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
            + cubicScale lam alpha ^ 2 / (2 * t) *
                (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
            + cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) *
                (∫ u : ℝ, u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
            - cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) *
                (∫ u : ℝ, u ^ (n + 9) * Real.exp (-(u ^ 2) / 2)))| ≤ K / t ^ 2 := by
  obtain ⟨K₀, hK₀_nn, hrem⟩ := perturbation_remainder4_integral_bound hlam hgamma hdisc n
  set A := cubicScale lam alpha with hA_def
  set B := quarticScale lam gamma with hB_def
  set m8 : ℝ := ∫ u : ℝ, u ^ (n + 8) * Real.exp (-(u ^ 2) / 2) with hm8
  set m10 : ℝ := ∫ u : ℝ, u ^ (n + 10) * Real.exp (-(u ^ 2) / 2) with hm10
  set m11 : ℝ := ∫ u : ℝ, u ^ (n + 11) * Real.exp (-(u ^ 2) / 2) with hm11
  set m12 : ℝ := ∫ u : ℝ, u ^ (n + 12) * Real.exp (-(u ^ 2) / 2) with hm12
  refine ⟨K₀ + |B ^ 2 / 2 * m8| + |A ^ 2 * B / 2 * m10| + |A * B ^ 2 / 2 * m11| +
    |B ^ 3 / 6 * m12|, by positivity, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hts : (0 : ℝ) < t * Real.sqrt t := by positivity
  -- Split J_n into the quadratised part, the cubed part and the quartic remainder.
  have hJ_int := integrable_J_n hlam hgamma hdisc n ht0
  have hrem_int := integrable_remainder4 hlam hgamma hdisc n ht
  have hcub_int : Integrable (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) := by
    rw [cubed_integrand_eq lam alpha gamma n ht0]
    exact ((integrable_pow_mul_exp_neg_half_sq (n + 9)).const_mul _).add
      (((integrable_pow_mul_exp_neg_half_sq (n + 10)).const_mul _).add
        (((integrable_pow_mul_exp_neg_half_sq (n + 11)).const_mul _).add
          ((integrable_pow_mul_exp_neg_half_sq (n + 12)).const_mul _)))
  have hP3_int : Integrable (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (1 - rescaledPerturbation lam alpha gamma t u +
        rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
        rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) := by
    refine (hJ_int.sub hrem_int).congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  have hP2_int : Integrable (fun u : ℝ ↦ u ^ n * Real.exp (-(u ^ 2) / 2) *
      (1 - rescaledPerturbation lam alpha gamma t u +
        rescaledPerturbation lam alpha gamma t u ^ 2 / 2)) := by
    refine (hP3_int.add hcub_int).congr (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hJ_split : J_n lam alpha gamma n t =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u +
          rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
          rescaledPerturbation lam alpha gamma t u ^ 3 / 6))
      + ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u +
           rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
           rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) := by
    unfold J_n
    rw [← integral_add hP3_int hrem_int]
    congr 1
    funext u
    ring
  have hP3_split : (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
      (1 - rescaledPerturbation lam alpha gamma t u +
        rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
        rescaledPerturbation lam alpha gamma t u ^ 3 / 6)) =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u +
          rescaledPerturbation lam alpha gamma t u ^ 2 / 2))
      - ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (rescaledPerturbation lam alpha gamma t u ^ 3 / 6) := by
    rw [← integral_sub hP2_int hcub_int]
    congr 1
    funext u
    ring
  rw [hJ_split, hP3_split, quadratised_integral_decomposition lam alpha gamma n ht0,
    cubed_integral_decomposition lam alpha gamma n ht0]
  -- The difference is the four small terms plus the quartic remainder.
  have hgoal_eq : ∀ R : ℝ,
      ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
        - A / Real.sqrt t * (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
        - B / t * (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
        + A ^ 2 / (2 * t) * (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
        + A * B / (t * Real.sqrt t) * (∫ u : ℝ, u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
        + B ^ 2 / (2 * t ^ 2) * m8
        - (A ^ 3 / (6 * (t * Real.sqrt t)) * (∫ u : ℝ, u ^ (n + 9) * Real.exp (-(u ^ 2) / 2))
          + A ^ 2 * B / (2 * t ^ 2) * m10
          + A * B ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) * m11
          + B ^ 3 / (6 * t ^ 3) * m12)
        + R)
      - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
          - A / Real.sqrt t * (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
          - B / t * (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))
          + A ^ 2 / (2 * t) * (∫ u : ℝ, u ^ (n + 6) * Real.exp (-(u ^ 2) / 2))
          + A * B / (t * Real.sqrt t) * (∫ u : ℝ, u ^ (n + 7) * Real.exp (-(u ^ 2) / 2))
          - A ^ 3 / (6 * (t * Real.sqrt t)) *
              (∫ u : ℝ, u ^ (n + 9) * Real.exp (-(u ^ 2) / 2))) =
      B ^ 2 / (2 * t ^ 2) * m8 - A ^ 2 * B / (2 * t ^ 2) * m10
        - A * B ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) * m11 - B ^ 3 / (6 * t ^ 3) * m12 + R :=
    fun R ↦ by ring
  rw [hgoal_eq]
  have hR := hrem ht
  set X8 : ℝ := B ^ 2 / (2 * t ^ 2) * m8 with hX8
  set X10 : ℝ := A ^ 2 * B / (2 * t ^ 2) * m10 with hX10
  set X11 : ℝ := A * B ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) * m11 with hX11
  set X12 : ℝ := B ^ 3 / (6 * t ^ 3) * m12 with hX12
  have hb8 : |X8| = |B ^ 2 / 2 * m8| / t ^ 2 := by
    rw [hX8, show B ^ 2 / (2 * t ^ 2) * m8 = (B ^ 2 / 2 * m8) / t ^ 2 by ring, abs_div,
      abs_of_pos ht2]
  have hb10 : |X10| = |A ^ 2 * B / 2 * m10| / t ^ 2 := by
    rw [hX10, show A ^ 2 * B / (2 * t ^ 2) * m10 = (A ^ 2 * B / 2 * m10) / t ^ 2 by ring, abs_div,
      abs_of_pos ht2]
  have hb11 : |X11| ≤ |A * B ^ 2 / 2 * m11| / t ^ 2 := by
    rw [hX11, show A * B ^ 2 / (2 * (t ^ 2 * Real.sqrt t)) * m11 =
      (A * B ^ 2 / 2 * m11) / (t ^ 2 * Real.sqrt t) by ring, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < t ^ 2 * Real.sqrt t)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) ht2
    nlinarith
  have hb12 : |X12| ≤ |B ^ 3 / 6 * m12| / t ^ 2 := by
    rw [hX12, show B ^ 3 / (6 * t ^ 3) * m12 = (B ^ 3 / 6 * m12) / t ^ 3 by ring, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < t ^ 3)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) ht2
    calc t ^ 2 = t ^ 2 * 1 := (mul_one _).symm
      _ ≤ t ^ 2 * t := by gcongr
      _ = t ^ 3 := by ring
  calc |X8 - X10 - X11 - X12 + ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
             rescaledPerturbation lam alpha gamma t u ^ 3 / 6))|
      ≤ |X8 - X10 - X11 - X12| + |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u +
             rescaledPerturbation lam alpha gamma t u ^ 2 / 2 -
             rescaledPerturbation lam alpha gamma t u ^ 3 / 6))| := abs_add_le _ _
    _ ≤ (|X8| + |X10| + |X11| + |X12|) + K₀ / t ^ 2 := by
        gcongr
        calc |X8 - X10 - X11 - X12| ≤ |X8 - X10 - X11| + |X12| := abs_sub _ _
          _ ≤ |X8 - X10| + |X11| + |X12| := by gcongr; exact abs_sub _ _
          _ ≤ |X8| + |X10| + |X11| + |X12| := by gcongr; exact abs_sub _ _
    _ ≤ (|B ^ 2 / 2 * m8| / t ^ 2 + |A ^ 2 * B / 2 * m10| / t ^ 2 + |A * B ^ 2 / 2 * m11| / t ^ 2
          + |B ^ 3 / 6 * m12| / t ^ 2) + K₀ / t ^ 2 := by
        gcongr
        · exact hb8.le
        · exact hb10.le
    _ = (K₀ + |B ^ 2 / 2 * m8| + |A ^ 2 * B / 2 * m10| + |A * B ^ 2 / 2 * m11| +
          |B ^ 3 / 6 * m12|) / t ^ 2 := by ring

/-- **Even `n`**: odd Gaussian moments vanish, so the second-order formula holds with a `t⁻²`
remainder: `|J_{2k} − (m_{2k} − (B/t) m_{2k+4} + (A²/(2t)) m_{2k+6})| ≤ K/t²`. -/
theorem J_n_even_asymptotic_order3 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma (2 * k) t
        - ((∫ u : ℝ, u ^ (2 * k) * Real.exp (-(u ^ 2) / 2))
            - quarticScale lam gamma / t *
                (∫ u : ℝ, u ^ (2 * k + 4) * Real.exp (-(u ^ 2) / 2))
            + cubicScale lam alpha ^ 2 / (2 * t) *
                (∫ u : ℝ, u ^ (2 * k + 6) * Real.exp (-(u ^ 2) / 2)))| ≤ K / t ^ 2 := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order3 hlam hgamma hdisc (2 * k)
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm3 : (∫ u : ℝ, u ^ (2 * k + 3) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at h'
  have hm7 : (∫ u : ℝ, u ^ (2 * k + 7) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd (k + 3)
    rwa [show 2 * (k + 3) + 1 = 2 * k + 7 by ring] at h'
  have hm9 : (∫ u : ℝ, u ^ (2 * k + 9) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd (k + 4)
    rwa [show 2 * (k + 4) + 1 = 2 * k + 9 by ring] at h'
  rw [hm3, hm7, hm9] at h
  simpa only [mul_zero, sub_zero, add_zero] using h

/-- **Odd `n`**: even Gaussian moments of the leading terms vanish, so
`|J_{2k+1} − (−(A/√t) m_{2k+4} + (AB/(t√t)) m_{2k+8} − (A³/(6t√t)) m_{2k+10})| ≤ K/t²`. -/
theorem J_n_odd_asymptotic_order3 {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma (2 * k + 1) t
        - (-(cubicScale lam alpha / Real.sqrt t *
              (∫ u : ℝ, u ^ (2 * k + 4) * Real.exp (-(u ^ 2) / 2)))
            + cubicScale lam alpha * quarticScale lam gamma / (t * Real.sqrt t) *
                (∫ u : ℝ, u ^ (2 * k + 8) * Real.exp (-(u ^ 2) / 2))
            - cubicScale lam alpha ^ 3 / (6 * (t * Real.sqrt t)) *
                (∫ u : ℝ, u ^ (2 * k + 10) * Real.exp (-(u ^ 2) / 2)))| ≤ K / t ^ 2 := by
  obtain ⟨K, hK, hb⟩ := J_n_asymptotic_order3 hlam hgamma hdisc (2 * k + 1)
  refine ⟨K, hK, fun {t} ht ↦ ?_⟩
  have h := hb ht
  have hm1 : (∫ u : ℝ, u ^ (2 * k + 1) * Real.exp (-(u ^ 2) / 2)) = 0 :=
    integral_pow_mul_exp_neg_sq_odd k
  have hm5 : (∫ u : ℝ, u ^ (2 * k + 1 + 4) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd (k + 2)
    rwa [show 2 * (k + 2) + 1 = 2 * k + 1 + 4 by ring] at h'
  have hm7 : (∫ u : ℝ, u ^ (2 * k + 1 + 6) * Real.exp (-(u ^ 2) / 2)) = 0 := by
    have h' := integral_pow_mul_exp_neg_sq_odd (k + 3)
    rwa [show 2 * (k + 3) + 1 = 2 * k + 1 + 6 by ring] at h'
  rw [hm1, hm5, hm7, show 2 * k + 1 + 3 = 2 * k + 4 by ring, show 2 * k + 1 + 7 = 2 * k + 8 by ring,
    show 2 * k + 1 + 9 = 2 * k + 10 by ring] at h
  simpa only [mul_zero, zero_sub, sub_zero, add_zero] using h

end Laplace.OneD
