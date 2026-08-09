/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.Quartic
import Laplace.OneD.QuarticBoundedPrior

/-!
# Bounded-prior quartic even moments

The moment family of the grammar-precursor thread: for `t, a > 0`
and every `j`, the bounded-prior even moment
`∫_{[-a,a]} x^(2j) exp(-(t x⁴/24))` equals the full-line Gamma
closed form up to an explicitly exponentially bounded tail,
generalizing the `j = 0` headline `quartic_partition_bounded_prior`.
The tail is controlled by rate-halving — on the tail region,
`exp(-(t x⁴/24)) ≤ exp(-(t a⁴/48)) · exp(-((t/2) x⁴/24))` — so the
monomial factor is absorbed into the merged full-line closed form at
halved rate, with no polynomial-times-Gaussian tail machinery. The
even split of the full-line integral is extracted once, for any even
integrable real function.
-/

open Real MeasureTheory Set

namespace Laplace.OneD

/-! ## The generic even split -/

/-- Reflection of the left tail of an even function. -/
theorem integral_Iio_neg_eq_integral_Ioi_of_even {f : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x) (a : ℝ) :
    ∫ x in Iio (-a), f x = ∫ x in Ioi a, f x := by
  rw [← integral_Iic_eq_integral_Iio]
  have hsub := integral_comp_neg_Iic (-a) f
  rw [show (-(-a) : ℝ) = a from neg_neg a] at hsub
  rw [show (fun x : ℝ ↦ f (-x)) = f from funext heven] at hsub
  exact hsub

/-- **The even split**: the full-line integral of an even integrable
function decomposes as the symmetric-window integral plus two equal
tails. -/
theorem integral_eq_Icc_add_two_mul_Ioi_of_even {f : ℝ → ℝ}
    (hf : Integrable f) (heven : ∀ x, f (-x) = f x)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫ x : ℝ, f x =
      (∫ x in Icc (-a) a, f x) + 2 * ∫ x in Ioi a, f x := by
  have h1 : ∫ x : ℝ, f x =
      (∫ x in Iic a, f x) + ∫ x in Ioi a, f x := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
      hf.integrableOn hf.integrableOn]
  have hunion : Iio (-a) ∪ Icc (-a) a = Iic a := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro (hlt | ⟨_, hub⟩)
      · linarith
      · exact hub
    · intro hub
      rcases lt_or_ge x (-a) with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨hge, hub⟩
  have hdisj : Disjoint (Iio (-a)) (Icc (-a) a) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hlt, hge, _⟩
    linarith
  have h2 : ∫ x in Iic a, f x =
      (∫ x in Iio (-a), f x) + ∫ x in Icc (-a) a, f x := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Icc
      hf.integrableOn hf.integrableOn
  rw [h1, h2, integral_Iio_neg_eq_integral_Ioi_of_even heven]
  ring

/-! ## The rate-halved moment tail -/

/-- **Moment tail bound by rate-halving**: on the tail region the
Boltzmann factor donates half its rate to an `a`-dependent
exponential, and the remaining half absorbs the monomial into the
full-line closed form at rate `t/2`. -/
theorem quartic_moment_tail_Ioi (j : ℕ) {t a : ℝ} (ht : 0 < t)
    (ha : 0 < a) :
    ∫ x in Ioi a, x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24)) ≤
      (1/2) * (48/t) ^ ((2 * j + 1 : ℝ) / 4) *
        Real.Gamma ((2 * j + 1 : ℝ) / 4) *
        Real.exp (-(t * a ^ 4 / 48)) := by
  have ht2 : (0 : ℝ) < t / 2 := by positivity
  have hint2 : Integrable
      (fun x : ℝ ↦ x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24))) :=
    quartic_integrable_pow (2 * j) ht2
  have hpw : ∀ x ∈ Ioi a,
      x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24)) ≤
      Real.exp (-(t * a ^ 4 / 48)) *
        (x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24))) := by
    intro x hx
    have hxa : a ≤ x := le_of_lt hx
    have hx0 : (0 : ℝ) ≤ x := le_trans ha.le hxa
    have hx4 : a ^ 4 ≤ x ^ 4 := by
      exact pow_le_pow_left₀ ha.le hxa 4
    have hsplit : Real.exp (-(t * x ^ 4 / 24)) =
        Real.exp (-(t * x ^ 4 / 48)) *
          Real.exp (-(t * x ^ 4 / 48)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfac : Real.exp (-(t * x ^ 4 / 48)) ≤
        Real.exp (-(t * a ^ 4 / 48)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hx4 ht.le
      linarith
    calc x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))
        = Real.exp (-(t * x ^ 4 / 48)) *
            (x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 48))) := by
          rw [hsplit]; ring
      _ ≤ Real.exp (-(t * a ^ 4 / 48)) *
            (x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 48))) := by
          refine mul_le_mul_of_nonneg_right hfac ?_
          positivity
      _ = Real.exp (-(t * a ^ 4 / 48)) *
            (x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24))) := by
          congr 3
          ring
  have hmono : ∫ x in Ioi a,
      x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24)) ≤
      ∫ x in Ioi a, Real.exp (-(t * a ^ 4 / 48)) *
        (x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24))) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi hpw
    · exact (quartic_integrable_pow (2 * j) ht).integrableOn
    · exact (hint2.const_mul _).integrableOn
  have hfull : ∫ x in Ioi a,
      Real.exp (-(t * a ^ 4 / 48)) *
        (x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24))) ≤
      Real.exp (-(t * a ^ 4 / 48)) *
        ∫ x : ℝ, x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24)) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine setIntegral_le_integral hint2
      (Filter.Eventually.of_forall fun x ↦ ?_)
    exact mul_nonneg (by rw [pow_mul]; positivity) (Real.exp_pos _).le
  have hclosed := quartic_moment_even j (t := t / 2) ht2
  have h48 : (24 : ℝ) / (t / 2) = 48 / t := by
    rw [div_div_eq_mul_div]
    norm_num
  rw [h48] at hclosed
  calc ∫ x in Ioi a, x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))
      ≤ Real.exp (-(t * a ^ 4 / 48)) *
          ∫ x : ℝ, x ^ (2 * j) * Real.exp (-(t / 2 * x ^ 4 / 24)) :=
        le_trans hmono hfull
    _ = (1/2) * (48/t) ^ ((2 * j + 1 : ℝ) / 4) *
          Real.Gamma ((2 * j + 1 : ℝ) / 4) *
          Real.exp (-(t * a ^ 4 / 48)) := by
        rw [hclosed]
        ring

/-! ## Headline: the bounded-prior moment family -/

/-- **Bounded-prior quartic even moments**: for `t, a > 0` and every
`j`, the symmetric-window even moment agrees with the full-line
Gamma closed form up to an explicitly exponentially bounded tail —
the `j = 0` case is `quartic_partition_bounded_prior` (with the
rate-halved envelope in place of its Gaussian-comparison bound). -/
theorem quartic_moment_bounded_prior (j : ℕ) {t a : ℝ} (ht : 0 < t)
    (ha : 0 < a) :
    |(∫ x in Icc (-a) a, x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))) -
        (1/2) * (24/t) ^ ((2 * j + 1 : ℝ) / 4) *
          Real.Gamma ((2 * j + 1 : ℝ) / 4)| ≤
      (48/t) ^ ((2 * j + 1 : ℝ) / 4) *
        Real.Gamma ((2 * j + 1 : ℝ) / 4) *
        Real.exp (-(t * a ^ 4 / 48)) := by
  have hint := quartic_integrable_pow (2 * j) ht
  have heven : ∀ x : ℝ,
      (fun y : ℝ ↦ y ^ (2 * j) * Real.exp (-(t * y ^ 4 / 24))) (-x) =
      (fun y : ℝ ↦ y ^ (2 * j) * Real.exp (-(t * y ^ 4 / 24))) x := by
    intro x
    simp only []
    rw [show ((-x) : ℝ) ^ (2 * j) = x ^ (2 * j) from by
        rw [pow_mul, pow_mul, neg_sq],
      show ((-x) : ℝ) ^ 4 = x ^ 4 from by ring]
  have hsplit := integral_eq_Icc_add_two_mul_Ioi_of_even hint heven
    ha.le
  have hclosed := quartic_moment_even j ht
  have hdiff : (∫ x in Icc (-a) a,
        x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))) -
      (1/2) * (24/t) ^ ((2 * j + 1 : ℝ) / 4) *
        Real.Gamma ((2 * j + 1 : ℝ) / 4) =
      -(2 * ∫ x in Ioi a,
        x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))) := by
    rw [← hclosed, hsplit]
    ring
  rw [hdiff, abs_neg]
  have htail_nn : 0 ≤ ∫ x in Ioi a,
      x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24)) :=
    setIntegral_nonneg measurableSet_Ioi fun x hx ↦ by
      have hx0 : (0 : ℝ) < x := lt_trans ha hx
      positivity
  rw [abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) htail_nn)]
  have htail := quartic_moment_tail_Ioi j ht ha
  calc 2 * ∫ x in Ioi a, x ^ (2 * j) * Real.exp (-(t * x ^ 4 / 24))
      ≤ 2 * ((1/2) * (48/t) ^ ((2 * j + 1 : ℝ) / 4) *
          Real.Gamma ((2 * j + 1 : ℝ) / 4) *
          Real.exp (-(t * a ^ 4 / 48))) := by linarith
    _ = (48/t) ^ ((2 * j + 1 : ℝ) / 4) *
          Real.Gamma ((2 * j + 1 : ℝ) / 4) *
          Real.exp (-(t * a ^ 4 / 48)) := by ring

end Laplace.OneD
