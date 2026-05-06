import Laplace.OneD.QuarticBoundedPrior

/-!
# Bounded-prior quartic Gibbs measure with a continuous test function

Step 2 of the grammar paper precursor sequence: extends the bounded-prior
quartic partition function (in `Laplace.OneD.QuarticBoundedPrior`) by
introducing a Lipschitz test function `φ` against the bounded-prior Gibbs
measure on `[-a, a]`.

## Headline result

`quartic_lipschitz_unnormalised_bounded_prior`: for `t > 0`, `a > 0`, and
`K`-Lipschitz `φ` on `[-a, a]` (in the form `|φ(w) − φ(0)| ≤ K · |w|`),
```
| ∫_{[-a,a]} φ(w) · exp(-(t · w⁴/24)) dw
    − φ(0) · ∫_{[-a,a]} exp(-(t · w⁴/24)) dw |
  ≤ K · (1/2) · √(24π/t).
```

The unnormalised numerator with the test function differs from `φ(0)`-times
the bounded-prior partition by at most `K · ⟨|w|⟩`-style-bound, with rate
`t^{-1/2}` in the unnormalised form.

See `projects/primer/tide-log/2026-05-06-tide-bounded-prior-continuous-test.md`
for the deliberation log.
-/

open Real MeasureTheory Set

namespace Laplace.OneD

/-! ## First moment (half-line and full-line) -/

/-- Half-line first moment of the pure-quartic Gibbs weight. For `t > 0`,
`∫_{Ioi 0} w · exp(-(t · w⁴/24)) dw = (1/4) · √(24π/t)`. -/
theorem quartic_integral_w_exp_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ w in Ioi (0 : ℝ), w * exp (-(t * w ^ 4 / 24)) =
      (1/4) * Real.sqrt (24 * Real.pi / t) := by
  have ht24 : (0 : ℝ) < t / 24 := by positivity
  have hq : (-1 : ℝ) < (1 : ℝ) := by norm_num
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := 4) (q := 1) (b := t / 24)
    (by norm_num) hq ht24
  have hLHS : (∫ w in Ioi (0 : ℝ), w * exp (-(t * w ^ 4 / 24))) =
      ∫ w in Ioi (0 : ℝ), w ^ (1 : ℝ) * exp (-(t / 24) * w ^ (4 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
    rw [mem_Ioi] at hw
    have h1 : w ^ (1 : ℝ) = w := by rw [Real.rpow_one]
    have h4 : w ^ (4 : ℝ) = w ^ (4 : ℕ) := by
      rw [show ((4 : ℝ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [h1, h4]
    congr 2
    ring
  rw [hLHS, key]
  have hg : ((1 : ℝ) + 1) / 4 = (1 : ℝ) / 2 := by norm_num
  have hgneg : -((1 : ℝ) + 1) / 4 = -((1 : ℝ) / 2) := by norm_num
  rw [hg, hgneg, Real.Gamma_one_half_eq]
  have hinv : (t / 24 : ℝ) ^ (-((1 : ℝ) / 2)) = Real.sqrt (24 / t) := by
    rw [Real.rpow_neg ht24.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    congr 1
    field_simp
  rw [hinv]
  have h24t : (0 : ℝ) ≤ 24 / t := le_of_lt (by positivity)
  rw [show (24 * Real.pi / t : ℝ) = (24/t) * Real.pi from by ring]
  rw [Real.sqrt_mul h24t]
  ring

/-- Full-line first absolute moment of the pure-quartic Gibbs weight.
For `t > 0`,
`∫_ℝ |w| · exp(-(t · w⁴/24)) dw = (1/2) · √(24π/t)`. -/
theorem quartic_integral_abs_w_exp_full {t : ℝ} (ht : 0 < t) :
    ∫ w : ℝ, |w| * exp (-(t * w ^ 4 / 24)) =
      (1/2) * Real.sqrt (24 * Real.pi / t) := by
  -- Rewrite integrand in |w|-form (using w^4 = |w|^4).
  have heven : (∫ w : ℝ, |w| * exp (-(t * w ^ 4 / 24))) =
      ∫ w : ℝ, |w| * exp (-(t * |w| ^ 4 / 24)) := by
    congr 1
    ext w
    rw [show w ^ 4 = |w| ^ 4 from by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul w 2 2, ← sq_abs w, ← pow_mul]]
  rw [heven]
  -- integral_comp_abs gives 2 × half-line, with f(y) = y · exp(-t·y^4/24)
  rw [integral_comp_abs (f := fun y => y * exp (-(t * y ^ 4 / 24)))]
  rw [quartic_integral_w_exp_Ioi ht]
  ring

/-! ## Integrability on the bounded prior -/

/-- Integrability of `|w| · exp(-(t · w⁴/24))` on `ℝ`. -/
theorem quartic_integrable_abs_w {t : ℝ} (ht : 0 < t) :
    Integrable (fun w : ℝ => |w| * exp (-(t * w ^ 4 / 24))) := by
  have h := quartic_integrable_pow 1 ht
  have heq : (fun w : ℝ => w ^ 1 * Real.exp (-(t * w ^ 4 / 24))) =
             (fun w : ℝ => w * Real.exp (-(t * w ^ 4 / 24))) := by
    ext w; rw [pow_one]
  rw [heq] at h
  -- |·| of an integrable function is integrable.
  have habs := h.abs
  have heq2 : (fun w : ℝ => |w * Real.exp (-(t * w ^ 4 / 24))|) =
              (fun w : ℝ => |w| * Real.exp (-(t * w ^ 4 / 24))) := by
    ext w
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rwa [heq2] at habs

/-- Bounded-prior first absolute moment is bounded by the full-line value.
For `t > 0`, `a > 0`,
`∫_{Icc(-a,a)} |w| · exp(-(t · w⁴/24)) dw ≤ (1/2) · √(24π/t)`. -/
theorem quartic_integral_abs_w_bounded_prior_le {t a : ℝ} (ht : 0 < t) (_ha : 0 < a) :
    ∫ w in Icc (-a) a, |w| * exp (-(t * w ^ 4 / 24)) ≤
      (1/2) * Real.sqrt (24 * Real.pi / t) := by
  rw [← quartic_integral_abs_w_exp_full ht]
  -- ∫_{Icc} f ≤ ∫_ℝ f, since f is nonnegative.
  apply MeasureTheory.setIntegral_le_integral (quartic_integrable_abs_w ht)
  refine Filter.Eventually.of_forall (fun w => ?_)
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-! ## Headline: unnormalised Lipschitz estimate -/

/-- **Bounded-prior Lipschitz unnormalised estimate.** For `t > 0`, `a > 0`,
`K ≥ 0`, and `K`-Lipschitz `φ` near `0` on `[-a, a]` (i.e.
`|φ(w) − φ(0)| ≤ K · |w|` for `w ∈ [-a, a]`):

`| ∫_{[-a,a]} φ(w)·exp(-(t·w⁴/24)) dw − φ(0) · ∫_{[-a,a]} exp(-(t·w⁴/24)) dw |
   ≤ K · (1/2) · √(24π/t)`.

The bound uses the closed-form full-line first absolute moment
(`quartic_integral_abs_w_exp_full`) plus the bounded-prior monotonicity
(`quartic_integral_abs_w_bounded_prior_le`). Per the Step 2 deliberation,
the rate is `t^{-1/2}` in the *unnormalised* form; the normalised
`|⟨φ⟩_{t,a} − φ(0)| = O(t^{-1/4})` is a downstream corollary using
the bounded-prior partition function. -/
theorem quartic_lipschitz_unnormalised_bounded_prior
    {t a K : ℝ} (ht : 0 < t) (ha : 0 < a) (hK : 0 ≤ K)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hLip : ∀ w ∈ Icc (-a) a, |φ w - φ 0| ≤ K * |w|) :
    |(∫ w in Icc (-a) a, φ w * exp (-(t * w ^ 4 / 24))) -
        φ 0 * (∫ w in Icc (-a) a, exp (-(t * w ^ 4 / 24)))| ≤
      K * (1/2) * Real.sqrt (24 * Real.pi / t) := by
  -- Step 1: integrability witnesses on Icc(-a, a).
  have hg_int : Integrable (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) := by
    have h := quartic_integrable_pow 0 ht
    have heq : (fun w : ℝ => w ^ 0 * Real.exp (-(t * w ^ 4 / 24))) =
               (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24))) := by ext; simp
    rwa [heq] at h
  have hg_int_Icc : IntegrableOn (fun w : ℝ => Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-a) a) volume := hg_int.integrableOn
  -- φ is continuous, hence bounded on the compact Icc, and so is φ·g.
  have hφg_cont : Continuous (fun w : ℝ => φ w * Real.exp (-(t * w ^ 4 / 24))) :=
    hφ.mul (by fun_prop)
  have hφg_int : IntegrableOn (fun w : ℝ => φ w * Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-a) a) volume :=
    hφg_cont.integrableOn_Icc
  have hconst_int : IntegrableOn (fun w : ℝ => φ 0 * Real.exp (-(t * w ^ 4 / 24)))
      (Icc (-a) a) volume :=
    (continuous_const.mul (by fun_prop)).integrableOn_Icc
  -- Step 2: rewrite the difference as a single integral.
  have hdiff : (∫ w in Icc (-a) a, φ w * exp (-(t * w ^ 4 / 24))) -
        φ 0 * (∫ w in Icc (-a) a, exp (-(t * w ^ 4 / 24))) =
      ∫ w in Icc (-a) a, (φ w - φ 0) * exp (-(t * w ^ 4 / 24)) := by
    rw [show (fun w : ℝ => (φ w - φ 0) * exp (-(t * w ^ 4 / 24))) =
           (fun w : ℝ => φ w * exp (-(t * w ^ 4 / 24)) -
                         φ 0 * exp (-(t * w ^ 4 / 24))) from by funext w; ring]
    rw [MeasureTheory.integral_sub hφg_int hconst_int]
    rw [MeasureTheory.integral_const_mul]
  rw [hdiff]
  -- Step 3: pointwise bound + monotonicity.
  -- Key: |(φ w - φ 0) * exp(...)| = |φ w - φ 0| * exp(...) ≤ K * |w| * exp(...).
  have hpointwise : ∀ w ∈ Icc (-a) a,
      |(φ w - φ 0) * exp (-(t * w ^ 4 / 24))| ≤
        K * |w| * exp (-(t * w ^ 4 / 24)) := by
    intro w hw
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := hLip w hw
    have hexp_nn : (0 : ℝ) ≤ exp (-(t * w ^ 4 / 24)) := (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right h hexp_nn
  -- Integrability of the absolute-value function on Icc.
  have hLip_diff_int : IntegrableOn
      (fun w : ℝ => (φ w - φ 0) * exp (-(t * w ^ 4 / 24))) (Icc (-a) a) volume := by
    have h := hφg_int.sub hconst_int
    have heq : ((fun w : ℝ => φ w * exp (-(t * w ^ 4 / 24))) -
                (fun w : ℝ => φ 0 * exp (-(t * w ^ 4 / 24)))) =
               (fun w : ℝ => (φ w - φ 0) * exp (-(t * w ^ 4 / 24))) := by
      funext w; simp; ring
    rwa [heq] at h
  -- Integrability of K · |w| · exp(...) on Icc.
  have hKabsw_int_full : Integrable
      (fun w : ℝ => K * |w| * exp (-(t * w ^ 4 / 24))) := by
    have h := (quartic_integrable_abs_w ht).const_mul K
    have heq : (fun w : ℝ => K * (|w| * Real.exp (-(t * w ^ 4 / 24)))) =
               (fun w : ℝ => K * |w| * Real.exp (-(t * w ^ 4 / 24))) := by
      funext w; ring
    rwa [heq] at h
  have hKabsw_int : IntegrableOn
      (fun w : ℝ => K * |w| * exp (-(t * w ^ 4 / 24))) (Icc (-a) a) volume :=
    hKabsw_int_full.integrableOn
  calc |∫ w in Icc (-a) a, (φ w - φ 0) * exp (-(t * w ^ 4 / 24))|
      ≤ ∫ w in Icc (-a) a, |(φ w - φ 0) * exp (-(t * w ^ 4 / 24))| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ w in Icc (-a) a, K * |w| * exp (-(t * w ^ 4 / 24)) :=
        setIntegral_mono_on hLip_diff_int.abs hKabsw_int measurableSet_Icc hpointwise
    _ = K * ∫ w in Icc (-a) a, |w| * exp (-(t * w ^ 4 / 24)) := by
        rw [show (fun w : ℝ => K * |w| * exp (-(t * w ^ 4 / 24))) =
               (fun w : ℝ => K * (|w| * exp (-(t * w ^ 4 / 24)))) from by
              funext w; ring]
        rw [MeasureTheory.integral_const_mul]
    _ ≤ K * ((1/2) * Real.sqrt (24 * Real.pi / t)) :=
        mul_le_mul_of_nonneg_left (quartic_integral_abs_w_bounded_prior_le ht ha) hK
    _ = K * (1/2) * Real.sqrt (24 * Real.pi / t) := by ring

end Laplace.OneD
