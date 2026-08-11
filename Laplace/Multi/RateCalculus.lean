/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.GaussianCovariance

/-!
# Rate calculus for the pairwise moment difference

Stages J5a and J5b of the tensor programme (per the shape consult's
staging): the scalar exponential secant calculus — the FTC identity
`e^{-a} - e^{-b} = -(a-b)·∫₀¹ e^{-(b+t(a-b))}dt`, the two-sided
secant bound, and the filter limit
`(e^{-a₁} - e^{-a₂})/s → -e^{-u}·v` — and the retreating
Gaussian-tail lemma: the rate-divided integral over `ρ ≤ q‖x‖`
vanishes, by the trade `q^{-r} ≤ ρ^{-r}‖x‖^r` on the support. Also
the general-rate polynomial Gaussian integrability these and the
later J5 stages consume.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {d : ℕ}

/-- Norm powers have polynomial growth. -/
theorem hasPolynomialGrowth_norm_pow (r : ℕ) :
    HasPolynomialGrowth (fun x : EuclidD d ↦ ‖x‖ ^ r) := by
  refine ⟨1, r, zero_le_one, fun x ↦ ?_⟩
  rw [abs_of_nonneg (by positivity), one_mul]
  nlinarith [pow_nonneg (norm_nonneg x) r]

/-- General-rate polynomial Gaussian integrability: `‖x‖ⁿ·e^{-c‖x‖²}`
is integrable for every `c > 0`. -/
theorem integrable_pow_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c)
    (n : ℕ) :
    Integrable (fun x : EuclidD d ↦
      ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2)) := by
  set m : ℕ := n / 2 + 1 with hm_def
  have hn2m : n < 2 * m := by omega
  have hK : (0 : ℝ) < (2 / c) ^ m * (Nat.factorial m : ℝ) := by
    positivity
  have hdom : Integrable (fun x : EuclidD d ↦
      (1 + (2 / c) ^ m * (Nat.factorial m : ℝ)) *
        Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
    (integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact ((continuous_norm.pow n).mul
      (Real.continuous_exp.comp
        ((continuous_norm.pow 2).const_mul (-c)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm,
      abs_of_pos (Real.exp_pos _)]
    have hterm : (c / 2 * ‖x‖ ^ 2) ^ m / (Nat.factorial m : ℝ) ≤
        Real.exp (c / 2 * ‖x‖ ^ 2) := by
      refine le_trans ?_ (Real.sum_le_exp_of_nonneg
        (by positivity) (m + 1))
      exact Finset.single_le_sum
        (f := fun i ↦ (c / 2 * ‖x‖ ^ 2) ^ i / (Nat.factorial i : ℝ))
        (fun i _ ↦ by positivity) (Finset.self_mem_range_succ m)
    have hpow : ‖x‖ ^ (2 * m) ≤ (2 / c) ^ m *
        (Nat.factorial m : ℝ) * Real.exp (c / 2 * ‖x‖ ^ 2) := by
      have hkey : ‖x‖ ^ (2 * m) = (‖x‖ ^ 2) ^ m := by
        rw [pow_mul]
      rw [hkey]
      have hfac : (Nat.factorial m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_ne_zero m)
      have hc0 : (c : ℝ) ≠ 0 := hc.ne'
      have hex : (2 / c) ^ m * (Nat.factorial m : ℝ) *
          ((c / 2 * ‖x‖ ^ 2) ^ m / (Nat.factorial m : ℝ)) =
          (‖x‖ ^ 2) ^ m := by
        calc (2 / c) ^ m * (Nat.factorial m : ℝ) *
              ((c / 2 * ‖x‖ ^ 2) ^ m / (Nat.factorial m : ℝ))
            = (2 / c) ^ m * (c / 2 * ‖x‖ ^ 2) ^ m := by
              field_simp
          _ = ((2 / c) * (c / 2 * ‖x‖ ^ 2)) ^ m := (mul_pow _ _ _).symm
          _ = (‖x‖ ^ 2) ^ m := by
              congr 1
              field_simp
      rw [← hex]
      exact mul_le_mul_of_nonneg_left hterm (by positivity)
    have hcases : ‖x‖ ^ n ≤ 1 + ‖x‖ ^ (2 * m) := by
      rcases le_total ‖x‖ 1 with hy | hy
      · have h1 : ‖x‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg x) hy
        have h2 : (0 : ℝ) ≤ ‖x‖ ^ (2 * m) := by positivity
        linarith
      · have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ (2 * m) :=
          pow_le_pow_right₀ hy (by omega)
        linarith
    calc ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2)
        ≤ (1 + ‖x‖ ^ (2 * m)) * Real.exp (-c * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hcases (Real.exp_pos _).le
      _ ≤ (1 + (2 / c) ^ m * (Nat.factorial m : ℝ) *
            Real.exp (c / 2 * ‖x‖ ^ 2)) * Real.exp (-c * ‖x‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith [hpow]
      _ = Real.exp (-c * ‖x‖ ^ 2) + (2 / c) ^ m *
            (Nat.factorial m : ℝ) *
            Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
          rw [add_mul, one_mul, mul_assoc, ← Real.exp_add]
          have harg : c / 2 * ‖x‖ ^ 2 + -c * ‖x‖ ^ 2 =
              -(c / 2) * ‖x‖ ^ 2 := by ring
          rw [harg]
      _ ≤ (1 + (2 / c) ^ m * (Nat.factorial m : ℝ)) *
            Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
          have hmono : Real.exp (-c * ‖x‖ ^ 2) ≤
              Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [sq_nonneg ‖x‖]
          nlinarith [Real.exp_pos (-(c / 2) * ‖x‖ ^ 2)]

/-- Polynomial-growth observables are integrable against every
Gaussian rate. -/
theorem integrable_mul_exp_neg_mul_sq_of_polynomialGrowth {c : ℝ}
    (hc : 0 < c) {P : EuclidD d → ℝ}
    (hP_meas : AEStronglyMeasurable P (volume : Measure (EuclidD d)))
    (hP : HasPolynomialGrowth P) :
    Integrable (fun x : EuclidD d ↦
      P x * Real.exp (-c * ‖x‖ ^ 2)) := by
  obtain ⟨C, n, hC, h⟩ := hP
  have hdom : Integrable (fun x : EuclidD d ↦
      C * (Real.exp (-c * ‖x‖ ^ 2) +
        ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2))) :=
    ((integrable_exp_neg_mul_sq_norm hc).add
      (integrable_pow_mul_exp_neg_mul_sq hc n)).const_mul C
  refine hdom.mono'
    (hP_meas.mul (Real.continuous_exp.comp
      ((continuous_norm.pow 2).const_mul (-c))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |P x| * Real.exp (-c * ‖x‖ ^ 2)
      ≤ C * (1 + ‖x‖ ^ n) * Real.exp (-c * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (h x) (Real.exp_pos _).le
    _ = C * (Real.exp (-c * ‖x‖ ^ 2) +
          ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2)) := by ring

/-- **The FTC secant identity** (J5a): the difference of exponentials
factors through the secant integral, with no chosen mean-value
point. -/
theorem exp_neg_sub_exp_neg_eq (a b : ℝ) :
    Real.exp (-a) - Real.exp (-b) =
      -(a - b) * ∫ t in (0 : ℝ)..1,
        Real.exp (-(b + t * (a - b))) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ Real.exp (-(b + t * (a - b))))
        (-(a - b) * Real.exp (-(b + t * (a - b)))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ ↦ -(b + t * (a - b)))
        (-(a - b)) t := by
      have hb : HasDerivAt (fun t : ℝ ↦ b + t * (a - b))
          (a - b) t := by
        simpa using ((hasDerivAt_id t).mul_const (a - b)).const_add b
      exact hb.neg
    have h2 := (Real.hasDerivAt_exp (-(b + t * (a - b)))).comp t h1
    simpa [mul_comm] using h2
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ -(a - b) * Real.exp (-(b + t * (a - b))))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have h0 : b + 1 * (a - b) = a := by ring
  have h1 : b + 0 * (a - b) = b := by ring
  rw [h0, h1] at hftc
  linarith [hftc]

/-- **The two-sided secant bound** (the multivariate sibling of the
1D JetDifference bound). -/
theorem abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤
      |a - b| * max (Real.exp (-a)) (Real.exp (-b)) := by
  rw [exp_neg_sub_exp_neg_eq a b, abs_mul, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := max (Real.exp (-a)) (Real.exp (-b)))
    (f := fun t : ℝ ↦ Real.exp (-(b + t * (a - b))))
    (a := 0) (b := 1) ?_
  · simpa using hbound
  · intro t ht
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmin : min a b ≤ b + t * (a - b) := by
      rcases le_total a b with hab | hab
      · have h1 : min a b = a := min_eq_left hab
        nlinarith [ht.1, ht.2]
      · have h1 : min a b = b := min_eq_right hab
        nlinarith [ht.1, ht.2]
    calc Real.exp (-(b + t * (a - b))) ≤ Real.exp (-(min a b)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = max (Real.exp (-a)) (Real.exp (-b)) := by
          rcases le_total a b with hab | hab
          · rw [min_eq_left hab,
              max_eq_left (Real.exp_le_exp.mpr (by linarith))]
          · rw [min_eq_right hab,
              max_eq_right (Real.exp_le_exp.mpr (by linarith))]

/-- **The scalar rate limit** (J5a): if both exponents converge to a
common value and their difference has a rate limit, the divided
exponential difference converges to `-e^{-u}·v`. -/
theorem tendsto_exp_neg_sub_div {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated]
    {a₁ a₂ s : α → ℝ} {u v : ℝ}
    (ha₁ : Tendsto a₁ l (𝓝 u)) (ha₂ : Tendsto a₂ l (𝓝 u))
    (hd : Tendsto (fun q ↦ (a₁ q - a₂ q) / s q) l (𝓝 v)) :
    Tendsto (fun q ↦
        (Real.exp (-(a₁ q)) - Real.exp (-(a₂ q))) / s q) l
      (𝓝 (-(Real.exp (-u)) * v)) := by
  have hsec : Tendsto (fun q ↦ ∫ t in (0 : ℝ)..1,
      Real.exp (-(a₂ q + t * (a₁ q - a₂ q)))) l
      (𝓝 (Real.exp (-u))) := by
    have hIoc : ∀ q, (∫ t in (0 : ℝ)..1,
        Real.exp (-(a₂ q + t * (a₁ q - a₂ q)))) =
        ∫ t in Set.Ioc (0 : ℝ) 1,
          Real.exp (-(a₂ q + t * (a₁ q - a₂ q))) := fun q ↦
      intervalIntegral.integral_of_le zero_le_one
    have htarget : Real.exp (-u) = ∫ _ in Set.Ioc (0 : ℝ) 1,
        Real.exp (-u) := by
      rw [setIntegral_const]
      simp
    rw [htarget]
    refine Tendsto.congr (fun q ↦ (hIoc q).symm) ?_
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ Real.exp (-u + 1)) ?_ ?_ ?_ ?_
    · filter_upwards with q
      exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · have hev₁ : ∀ᶠ q in l, u - 1 < a₁ q :=
        ha₁ (eventually_gt_nhds (by linarith))
      have hev₂ : ∀ᶠ q in l, u - 1 < a₂ q :=
        ha₂ (eventually_gt_nhds (by linarith))
      filter_upwards [hev₁, hev₂] with q h1 h2
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t hmem
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hconv : u - 1 < a₂ q + t * (a₁ q - a₂ q) := by
        rcases le_total (a₁ q) (a₂ q) with hab | hab
        · nlinarith [hmem.1, hmem.2]
        · nlinarith [hmem.1, hmem.2]
      linarith
    · exact integrableOn_const
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · refine Filter.Eventually.of_forall fun t ↦ ?_
      have harg : Tendsto (fun q ↦ a₂ q + t * (a₁ q - a₂ q)) l
          (𝓝 u) := by
        have := ha₂.add (((ha₁.sub ha₂).const_mul t))
        simpa using this
      exact (Real.continuous_exp.continuousAt.tendsto.comp harg.neg)
  have heq : ∀ q, (Real.exp (-(a₁ q)) - Real.exp (-(a₂ q))) / s q =
      -((a₁ q - a₂ q) / s q) *
        ∫ t in (0 : ℝ)..1,
          Real.exp (-(a₂ q + t * (a₁ q - a₂ q))) := by
    intro q
    rw [exp_neg_sub_exp_neg_eq (a₁ q) (a₂ q)]
    rw [neg_mul, neg_div, neg_mul, neg_inj, mul_div_right_comm]
  have hfinal := (hd.neg.mul hsec)
  rw [show -v * Real.exp (-u) = -(Real.exp (-u)) * v by ring] at hfinal
  exact hfinal.congr fun q ↦ (heq q).symm

/-- **The retreating Gaussian-tail lemma** (J5b): the rate-divided
integral of a polynomial-growth observable against a Gaussian over
the region `ρ ≤ q‖x‖` vanishes as `q → 0⁺`. -/
theorem tendsto_integral_retreating_tail_div_pow
    {P : EuclidD d → ℝ}
    (hP_meas : AEStronglyMeasurable P (volume : Measure (EuclidD d)))
    (hP_growth : HasPolynomialGrowth P)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (r : ℕ) :
    Tendsto (fun q : ℝ ↦ (∫ x : EuclidD d,
        Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
          (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) x) / q ^ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hdiv : ∀ q : ℝ, (∫ x : EuclidD d,
      Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
        (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) x) / q ^ r =
      ∫ x : EuclidD d,
        (Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
          (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) x) / q ^ r := by
    intro q
    rw [integral_div]
  have hmain : Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d,
      (Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
        (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) x) / q ^ r)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ _ : EuclidD d, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : EuclidD d ↦ (ρ⁻¹) ^ r *
        (|P x| * ‖x‖ ^ r * Real.exp (-c * ‖x‖ ^ 2))) ?_ ?_ ?_ ?_
    · filter_upwards with q
      have hset : MeasurableSet {x : EuclidD d | ρ ≤ q * ‖x‖} := by
        apply measurableSet_le measurable_const
        fun_prop
      exact (((hP_meas.mul (Real.continuous_exp.comp
        ((continuous_norm.pow 2).const_mul (-c))).aestronglyMeasurable).indicator
        hset).mul_const ((q ^ r)⁻¹))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      refine Filter.Eventually.of_forall fun x ↦ ?_
      by_cases hmem : x ∈ {x : EuclidD d | ρ ≤ q * ‖x‖}
      · rw [Set.indicator_of_mem hmem]
        have hqx : ρ ≤ q * ‖x‖ := hmem
        have hq0 : (0 : ℝ) < q := hq
        have htrade : (q ^ r)⁻¹ ≤ (ρ⁻¹) ^ r * ‖x‖ ^ r := by
          have hqinv : q⁻¹ ≤ ρ⁻¹ * ‖x‖ := by
            rw [inv_le_iff_one_le_mul₀ hq0]
            calc (1 : ℝ) = ρ⁻¹ * ρ := by
                  field_simp
              _ ≤ ρ⁻¹ * (q * ‖x‖) := by
                  apply mul_le_mul_of_nonneg_left hqx
                    (by positivity)
              _ = ρ⁻¹ * ‖x‖ * q := by ring
          calc (q ^ r)⁻¹ = (q⁻¹) ^ r := by
                rw [inv_pow]
            _ ≤ (ρ⁻¹ * ‖x‖) ^ r :=
                pow_le_pow_left₀ (by positivity) hqinv r
            _ = (ρ⁻¹) ^ r * ‖x‖ ^ r := mul_pow _ _ _
        rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul,
          abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_pos (by positivity : (0:ℝ) < (q ^ r)⁻¹)]
        calc |P x| * Real.exp (-c * ‖x‖ ^ 2) * (q ^ r)⁻¹
            ≤ |P x| * Real.exp (-c * ‖x‖ ^ 2) *
                ((ρ⁻¹) ^ r * ‖x‖ ^ r) := by
              apply mul_le_mul_of_nonneg_left htrade (by positivity)
          _ = (ρ⁻¹) ^ r * (|P x| * ‖x‖ ^ r *
                Real.exp (-c * ‖x‖ ^ 2)) := by ring
      · rw [Set.indicator_of_notMem hmem, zero_div, norm_zero]
        positivity
    · refine ((integrable_mul_exp_neg_mul_sq_of_polynomialGrowth hc
        ?_ ?_).const_mul _)
      · exact (hP_meas.norm.mul
          (continuous_norm.pow r).aestronglyMeasurable)
      · obtain ⟨C, n, hC, h⟩ := hP_growth
        have habs : HasPolynomialGrowth
            (fun x : EuclidD d ↦ |P x|) := by
          refine ⟨C, n, hC, fun x ↦ ?_⟩
          rw [abs_abs]
          exact h x
        exact habs.mul (hasPolynomialGrowth_norm_pow r)
    · refine Filter.Eventually.of_forall fun x ↦ ?_
      rcases eq_or_ne x 0 with rfl | hx
      · have hnever : ∀ᶠ q in 𝓝[>] (0 : ℝ),
            Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
              (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) (0 : EuclidD d) /
              q ^ r = 0 := by
          filter_upwards with q
          rw [Set.indicator_of_notMem, zero_div]
          simp [hρ.not_ge]
        exact tendsto_const_nhds.congr'
          (hnever.mono fun q hq ↦ hq.symm)
      · have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
        have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < ρ / ‖x‖ := by
          apply eventually_nhdsWithin_of_eventually_nhds
          exact eventually_lt_nhds (by positivity)
        have hnever : ∀ᶠ q in 𝓝[>] (0 : ℝ),
            Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
              (fun x ↦ P x * Real.exp (-c * ‖x‖ ^ 2)) x / q ^ r = 0 := by
          filter_upwards [hev, self_mem_nhdsWithin] with q hqρ hq0
          rw [Set.indicator_of_notMem, zero_div]
          intro hmem
          have : ρ ≤ q * ‖x‖ := hmem
          have : q * ‖x‖ < ρ / ‖x‖ * ‖x‖ :=
            mul_lt_mul_of_pos_right hqρ hnx
          rw [div_mul_cancel₀ _ hnx.ne'] at this
          linarith
        exact tendsto_const_nhds.congr'
          (hnever.mono fun q hq ↦ hq.symm)
  have hz : (∫ _ : EuclidD d, (0 : ℝ)) = 0 := by simp
  rw [hz] at hmain
  exact hmain.congr fun q ↦ (hdiv q).symm
end Laplace.Multi
