/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensityBox

/-!
# The log-weighted primitive (grammar §4.2, minimal block of multiplicity `m`)

The divide-and-integrate tower on a primitive `G(x) = ∫₀^x g` is the log-weighted integral

  `iterDivPrim G j y = (1/j!) ∫₀^y (log(y/t))^j g(t) dt`   (`iterDivPrim_primitive`),

proved by Fubini on the triangle `0 < s ≤ t ≤ y`. Applied to the weighted kernel
`g(t) = t^{p-1} e^{-βt² + βat}` this gives the **exact product-density formula** for the
equal-exponent chart block: with `q_i = (h_i+1)/k_i = p` for `i ≤ d`,

  `Z_{d+1}(c) = (∏ k_i⁻¹) c^{-p} (1/d!) ∫₀^{cB} (log(cB/t))^d t^{p-1} e^{-βt²+βat} dt`,
  `B = b^{∑k_i}`

(`iterChartGen_eq_logWeighted`). We also record integrability of `|log t|^i t^γ e^{-βt²+βat}` on
`(0,∞)`, the domination input for the multiplicity-`m` state-density theorem. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- `∫_s^y (log t − log s)^j / t dt = (log y − log s)^{j+1}/(j+1)` for `0 < s ≤ y`. -/
theorem integral_Icc_log_pow_div (j : ℕ) (s y : ℝ) (hs : 0 < s) (hsy : s ≤ y) :
    ∫ t in Icc s y, (Real.log t - Real.log s) ^ j / t
      = (Real.log y - Real.log s) ^ (j + 1) / (j + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsy]
  have hderiv : ∀ t ∈ uIcc s y, HasDerivAt (fun t => (Real.log t - Real.log s) ^ (j + 1) / (j + 1))
      ((Real.log t - Real.log s) ^ j / t) t := by
    intro t ht
    rw [uIcc_of_le hsy] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hs ht.1
    have h := (((Real.hasDerivAt_log ht0.ne').sub_const (Real.log s)).pow (j + 1)).div_const
      ((j : ℝ) + 1)
    refine h.congr_deriv ?_
    have : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    simp
  have hcont : ContinuousOn (fun t => (Real.log t - Real.log s) ^ j / t) (uIcc s y) := by
    rw [uIcc_of_le hsy]
    refine ContinuousOn.div ?_ continuousOn_id fun t ht => (lt_of_lt_of_le hs ht.1).ne'
    exact ((Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hs ht.1).ne').sub
      continuousOn_const).pow j
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

/-- The log-weighted primitive `Φ_j(g)(y) = (1/j!) ∫₀^y (log y − log t)^j g(t) dt`. -/
noncomputable def logWeightedPrim (g : ℝ → ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  1 / (j.factorial : ℝ) * ∫ t in Ioc (0 : ℝ) y, (Real.log y - Real.log t) ^ j * g t

/-- The triangle integrand `f(t, s) = 1_{s ≤ t} (log t − log s)^j g(s)/t`. -/
noncomputable def triIntegrand (g : ℝ → ℝ) (j : ℕ) (t s : ℝ) : ℝ :=
  if s ≤ t then (Real.log t - Real.log s) ^ j * g s / t else 0

theorem triIntegrand_measurable (g : ℝ → ℝ) (hg : Measurable g) (j : ℕ) :
    Measurable (Function.uncurry (triIntegrand g j)) := by
  unfold triIntegrand Function.uncurry
  refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
  fun_prop

/-- For `t ∈ (0, y]`, integrating the triangle integrand in `s` over `(0, y]` gives the inner
integral over `(0, t]`. -/
theorem triIntegrand_integral_s (g : ℝ → ℝ) (j : ℕ) (y t : ℝ) (ht : t ∈ Ioc (0 : ℝ) y) :
    ∫ s in Ioc (0 : ℝ) y, triIntegrand g j t s
      = (∫ s in Ioc (0 : ℝ) t, (Real.log t - Real.log s) ^ j * g s) / t := by
  have h1 : ∀ s, triIntegrand g j t s
      = (Iic t).indicator (fun s => (Real.log t - Real.log s) ^ j * g s / t) s := by
    intro s; simp only [triIntegrand, indicator_apply, mem_Iic]
  simp_rw [h1]
  have hset : Ioc (0 : ℝ) y ∩ Iic t = Ioc 0 t := by
    ext s; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
  rw [setIntegral_indicator measurableSet_Iic, ← integral_div, hset]

/-- For `s ∈ (0, y]`, integrating the triangle integrand in `t` over `(0, y]` gives
`g(s) (log y − log s)^{j+1}/(j+1)`. -/
theorem triIntegrand_integral_t (g : ℝ → ℝ) (j : ℕ) (y s : ℝ) (hs : s ∈ Ioc (0 : ℝ) y) :
    ∫ t in Ioc (0 : ℝ) y, triIntegrand g j t s
      = g s * ((Real.log y - Real.log s) ^ (j + 1) / (j + 1)) := by
  have h1 : ∀ t, triIntegrand g j t s
      = (Ici s).indicator (fun t => g s * ((Real.log t - Real.log s) ^ j / t)) t := by
    intro t; simp only [triIntegrand, indicator_apply, mem_Ici]
    split_ifs <;> ring_nf
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Ici, integral_const_mul]
  have hset : Ioc (0 : ℝ) y ∩ Ici s = Icc s y := by
    ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hs.1 h1, h2⟩, h1⟩
  rw [hset, integral_Icc_log_pow_div j s y hs.1 hs.2]

/-- The `t`-section of the triangle integrand is integrable for `s ∈ (0, y]`. -/
theorem triIntegrand_integrable_t (g : ℝ → ℝ) (j : ℕ) (y s : ℝ) (hs : s ∈ Ioc (0 : ℝ) y) :
    Integrable (fun t => triIntegrand g j t s) ((volume : Measure ℝ).restrict (Ioc 0 y)) := by
  have h1 : (fun t => triIntegrand g j t s)
      = (Ici s).indicator (fun t => g s * ((Real.log t - Real.log s) ^ j / t)) := by
    funext t; simp only [triIntegrand, indicator_apply, mem_Ici]
    split_ifs <;> ring_nf
  rw [h1, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici s ∩ Ioc (0 : ℝ) y = Icc s y := by
    ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h3, ⟨_, h2⟩⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨lt_of_lt_of_le hs.1 h1, h2⟩⟩
  rw [hset]
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  refine continuousOn_const.mul (ContinuousOn.div ?_ continuousOn_id
    fun t ht => (lt_of_lt_of_le hs.1 ht.1).ne')
  exact ((Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hs.1 ht.1).ne').sub
    continuousOn_const).pow j

/-- Integrability of the triangle integrand on the square, from integrability of
`(log y − log s)^{j+1} g(s)`. -/
theorem triIntegrand_integrable (g : ℝ → ℝ) (hg : Measurable g) (j : ℕ) (y : ℝ)
    (hint : IntegrableOn (fun s => (Real.log y - Real.log s) ^ (j + 1) * g s) (Ioc 0 y)) :
    Integrable (Function.uncurry (triIntegrand g j))
      (((volume : Measure ℝ).restrict (Ioc 0 y)).prod
        ((volume : Measure ℝ).restrict (Ioc 0 y))) := by
  rw [integrable_prod_iff' (triIntegrand_measurable g hg j).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun s hs => triIntegrand_integrable_t g j y s hs
  · have habs : ∀ s ∈ Ioc (0 : ℝ) y,
        ∫ t in Ioc (0 : ℝ) y, ‖Function.uncurry (triIntegrand g j) (t, s)‖
          = |g s| * ((Real.log y - Real.log s) ^ (j + 1) / (j + 1)) := by
      intro s hs
      have : ∀ t ∈ Ioc (0 : ℝ) y, ‖Function.uncurry (triIntegrand g j) (t, s)‖
          = triIntegrand (fun s => |g s|) j t s := by
        intro t ht
        simp only [Function.uncurry, triIntegrand, Real.norm_eq_abs]
        split_ifs with hst
        · have hlog : 0 ≤ Real.log t - Real.log s :=
            sub_nonneg.2 (Real.log_le_log hs.1 hst)
          rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hlog j), abs_of_pos ht.1]
        · simp
      rw [setIntegral_congr_fun measurableSet_Ioc this, triIntegrand_integral_t]
      exact hs
    refine (Integrable.congr ?_ ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun s hs => (habs s hs).symm)))
    have : (fun s => |g s| * ((Real.log y - Real.log s) ^ (j + 1) / (j + 1)))
        = fun s => (1 / ((j : ℝ) + 1)) * ((Real.log y - Real.log s) ^ (j + 1) * |g s|) := by
      funext s; ring
    rw [this]
    refine Integrable.const_mul ?_ _
    refine (hint.norm).congr ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun s hs => ?_))
    have hlog : 0 ≤ Real.log y - Real.log s := sub_nonneg.2 (Real.log_le_log hs.1 hs.2)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hlog _)]

/-- **The tower on a primitive is the log-weighted primitive**:
`iterDivPrim (∫₀^· g) j y = (1/j!) ∫₀^y (log(y/t))^j g(t) dt` for `y > 0`. -/
theorem iterDivPrim_primitive (g : ℝ → ℝ) (hg : Measurable g)
    (hint : ∀ j : ℕ, ∀ y, 0 < y →
      IntegrableOn (fun s => (Real.log y - Real.log s) ^ j * g s) (Ioc 0 y))
    (j : ℕ) (y : ℝ) (hy : 0 < y) :
    iterDivPrim (fun x => ∫ t in Ioc (0 : ℝ) x, g t) j y = logWeightedPrim g j y := by
  induction j generalizing y with
  | zero =>
    simp only [iterDivPrim_zero, logWeightedPrim, Nat.factorial_zero, Nat.cast_one, pow_zero,
      one_mul, div_one]
  | succ j ih =>
    rw [iterDivPrim_succ]
    have hpt : ∀ t ∈ Ioc (0 : ℝ) y,
        iterDivPrim (fun x => ∫ t in Ioc (0 : ℝ) x, g t) j t / t
          = 1 / (j.factorial : ℝ) * ∫ s in Ioc (0 : ℝ) y, triIntegrand g j t s := by
      intro t ht
      rw [ih t ht.1, triIntegrand_integral_s g j y t ht, logWeightedPrim]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
      integral_integral_swap (triIntegrand_integrable g hg j y (hint (j + 1) y hy)),
      setIntegral_congr_fun measurableSet_Ioc (fun s hs => triIntegrand_integral_t g j y s hs),
      logWeightedPrim]
    have : ∀ s, g s * ((Real.log y - Real.log s) ^ (j + 1) / ((j : ℝ) + 1))
        = (1 / ((j : ℝ) + 1)) * ((Real.log y - Real.log s) ^ (j + 1) * g s) := by
      intro s; ring
    simp_rw [this]
    rw [integral_const_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hj : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-- `|log t| ≤ t^{-ε}/ε` on `(0, 1]`. -/
theorem abs_log_le_rpow_neg_div (t ε : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    |Real.log t| ≤ t ^ (-ε) / ε := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  rw [abs_of_nonpos hlog, ← Real.log_inv, Real.rpow_neg ht.le, ← Real.inv_rpow ht.le]
  exact Real.log_le_rpow_div (inv_nonneg.2 ht.le) hε

/-- `|log t| ≤ t` on `[1, ∞)`. -/
theorem abs_log_le_self (t : ℝ) (ht : 1 ≤ t) : |Real.log t| ≤ t := by
  rw [abs_of_nonneg (Real.log_nonneg ht)]
  linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos ht)]

/-- **Log-power weighted kernel integrability**: `|log t|^i t^γ e^{-βt²+βat}` is integrable on
`(0, ∞)` for `γ > -1`. -/
theorem logPow_weightedKernel_integrableOn (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (i : ℕ) :
    IntegrableOn (fun t => |Real.log t| ^ i * (t ^ γ * quadKernel β a t)) (Ioi 0) := by
  have hmeas : Measurable fun t : ℝ => |Real.log t| ^ i * (t ^ γ * quadKernel β a t) := by
    unfold quadKernel; fun_prop
  set ε : ℝ := (γ + 1) / (2 * (i + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by positivity)
  have hεi : ε * i ≤ (γ + 1) / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (i : ℝ), (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hγ' : -1 < γ - ε * i := by linarith
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · -- near 0: `|log t|^i ≤ ε^{-i} t^{-εi}`
    have hdom : IntegrableOn (fun t : ℝ => ε⁻¹ ^ i * (t ^ (γ - ε * i) * quadKernel β a t))
        (Ioc 0 1) :=
      ((weightedKernel_integrableOn β a (γ - ε * i) hβ hγ').mono_set
        Ioc_subset_Ioi_self).const_mul _
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => ?_))
    have hq : 0 ≤ t ^ γ * quadKernel β a t :=
      mul_nonneg (Real.rpow_nonneg ht.1.le _) (quadKernel_pos β a t).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hq)]
    have h1 : |Real.log t| ^ i ≤ (t ^ (-ε) / ε) ^ i :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_rpow_neg_div t ε ht.1 ht.2 hεpos) i
    have h2 : (t ^ (-ε) / ε) ^ i = ε⁻¹ ^ i * t ^ (-(ε * i)) := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht.1.le, div_eq_mul_inv, mul_comm,
        neg_mul, inv_pow]
    have h3 : t ^ (γ - ε * i) = t ^ (-(ε * i)) * t ^ γ := by
      rw [← Real.rpow_add ht.1]; ring_nf
    rw [h3]
    calc |Real.log t| ^ i * (t ^ γ * quadKernel β a t)
        ≤ (ε⁻¹ ^ i * t ^ (-(ε * i))) * (t ^ γ * quadKernel β a t) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hq
      _ = _ := by ring
  · -- near ∞: `|log t|^i ≤ t^i`
    have hγ'' : -1 < γ + i := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hdom : IntegrableOn (fun t : ℝ => t ^ (γ + i) * quadKernel β a t) (Ioi 1) :=
      (weightedKernel_integrableOn β a (γ + i) hβ hγ'').mono_set (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hq : 0 ≤ t ^ γ * quadKernel β a t :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (quadKernel_pos β a t).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hq)]
    have h1 : |Real.log t| ^ i ≤ t ^ i := pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_self t ht1) i
    have h3 : t ^ (γ + i) = t ^ i * t ^ γ := by
      rw [Real.rpow_add ht0, Real.rpow_natCast]; ring
    rw [h3, mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 hq

/-- `(log y − log t)^j t^γ e^{-βt²+βat}` is integrable on `(0, y]` for `γ > -1`. -/
theorem logPow_weightedKernel_integrableOn_Ioc (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (j : ℕ)
    (y : ℝ) :
    IntegrableOn (fun t => (Real.log y - Real.log t) ^ j * (t ^ γ * quadKernel β a t))
      (Ioc 0 y) := by
  have hmeas : Measurable fun t : ℝ =>
      (Real.log y - Real.log t) ^ j * (t ^ γ * quadKernel β a t) := by
    unfold quadKernel; fun_prop
  -- `(A + x)^j = ∑ binom(j,i) A^{j-i} x^i`, each term integrable
  have hdom : IntegrableOn (fun t : ℝ => ∑ i ∈ Finset.range (j + 1),
      (|Real.log y| ^ i * (j.choose i : ℝ)) * (|Real.log t| ^ (j - i) * (t ^ γ * quadKernel β a t)))
      (Ioc 0 y) := by
    refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
    exact (logPow_weightedKernel_integrableOn β a γ hβ hγ (j - i)).mono_set Ioc_subset_Ioi_self
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun t ht => ?_))
  have hq : 0 ≤ t ^ γ * quadKernel β a t :=
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (quadKernel_pos β a t).le
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq]
  have h1 : |Real.log y - Real.log t| ^ j ≤ (|Real.log y| + |Real.log t|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) j
  calc |Real.log y - Real.log t| ^ j * (t ^ γ * quadKernel β a t)
      ≤ (|Real.log y| + |Real.log t|) ^ j * (t ^ γ * quadKernel β a t) :=
        mul_le_mul_of_nonneg_right h1 hq
    _ = _ := by
        rw [add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- The weighted primitive is the primitive of the weighted kernel (definitional). -/
theorem weightedPrimitive_eq_primitive (β a γ : ℝ) :
    weightedPrimitive β a γ = fun x => ∫ t in Ioc (0 : ℝ) x, t ^ γ * quadKernel β a t := rfl

/-- **Log-weighted form of the iterated weighted primitive**. -/
theorem iterWeightedPrim_eq_logWeighted (β a p : ℝ) (hβ : 0 < β) (hp : 0 < p) (j : ℕ) (y : ℝ)
    (hy : 0 < y) :
    iterDivPrim (weightedPrimitive β a (p - 1)) j y
      = logWeightedPrim (fun t => t ^ (p - 1) * quadKernel β a t) j y := by
  rw [weightedPrimitive_eq_primitive]
  refine iterDivPrim_primitive _ (by unfold quadKernel; fun_prop) (fun j y _ => ?_) j y hy
  exact logPow_weightedKernel_integrableOn_Ioc β a (p - 1) hβ (by linarith) j y

/-- **Exact product-density formula for the equal-exponent block**:
`Z_{d+1}(c) = (∏_{i ≤ d} k_i⁻¹) c^{-p} (1/d!) ∫₀^{cB} (log(cB) − log t)^d t^{p-1} e^{-βt²+βat} dt`.
-/
theorem iterChartGen_eq_logWeighted (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p) (c : ℝ) (hc : 0 < c) :
    iterChartGen β a b k h (d + 1) c
      = (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * c ^ (-p)
        * logWeightedPrim (fun t => t ^ (p - 1) * quadKernel β a t) d
            (c * b ^ (∑ i ∈ Finset.range (d + 1), k i)) := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le d)]; exact chartExp_pos k h hk 0
  rw [iterChartGen_succ_eq β a b k h p hb hk d hp c hc,
    iterWeightedPrim_eq_logWeighted β a p hβ hp0 d _ (by positivity)]

end Laplace.Grammar
