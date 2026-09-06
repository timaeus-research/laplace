/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogWeightedPrim

/-!
# Minimal block II: envelopes and the scale limit (grammar §4.2, multiplicity `m`)

For an equal-exponent block `q_0 = … = q_d = p` with constant `ξ = a`, the exact product-density
formula of unit 73 gives

* a **uniform envelope**, valid at every scale `c > 0` and uniformly in `|a| ≤ L`:
  `c^p Z_{d+1}(c) ≤ (∏ k_i⁻¹)(1/d!) E(β,L,p,d) (1 + log₊(cB))^d`  (`iterChartGen_block_le`);
* the **scale limit**: for every fixed `γ > 0`,
  `N^p Z_{d+1}(Nγ) / (log N)^d → (∏ k_i⁻¹)(1/d!) γ^{-p} A_{p-1}(a)`  (`iterChartGen_block_tendsto`),
  by dominated convergence in the log-weighted integral.

We also record the polynomial-log envelope of the tower on any admissible base
(`iterDivPrim_le_polyLog`), used for blocks with a non-minimal coordinate. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- `log₊ x = max 0 (log x)`. -/
noncomputable def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := le_max_left _ _

theorem log_le_logPlus (x : ℝ) : Real.log x ≤ logPlus x := le_max_right _ _

/-- `log₊(xy) ≤ log₊ x + log₊ y` for `x, y > 0`. -/
theorem logPlus_mul_le (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logPlus (x * y) ≤ logPlus x + logPlus y := by
  unfold logPlus
  rw [Real.log_mul hx.ne' hy.ne']
  rcases le_or_gt 0 (Real.log x + Real.log y) with h | h
  · rw [max_eq_right h]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
  · rw [max_eq_left h.le]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)

/-- `log₊ x ≤ log x` for `x ≥ 1`. -/
theorem logPlus_eq_log (x : ℝ) (hx : 1 ≤ x) : logPlus x = Real.log x :=
  max_eq_right (Real.log_nonneg hx)

/-- **Polynomial-log envelope of the tower on an admissible base**, at every `x > 0`. -/
theorem iterDivPrim_le_polyLog {G : ℝ → ℝ} {A M C δ ε : ℝ} (hG : LogBase G A M C δ ε) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, 0 < x → iterDivPrim G m x ≤ K * (1 + logPlus x) ^ m := by
  refine ⟨(∑ i ∈ Finset.range (m + 1), |divCoeff G A m i|) + M / ε ^ m + C / δ ^ m, ?_, ?_⟩
  · have hM : 0 ≤ M := by
      have := hG.tail 1 le_rfl
      simp only [Real.rpow_neg zero_le_one, Real.one_rpow, inv_one, mul_one] at this
      exact (abs_nonneg _).trans this
    have hC : 0 ≤ C := by
      have h1 := hG.le_pow 1 one_pos le_rfl
      rw [Real.one_rpow, mul_one] at h1
      exact (hG.nonneg 1).trans h1
    have := hG.ε_pos; have := hG.δ_pos
    positivity
  intro x hx
  have hlp := logPlus_nonneg x
  have hpow_ge : (1 : ℝ) ≤ (1 + logPlus x) ^ m := one_le_pow₀ (by linarith)
  rcases le_or_gt x 1 with hx1 | hx1
  · -- `x ≤ 1`: `H_m(x) ≤ C/δ^m x^δ ≤ C/δ^m`
    have h1 := (iterDivPrim_props hG m).2.2.1 x hx hx1
    have hxδ : x ^ δ ≤ 1 := Real.rpow_le_one hx.le hx1 hG.δ_pos.le
    have hC : 0 ≤ C / δ ^ m := by
      have h1' := hG.le_pow 1 one_pos le_rfl
      rw [Real.one_rpow, mul_one] at h1'
      have hδ := hG.δ_pos
      exact div_nonneg ((hG.nonneg 1).trans h1') (by positivity)
    have hM : 0 ≤ M / ε ^ m := by
      have := hG.tail 1 le_rfl
      simp only [Real.rpow_neg zero_le_one, Real.one_rpow, inv_one, mul_one] at this
      have hε := hG.ε_pos
      exact div_nonneg ((abs_nonneg _).trans this) (by positivity)
    have hS : 0 ≤ ∑ i ∈ Finset.range (m + 1), |divCoeff G A m i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    calc iterDivPrim G m x ≤ C / δ ^ m * x ^ δ := h1
      _ ≤ C / δ ^ m * 1 := by gcongr
      _ ≤ ((∑ i ∈ Finset.range (m + 1), |divCoeff G A m i|) + M / ε ^ m + C / δ ^ m) * 1 := by
          gcongr; linarith
      _ ≤ _ := by gcongr
  · -- `x > 1`: expansion plus remainder
    have hx1' : (1 : ℝ) ≤ x := hx1.le
    have hexp := iterDivPrim_expansion hG m x hx1'
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1'
    have hlp' : logPlus x = Real.log x := logPlus_eq_log x hx1'
    have hxε : x ^ (-ε) ≤ 1 := by
      rw [Real.rpow_neg hx.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow hx1' hG.ε_pos.le)
    have hM : 0 ≤ M / ε ^ m := by
      have := hG.tail 1 le_rfl
      simp only [Real.rpow_neg zero_le_one, Real.one_rpow, inv_one, mul_one] at this
      have hε := hG.ε_pos
      exact div_nonneg ((abs_nonneg _).trans this) (by positivity)
    have hC : 0 ≤ C / δ ^ m := by
      have h1' := hG.le_pow 1 one_pos le_rfl
      rw [Real.one_rpow, mul_one] at h1'
      have hδ := hG.δ_pos
      exact div_nonneg ((hG.nonneg 1).trans h1') (by positivity)
    have hsum : ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log x ^ i
        ≤ (∑ i ∈ Finset.range (m + 1), |divCoeff G A m i|) * (1 + logPlus x) ^ m := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      calc divCoeff G A m i * Real.log x ^ i ≤ |divCoeff G A m i| * Real.log x ^ i :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hlog i)
        _ ≤ |divCoeff G A m i| * (1 + logPlus x) ^ m := by
            gcongr
            calc Real.log x ^ i ≤ (1 + logPlus x) ^ i := by
                  gcongr; rw [hlp']; linarith
              _ ≤ (1 + logPlus x) ^ m := pow_le_pow_right₀ (by linarith) hi'
    have hrem : iterDivPrim G m x - ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log x ^ i
        ≤ M / ε ^ m := by
      calc _ ≤ |iterDivPrim G m x
              - ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log x ^ i| := le_abs_self _
        _ ≤ M / ε ^ m * x ^ (-ε) := hexp
        _ ≤ M / ε ^ m * 1 := by gcongr
        _ = M / ε ^ m := mul_one _
    calc iterDivPrim G m x
        ≤ (∑ i ∈ Finset.range (m + 1), |divCoeff G A m i|) * (1 + logPlus x) ^ m + M / ε ^ m := by
          linarith
      _ ≤ (∑ i ∈ Finset.range (m + 1), |divCoeff G A m i|) * (1 + logPlus x) ^ m
          + M / ε ^ m * (1 + logPlus x) ^ m + C / δ ^ m * (1 + logPlus x) ^ m := by
          nlinarith [mul_nonneg hC (sub_nonneg.2 hpow_ge), mul_nonneg hM (sub_nonneg.2 hpow_ge)]
      _ = _ := by ring

/-- `(K + |log t|)^j t^γ e^{-βt²+βat}` is integrable on `(0, ∞)` for `γ > -1`, `K ≥ 0`. -/
theorem logPowShift_weightedKernel_integrableOn (β a γ K : ℝ) (hβ : 0 < β) (hγ : -1 < γ)
    (j : ℕ) :
    IntegrableOn (fun t => (K + |Real.log t|) ^ j * (t ^ γ * quadKernel β a t)) (Ioi 0) := by
  have hpt : ∀ t : ℝ, (K + |Real.log t|) ^ j * (t ^ γ * quadKernel β a t)
      = ∑ i ∈ Finset.range (j + 1),
          (K ^ i * (j.choose i : ℝ)) * (|Real.log t| ^ (j - i) * (t ^ γ * quadKernel β a t)) := by
    intro t
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hpt]
  refine integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
  exact logPow_weightedKernel_integrableOn β a γ hβ hγ (j - i)

/-- `quadKernel (β/2) 0 t = e^{-(β/2) t²}`. -/
theorem quadKernel_half_zero (β t : ℝ) : quadKernel (β / 2) 0 t = Real.exp (-(β / 2) * t ^ 2) := by
  simp [quadKernel]

/-- The block envelope constant
`E(β,L,p,d) = e^{βL²/2} ∫₀^∞ (1+|log t|)^d t^{p-1} e^{-(β/2)t²} dt`. -/
noncomputable def blockEnv (β L p : ℝ) (d : ℕ) : ℝ :=
  Real.exp (β * L ^ 2 / 2)
    * ∫ t in Ioi (0 : ℝ), (1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t)

theorem blockEnv_integrand_nonneg (β p : ℝ) (d : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ (1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t) :=
  mul_nonneg (pow_nonneg (by positivity) _)
    (mul_nonneg (Real.rpow_nonneg ht.le _) (quadKernel_pos _ _ _).le)

theorem blockEnv_nonneg (β L p : ℝ) (d : ℕ) : 0 ≤ blockEnv β L p d := by
  unfold blockEnv
  exact mul_nonneg (Real.exp_pos _).le
    (setIntegral_nonneg measurableSet_Ioi fun t ht => blockEnv_integrand_nonneg β p d t ht)

/-- For `0 < t ≤ y`: `log y − log t ≤ log₊ y + |log t|`. -/
theorem log_sub_log_le (y t : ℝ) : Real.log y - Real.log t ≤ logPlus y + |Real.log t| :=
  add_le_add (log_le_logPlus y) (neg_le_abs _)

/-- `(x + y)^d ≤ (1+x)^d (1+y)^d` for `x, y ≥ 0`. -/
theorem add_pow_le_mul_pow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (d : ℕ) :
    (x + y) ^ d ≤ (1 + x) ^ d * (1 + y) ^ d := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) d

/-- **Uniform block envelope**: for all `c > 0` and `|a| ≤ L`,
`c^p Z_{d+1}(c) ≤ (∏ k_i⁻¹) (1/d!) E(β,L,p,d) (1 + log₊(cB))^d`. -/
theorem iterChartGen_block_le (β b L p : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p) (a : ℝ)
    (ha : |a| ≤ L) (c : ℝ) (hc : 0 < c) :
    c ^ p * iterChartGen β a b k h (d + 1) c
      ≤ (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) * blockEnv β L p d
        * (1 + logPlus (c * b ^ (∑ i ∈ Finset.range (d + 1), k i))) ^ d := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le d)]; exact chartExp_pos k h hk 0
  rw [iterChartGen_eq_logWeighted β a b k h p hβ hb hk d hp c hc, logWeightedPrim]
  set B : ℝ := b ^ (∑ i ∈ Finset.range (d + 1), k i) with hB
  have hcB : 0 < c * B := by positivity
  have hcp : c ^ p * ((∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * c ^ (-p)
      * (1 / (d.factorial : ℝ) * ∫ t in Ioc (0 : ℝ) (c * B),
          (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)))
      = (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ))
        * ∫ t in Ioc (0 : ℝ) (c * B),
          (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t) := by
    have : c ^ p * c ^ (-p) = 1 := by
      rw [← Real.rpow_add hc]; simp
    calc _ = (c ^ p * c ^ (-p)) * ((∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i)
          * (1 / (d.factorial : ℝ) * ∫ t in Ioc (0 : ℝ) (c * B),
            (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t))) := by ring
      _ = _ := by rw [this]; ring
  rw [hcp]
  have hprod : 0 ≤ (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) := by
    positivity
  suffices key : ∫ t in Ioc (0 : ℝ) (c * B),
      (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)
        ≤ blockEnv β L p d * (1 + logPlus (c * B)) ^ d by
    calc _ ≤ (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ))
          * (blockEnv β L p d * (1 + logPlus (c * B)) ^ d) := mul_le_mul_of_nonneg_left key hprod
      _ = _ := by ring
  -- pointwise domination of the integrand
  have ha2 : a ^ 2 ≤ L ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hexp : Real.exp (β * a ^ 2 / 2) ≤ Real.exp (β * L ^ 2 / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (c * B),
      (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)
        ≤ (1 + logPlus (c * B)) ^ d * (Real.exp (β * L ^ 2 / 2)
            * ((1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t))) := by
    intro t ht
    have hlog0 : 0 ≤ Real.log (c * B) - Real.log t := sub_nonneg.2 (Real.log_le_log ht.1 ht.2)
    have h1 : (Real.log (c * B) - Real.log t) ^ d
        ≤ (1 + logPlus (c * B)) ^ d * (1 + |Real.log t|) ^ d :=
      (pow_le_pow_left₀ hlog0 (log_sub_log_le _ _) d).trans
        (add_pow_le_mul_pow _ _ (logPlus_nonneg _) (abs_nonneg _) d)
    have h2 : quadKernel β a t ≤ Real.exp (β * L ^ 2 / 2) * quadKernel (β / 2) 0 t := by
      rw [quadKernel_half_zero]
      exact (quadKernel_le β a t hβ).trans (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le)
    have ht' : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht.1.le _
    have hq : 0 ≤ t ^ (p - 1) * quadKernel β a t := mul_nonneg ht' (quadKernel_pos _ _ _).le
    have hb0 : 0 ≤ (1 + logPlus (c * B)) ^ d * (1 + |Real.log t|) ^ d :=
      mul_nonneg (pow_nonneg (by linarith [logPlus_nonneg (c * B)]) _)
        (pow_nonneg (by positivity) _)
    calc (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)
        ≤ ((1 + logPlus (c * B)) ^ d * (1 + |Real.log t|) ^ d)
            * (t ^ (p - 1) * quadKernel β a t) := mul_le_mul_of_nonneg_right h1 hq
      _ ≤ ((1 + logPlus (c * B)) ^ d * (1 + |Real.log t|) ^ d)
            * (t ^ (p - 1) * (Real.exp (β * L ^ 2 / 2) * quadKernel (β / 2) 0 t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 ht') hb0
      _ = _ := by ring
  have hint : IntegrableOn
      (fun t => (1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t)) (Ioi 0) :=
    logPowShift_weightedKernel_integrableOn (β / 2) 0 (p - 1) 1 (by positivity) (by linarith) d
  have hfa : IntegrableOn (fun t => (Real.log (c * B) - Real.log t) ^ d
      * (t ^ (p - 1) * quadKernel β a t)) (Ioc 0 (c * B)) :=
    logPow_weightedKernel_integrableOn_Ioc β a (p - 1) hβ (by linarith) d (c * B)
  calc ∫ t in Ioc (0 : ℝ) (c * B),
        (Real.log (c * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)
      ≤ ∫ t in Ioc (0 : ℝ) (c * B), (1 + logPlus (c * B)) ^ d * (Real.exp (β * L ^ 2 / 2)
            * ((1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t))) := by
        refine setIntegral_mono_on hfa ?_ measurableSet_Ioc hpt
        exact ((hint.mono_set Ioc_subset_Ioi_self).const_mul _).const_mul _
    _ = (1 + logPlus (c * B)) ^ d * Real.exp (β * L ^ 2 / 2)
          * ∫ t in Ioc (0 : ℝ) (c * B),
              (1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t) := by
        rw [integral_const_mul, integral_const_mul]; ring
    _ ≤ (1 + logPlus (c * B)) ^ d * Real.exp (β * L ^ 2 / 2)
          * ∫ t in Ioi (0 : ℝ),
              (1 + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel (β / 2) 0 t) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (pow_nonneg (by linarith [logPlus_nonneg (c * B)]) _) (Real.exp_pos _).le)
        refine setIntegral_mono_set hint ?_ (Ioc_subset_Ioi_self.eventuallyLE)
        exact (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun t ht => blockEnv_integrand_nonneg β p d t ht)
    _ = _ := by rw [blockEnv]; ring

/-- The scaled log-weighted integrand
`F_N(t) = 1_{(0, NγB]}(t) ((log(NγB) − log t)/log N)^d g(t)`. -/
noncomputable def scaledLogIntegrand (β a p γ B : ℝ) (d : ℕ) (N t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) (N * γ * B)).indicator
    (fun t => ((Real.log (N * γ * B) - Real.log t) / Real.log N) ^ d
      * (t ^ (p - 1) * quadKernel β a t)) t

/-- **Dominated convergence for the scaled log-weighted integrand**:
`∫₀^∞ F_N → A_{p-1}(a)`. -/
theorem scaledLogIntegrand_tendsto (β a p γ B : ℝ) (hβ : 0 < β) (hp : 0 < p) (hγ : 0 < γ)
    (hB : 0 < B) (d : ℕ) :
    Tendsto (fun N => ∫ t in Ioi (0 : ℝ), scaledLogIntegrand β a p γ B d N t) atTop
      (𝓝 (weightedMass β a (p - 1))) := by
  have hγB : 0 < γ * B := mul_pos hγ hB
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => ((1 + |Real.log (γ * B)|) + |Real.log t|) ^ d * (t ^ (p - 1) * quadKernel β a t))
    ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun N => ?_
    refine (Measurable.indicator ?_ measurableSet_Ioc).aestronglyMeasurable
    unfold quadKernel; fun_prop
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hlogN : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have hgt : 0 ≤ t ^ (p - 1) * quadKernel β a t :=
      mul_nonneg (Real.rpow_nonneg ht.le _) (quadKernel_pos _ _ _).le
    have hbnd : 0 ≤ ((1 + |Real.log (γ * B)|) + |Real.log t|) ^ d
        * (t ^ (p - 1) * quadKernel β a t) :=
      mul_nonneg (pow_nonneg (by positivity) _) hgt
    simp only [scaledLogIntegrand, indicator_apply]
    split_ifs with hmem
    · have hlog0 : 0 ≤ Real.log (N * γ * B) - Real.log t :=
        sub_nonneg.2 (Real.log_le_log (mem_Ioi.1 ht) hmem.2)
      have hratio : 0 ≤ (Real.log (N * γ * B) - Real.log t) / Real.log N := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hratio _) hgt)]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hratio ?_ d) hgt
      rw [mul_assoc, Real.log_mul hNpos.ne' hγB.ne', div_le_iff₀ (by linarith)]
      have h1 : Real.log (γ * B) - Real.log t ≤ |Real.log (γ * B)| + |Real.log t| :=
        (le_abs_self _).trans (abs_sub _ _)
      have h2 : |Real.log (γ * B)| + |Real.log t|
          ≤ (|Real.log (γ * B)| + |Real.log t|) * Real.log N :=
        le_mul_of_one_le_right (by positivity) hlogN
      nlinarith
    · rw [norm_zero]; exact hbnd
  · exact logPowShift_weightedKernel_integrableOn β a (p - 1) (1 + |Real.log (γ * B)|) hβ
      (by linarith) d
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have h1 : Tendsto (fun N : ℝ => (1 + (Real.log (γ * B) - Real.log t) / Real.log N) ^ d
        * (t ^ (p - 1) * quadKernel β a t)) atTop
        (𝓝 ((1 + 0) ^ d * (t ^ (p - 1) * quadKernel β a t))) := by
      refine Tendsto.mul_const _ (Tendsto.pow ?_ d)
      exact tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
    rw [add_zero, one_pow, one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (t / (γ * B))] with N hN1 hN2
    have hNpos : 0 < N := by linarith
    have hlogN : 0 < Real.log N := Real.log_pos hN1
    have hmem : t ∈ Ioc (0 : ℝ) (N * γ * B) := by
      refine ⟨mem_Ioi.1 ht, ?_⟩
      rw [div_le_iff₀ hγB] at hN2
      linarith [mul_assoc N γ B]
    simp only [scaledLogIntegrand, indicator_of_mem hmem]
    congr 2
    rw [mul_assoc, Real.log_mul hNpos.ne' hγB.ne']
    field_simp
    ring

/-- **Scale limit of the block**: for fixed `γ > 0`,
`N^p Z_{d+1}(Nγ) / (log N)^d → (∏ k_i⁻¹) (1/d!) γ^{-p} A_{p-1}(a)`. -/
theorem iterChartGen_block_tendsto (β a b p γ : ℝ) (k h : ℕ → ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p) (hγ : 0 < γ) :
    Tendsto (fun N : ℝ => N ^ p / Real.log N ^ d * iterChartGen β a b k h (d + 1) (N * γ)) atTop
      (𝓝 ((∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) * γ ^ (-p)
        * weightedMass β a (p - 1))) := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le d)]; exact chartExp_pos k h hk 0
  set B : ℝ := b ^ (∑ i ∈ Finset.range (d + 1), k i) with hB
  have hBpos : 0 < B := by positivity
  have hlim := (scaledLogIntegrand_tendsto β a p γ B hβ hp0 hγ hBpos d).const_mul
    ((∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) * γ ^ (-p))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  rw [iterChartGen_eq_logWeighted β a b k h p hβ hb hk d hp (N * γ) (by positivity),
    logWeightedPrim]
  have hFint : ∫ t in Ioi (0 : ℝ), scaledLogIntegrand β a p γ B d N t
      = (Real.log N ^ d)⁻¹ * ∫ t in Ioc (0 : ℝ) (N * γ * B),
          (Real.log (N * γ * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t) := by
    unfold scaledLogIntegrand
    rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [div_pow]; ring
  rw [hFint]
  have hNp : (N * γ) ^ (-p) = N ^ (-p) * γ ^ (-p) := Real.mul_rpow hNpos.le hγ.le
  have hNN : N ^ p * N ^ (-p) = 1 := by rw [← Real.rpow_add hNpos]; simp
  rw [hNp]
  set I := ∫ t in Ioc (0 : ℝ) (N * γ * B),
    (Real.log (N * γ * B) - Real.log t) ^ d * (t ^ (p - 1) * quadKernel β a t)
  set P := ∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i
  linear_combination (-(P * (1 / (d.factorial : ℝ)) * γ ^ (-p) * (Real.log N ^ d)⁻¹ * I)) * hNN

end Laplace.Grammar
