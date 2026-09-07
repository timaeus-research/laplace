/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ParamIntegration

/-!
# The weighted finite-part axis lemma (grammar §4.2, higher-order `d = 2`)

For `f(v) = ∑_{m<M} f_m v^m + R_M(v)` on `(0, b]` with `|R_M(v)| ≤ H v^M` and `0 ≤ γ < M`, the
weighted axis integral `J(ε) = ∫_ε^b v^{-1-γ} f(v) dv` has the exact expansion

  `J(ε) = FP_γ f − ∑_{m<M} f_m · axisPrim γ ε m + E(ε)`,   `|E(ε)| ≤ H/(M−γ) · ε^{M−γ}`,

where `axisPrim γ x m = log x` at the resonance `m = γ` and `x^{m-γ}/(m-γ)` otherwise, and the
finite part `FP_γ f = ∫_0^b v^{-1-γ}(f − T_M f) + ∑_{m<M} f_m · axisPrim γ b m` collects the
regularised integral and the upper-endpoint counterterms. With `ε = (r/A)^{1/k}` this produces the
exponents `(m−γ)/k` and the resonant `log(A/r)/k` of the `d = 2` density expansion
(`axisPrim_rpow`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Finset

namespace Laplace.Grammar

/-- `∫_ε^b v^c dv` for `0 < ε ≤ b`, including the logarithmic case `c = -1`. -/
theorem integral_rpow_Ioc (ε b c : ℝ) (hε : 0 < ε) (hεb : ε ≤ b) :
    ∫ v in Ioc ε b, v ^ c
      = if c = -1 then Real.log b - Real.log ε else (b ^ (c + 1) - ε ^ (c + 1)) / (c + 1) := by
  have hb : 0 < b := lt_of_lt_of_le hε hεb
  have h0 : (0 : ℝ) ∉ uIcc ε b := by
    rw [uIcc_of_le hεb]
    intro h
    exact absurd h.1 (not_le.2 hε)
  rw [← intervalIntegral.integral_of_le hεb]
  split_ifs with hc
  · subst hc
    rw [← Real.log_div hb.ne' hε.ne', ← integral_inv h0]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hεb] at hv
    rw [Real.rpow_neg (lt_of_lt_of_le hε hv.1).le, Real.rpow_one]
  · exact integral_rpow (Or.inr ⟨hc, h0⟩)

/-- The endpoint primitive of `v^{m-1-γ}`: `log x` at the resonance `m = γ`, `x^{m-γ}/(m-γ)`
otherwise. -/
noncomputable def axisPrim (γ x : ℝ) (m : ℕ) : ℝ :=
  if (m : ℝ) = γ then Real.log x else x ^ ((m : ℝ) - γ) / ((m : ℝ) - γ)

theorem integral_rpow_shift_Ioc (γ ε b : ℝ) (m : ℕ) (hε : 0 < ε) (hεb : ε ≤ b) :
    ∫ v in Ioc ε b, v ^ ((m : ℝ) - 1 - γ) = axisPrim γ b m - axisPrim γ ε m := by
  rw [integral_rpow_Ioc ε b _ hε hεb]
  unfold axisPrim
  by_cases h : (m : ℝ) = γ
  · rw [if_pos (by linarith), if_pos h, if_pos h]
  · rw [if_neg (fun h' => h (by linarith)), if_neg h, if_neg h,
      show (m : ℝ) - 1 - γ + 1 = (m : ℝ) - γ by ring, sub_div]

/-- The Taylor remainder `f(v) − ∑_{m<M} f_m v^m`. -/
def taylorRem (f : ℝ → ℝ) (fm : ℕ → ℝ) (M : ℕ) (v : ℝ) : ℝ :=
  f v - ∑ m ∈ range M, fm m * v ^ m

theorem taylorRem_measurable (f : ℝ → ℝ) (fm : ℕ → ℝ) (M : ℕ) (hf : Measurable f) :
    Measurable (taylorRem f fm M) := by
  unfold taylorRem
  exact hf.sub (Finset.measurable_sum _ fun m _ => measurable_const.mul (measurable_id.pow_const m))

/-- The regularised axis integral `∫_0^b v^{-1-γ} (f − T_M f) dv`. -/
noncomputable def regAxisIntegral (γ b : ℝ) (f : ℝ → ℝ) (fm : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∫ v in Ioc (0 : ℝ) b, v ^ (-1 - γ) * taylorRem f fm M v

/-- The weighted finite part `FP_γ f`: regularised integral plus upper-endpoint counterterms. -/
noncomputable def axisFinitePart (γ b : ℝ) (f : ℝ → ℝ) (fm : ℕ → ℝ) (M : ℕ) : ℝ :=
  regAxisIntegral γ b f fm M + ∑ m ∈ range M, fm m * axisPrim γ b m

/-- The weighted remainder `v^{-1-γ} R_M(v)` is integrable on `(0, b]` when `γ < M`. -/
theorem weighted_taylorRem_integrableOn (γ b H : ℝ) (M : ℕ) (hM : γ < M)
    (f : ℝ → ℝ) (fm : ℕ → ℝ) (hf : Measurable f)
    (hrem : ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm M v| ≤ H * v ^ M) :
    IntegrableOn (fun v => v ^ (-1 - γ) * taylorRem f fm M v) (Ioc 0 b) := by
  have hpow : IntegrableOn (fun v : ℝ => v ^ ((M : ℝ) - 1 - γ)) (Ioc 0 b) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) (by linarith)).1
  refine Integrable.mono' (hpow.const_mul H) ?_ ?_
  · exact ((measurable_id.pow_const _).mul (taylorRem_measurable f fm M hf)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := hv.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _),
      show (M : ℝ) - 1 - γ = (-1 - γ) + (M : ℝ) by ring, Real.rpow_add hv0, Real.rpow_natCast]
    calc v ^ (-1 - γ) * |taylorRem f fm M v| ≤ v ^ (-1 - γ) * (H * v ^ M) :=
          mul_le_mul_of_nonneg_left (hrem v hv) (Real.rpow_nonneg hv0.le _)
      _ = _ := by ring

/-- The tail of the regularised integral below `ε` is `O(ε^{M-γ})`. -/
theorem weighted_taylorRem_tail_le (γ b H : ℝ) (M : ℕ) (hM : γ < M)
    (f : ℝ → ℝ) (fm : ℕ → ℝ)
    (hrem : ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm M v| ≤ H * v ^ M)
    (ε : ℝ) (hε : 0 < ε) (hεb : ε ≤ b) :
    |∫ v in Ioc (0 : ℝ) ε, v ^ (-1 - γ) * taylorRem f fm M v|
      ≤ H / ((M : ℝ) - γ) * ε ^ ((M : ℝ) - γ) := by
  have hMγ : 0 < (M : ℝ) - γ := by linarith
  have hpow : IntegrableOn (fun v : ℝ => v ^ ((M : ℝ) - 1 - γ)) (Ioc 0 ε) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) (by linarith)).1
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) ε))
    (f := fun v => v ^ (-1 - γ) * taylorRem f fm M v) (hpow.const_mul H) ?_
  · have hint : ∫ v in Ioc (0 : ℝ) ε, v ^ ((M : ℝ) - 1 - γ)
        = ε ^ ((M : ℝ) - γ) / ((M : ℝ) - γ) := by
      rw [← intervalIntegral.integral_of_le hε.le, integral_rpow (Or.inl (by linarith)),
        show (M : ℝ) - 1 - γ + 1 = (M : ℝ) - γ by ring, Real.zero_rpow hMγ.ne', sub_zero]
    rw [Real.norm_eq_abs, integral_const_mul, hint] at hbound
    refine hbound.trans (le_of_eq ?_)
    ring
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := hv.1
    have hv' : v ∈ Ioc (0 : ℝ) b := ⟨hv.1, hv.2.trans hεb⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _),
      show (M : ℝ) - 1 - γ = (-1 - γ) + (M : ℝ) by ring, Real.rpow_add hv0, Real.rpow_natCast]
    calc v ^ (-1 - γ) * |taylorRem f fm M v| ≤ v ^ (-1 - γ) * (H * v ^ M) :=
          mul_le_mul_of_nonneg_left (hrem v hv') (Real.rpow_nonneg hv0.le _)
      _ = _ := by ring

/-- **The weighted finite-part axis lemma.** -/
theorem axis_finite_part_expansion (γ b H : ℝ) (M : ℕ) (hM : γ < M)
    (f : ℝ → ℝ) (fm : ℕ → ℝ) (hf : Measurable f)
    (hrem : ∀ v ∈ Ioc (0 : ℝ) b, |taylorRem f fm M v| ≤ H * v ^ M)
    (ε : ℝ) (hε : 0 < ε) (hεb : ε ≤ b) :
    |(∫ v in Ioc ε b, v ^ (-1 - γ) * f v)
        - (axisFinitePart γ b f fm M - ∑ m ∈ range M, fm m * axisPrim γ ε m)|
      ≤ H / ((M : ℝ) - γ) * ε ^ ((M : ℝ) - γ) := by
  have hR := weighted_taylorRem_integrableOn γ b H M hM f fm hf hrem
  -- the powers are integrable on `(ε, b]`
  have hpow : ∀ m : ℕ, IntegrableOn (fun v : ℝ => v ^ ((m : ℝ) - 1 - γ)) (Ioc ε b) := by
    intro m
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_id.rpow_const fun v hv => Or.inl (lt_of_lt_of_le hε hv.1).ne'
  -- decompose the integrand on `(ε, b]`
  have hsplit : ∫ v in Ioc ε b, v ^ (-1 - γ) * f v
      = (∫ v in Ioc ε b, v ^ (-1 - γ) * taylorRem f fm M v)
        + ∑ m ∈ range M, fm m * ∫ v in Ioc ε b, v ^ ((m : ℝ) - 1 - γ) := by
    have hpt : ∀ v ∈ Ioc ε b, v ^ (-1 - γ) * f v
        = v ^ (-1 - γ) * taylorRem f fm M v + ∑ m ∈ range M, fm m * v ^ ((m : ℝ) - 1 - γ) := by
      intro v hv
      have hv0 : 0 < v := hε.trans hv.1
      unfold taylorRem
      rw [mul_sub, Finset.mul_sum]
      have : ∀ m ∈ range M, v ^ (-1 - γ) * (fm m * v ^ m) = fm m * v ^ ((m : ℝ) - 1 - γ) := by
        intro m _
        rw [show (m : ℝ) - 1 - γ = (-1 - γ) + (m : ℝ) by ring, Real.rpow_add hv0,
          Real.rpow_natCast]
        ring
      rw [Finset.sum_congr rfl this]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt,
      integral_add (hR.mono_set (Ioc_subset_Ioc_left hε.le))
        (integrable_finsetSum _ fun m _ => (hpow m).const_mul _),
      integral_finsetSum _ fun m _ => (hpow m).const_mul _]
    simp only [integral_const_mul]
  -- split the regularised integral at `ε`
  have hunion : regAxisIntegral γ b f fm M
      = (∫ v in Ioc (0 : ℝ) ε, v ^ (-1 - γ) * taylorRem f fm M v)
        + ∫ v in Ioc ε b, v ^ (-1 - γ) * taylorRem f fm M v := by
    unfold regAxisIntegral
    rw [← Ioc_union_Ioc_eq_Ioc hε.le hεb]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hR.mono_set (Ioc_subset_Ioc_right hεb)) (hR.mono_set (Ioc_subset_Ioc_left hε.le))
  have hprim : ∀ m ∈ range M, fm m * ∫ v in Ioc ε b, v ^ ((m : ℝ) - 1 - γ)
      = fm m * axisPrim γ b m - fm m * axisPrim γ ε m := by
    intro m _
    rw [integral_rpow_shift_Ioc γ ε b m hε hεb, mul_sub]
  rw [hsplit, Finset.sum_congr rfl hprim, Finset.sum_sub_distrib]
  unfold axisFinitePart
  rw [hunion]
  rw [show (∫ v in Ioc ε b, v ^ (-1 - γ) * taylorRem f fm M v)
      + ((∑ m ∈ range M, fm m * axisPrim γ b m) - ∑ m ∈ range M, fm m * axisPrim γ ε m)
      - ((∫ v in Ioc (0 : ℝ) ε, v ^ (-1 - γ) * taylorRem f fm M v)
          + (∫ v in Ioc ε b, v ^ (-1 - γ) * taylorRem f fm M v)
        + ∑ m ∈ range M, fm m * axisPrim γ b m - ∑ m ∈ range M, fm m * axisPrim γ ε m)
      = -(∫ v in Ioc (0 : ℝ) ε, v ^ (-1 - γ) * taylorRem f fm M v) by ring, abs_neg]
  exact weighted_taylorRem_tail_le γ b H M hM f fm hrem ε hε hεb

/-- The endpoint primitive at `ε = (r/A)^{1/k}`: the exponents `(m-γ)/k` and the resonant
`(log r − log A)/k` of the density expansion. -/
theorem axisPrim_rpow (γ A r k : ℝ) (m : ℕ) (hA : 0 < A) (hr : 0 < r) :
    axisPrim γ ((r / A) ^ (1 / k)) m
      = if (m : ℝ) = γ then (Real.log r - Real.log A) / k
        else (r / A) ^ (((m : ℝ) - γ) / k) / ((m : ℝ) - γ) := by
  have hrA : 0 < r / A := div_pos hr hA
  unfold axisPrim
  split_ifs with h
  · rw [Real.log_rpow hrA, Real.log_div hr.ne' hA.ne']
    ring
  · rw [← Real.rpow_mul hrA.le, show 1 / k * ((m : ℝ) - γ) = ((m : ℝ) - γ) / k by ring]

theorem rpow_one_div_rpow (x k c : ℝ) (hx : 0 ≤ x) : (x ^ (1 / k)) ^ c = x ^ (c / k) := by
  rw [← Real.rpow_mul hx, show 1 / k * c = c / k by ring]

end Laplace.Grammar
