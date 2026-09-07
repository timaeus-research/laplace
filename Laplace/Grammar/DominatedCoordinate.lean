/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.PowerLogEnvelope

/-!
# The dominated-coordinate transfer lemma

Second step of the mixed-ratio general-`d` monomial programme (Astra #15, route A). If a bounded
measurable `f` on `(0,∞)` has the power–log asymptotic `f(M)/(M^{-λ}(log M)^r) → C`, then
integrating it against a **dominated** coordinate weight `t^{q-1}` with `q > λ` preserves the
exponent, the logarithmic degree and multiplies the constant by `1/(q-λ)`:

  `(∫₀¹ t^{q-1} f(Nt) dt) / (N^{-λ} (log N)^r) → C/(q-λ)`

(`tendsto_weighted_scale_div`). The proof is dominated convergence on `(0,1]` with the
`N`-independent bound `K 2^r t^{q-λ-1}` from `PowerLogEnvelope.lean`, and the pointwise limit
`C t^{q-λ-1}`, whose integral is `C/(q-λ)`.

Peeling one nonminimal coordinate of the weighted box integral is exactly an application of this
lemma to `f = ` the lower-dimensional weighted integral, which is how the mixed-ratio theorem is
assembled in the following units.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- `∫₀¹ t^{q-λ-1} dt = 1/(q-λ)` for `q > λ`. -/
theorem integral_Ioc_rpow_gap (l q : ℝ) (hq : l < q) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (q - l - 1) = 1 / (q - l) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    show q - l - 1 + 1 = q - l by ring, Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-- The dominating power `t^{q-λ-1}` is integrable on `(0,1]` for `q > λ`. -/
theorem integrableOn_Ioc_rpow_gap (l q : ℝ) (hq : l < q) :
    IntegrableOn (fun t : ℝ => t ^ (q - l - 1)) (Ioc 0 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (by linarith : (-1 : ℝ) < q - l - 1)).def'
  rwa [uIoc_of_le zero_le_one] at h

/-- **Dominated-coordinate transfer**: for `q > λ > 0`, a bounded measurable `f` with
`f(M)/(M^{-λ}(log M)^r) → C` satisfies
`(∫₀¹ t^{q-1} f(Nt) dt)/(N^{-λ}(log N)^r) → C/(q-λ)`. -/
theorem tendsto_weighted_scale_div (f : ℝ → ℝ) (l q : ℝ) (r : ℕ) (C B : ℝ) (hl : 0 < l)
    (hq : l < q) (hf : Measurable f) (hB : ∀ M, 0 < M → |f M| ≤ B)
    (hlim : Tendsto (fun M => f M / (M ^ (-l) * Real.log M ^ r)) atTop (𝓝 C)) :
    Tendsto (fun N => (∫ t in Ioc (0 : ℝ) 1, t ^ (q - 1) * f (N * t)) /
        (N ^ (-l) * Real.log N ^ r)) atTop (𝓝 (C / (q - l))) := by
  obtain ⟨K, hK, henv⟩ := envelope_of_tendsto_ratio f l r C B hl hB hlim
  set F : ℝ → ℝ → ℝ := fun N t => t ^ (q - 1) * f (N * t) / (N ^ (-l) * Real.log N ^ r) with hF
  have hDCT : Tendsto (fun N => ∫ t in Ioc (0 : ℝ) 1, F N t) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, C * t ^ (q - l - 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => K * 2 ^ r * t ^ (q - l - 1)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun N => ?_
      have : Measurable (F N) := by
        simp only [hF]
        fun_prop
      exact this.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact scaled_envelope_bound f l q r K hK henv N t hN ht.1 ht.2
    · exact (integrableOn_Ioc_rpow_gap l q hq).const_mul _
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      have h := (tendsto_scaled_ratio f l r C hlim t ht.1).const_mul (t ^ (q - 1))
      have hval : t ^ (q - 1) * (C * t ^ (-l)) = C * t ^ (q - l - 1) := by
        rw [show q - l - 1 = (q - 1) + (-l) by ring, Real.rpow_add ht.1]
        ring
      rw [hval] at h
      refine h.congr fun N => ?_
      simp only [hF]
      ring
  rw [integral_const_mul, integral_Ioc_rpow_gap l q hq, mul_one_div] at hDCT
  refine hDCT.congr fun N => ?_
  simp only [hF]
  exact integral_div _ _

end Laplace.Grammar
