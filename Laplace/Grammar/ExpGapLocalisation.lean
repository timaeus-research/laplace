/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.HeadlineTangential

/-!
# Exponential-gap localisation

The analytic content of the paper's localisation step (remark `rem:cutoff_correct`): away from the
zero set of the phase, where `f ≥ ε > 0`, a Laplace-type integral is exponentially small,

  `‖∫_S a(x) e^{-βN f(x)} dx‖ ≤ e^{-βNε} ∫_S g(x) dx`   whenever `‖a‖ ≤ g` on `S`

(`norm_setIntegral_exp_gap_le`), uniformly in any family of amplitudes dominated by `g`; hence the
region contributes `O(e^{-βNε})` (`exp_gap_isBigO`; stated for `β ≥ 0` and any real `ε`, so the
comparison function need not decay) and, for `β > 0`, `ε > 0`, `o` of every power–log scale
(`exp_gap_isLittleO_powLog`). The estimates carry measurability hypotheses on
the amplitude and the phase, so that the weighted integrand is a genuine (integrable) Bochner
integrand rather than a totalised one (`exp_gap_integrable`). Establishing the gap `f ≥ ε` on the
complement of a neighbourhood of the zero set is a separate geometric task and is not addressed
here: for a monomial phase the zero set is a union of coordinate faces, and removing a neighbourhood
of the corner alone does not produce a gap.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The pointwise domination `‖a e^{-βNf}‖ ≤ e^{-βNε} g` on the gap region. -/
theorem exp_gap_pointwise_le {X : Type*} (a g f : X → ℝ) (β N ε : ℝ) (hβN : 0 ≤ β * N)
    (x : X) (hb : ‖a x‖ ≤ g x) (hf : ε ≤ f x) :
    ‖a x * Real.exp (-(β * N * f x))‖ ≤ Real.exp (-(β * N * ε)) * g x := by
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), mul_comm]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) hb (norm_nonneg _) (Real.exp_pos _).le
  nlinarith

/-- The weighted Laplace integrand is genuinely integrable on the gap region. -/
theorem exp_gap_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} (S : Set X)
    (hS : MeasurableSet S) (a g f : X → ℝ) (β N ε : ℝ) (hβN : 0 ≤ β * N)
    (ha : AEStronglyMeasurable a (μ.restrict S)) (hf : AEStronglyMeasurable f (μ.restrict S))
    (hg : IntegrableOn g S μ) (hbound : ∀ x ∈ S, ‖a x‖ ≤ g x) (hgap : ∀ x ∈ S, ε ≤ f x) :
    IntegrableOn (fun x => a x * Real.exp (-(β * N * f x))) S μ := by
  refine Integrable.mono' (hg.const_mul (Real.exp (-(β * N * ε))))
    (ha.mul ((Real.continuous_exp.comp_aestronglyMeasurable (hf.const_mul _).neg))) ?_
  exact (ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
    exp_gap_pointwise_le a g f β N ε hβN x (hbound x hx) (hgap x hx))

/-- **Exponential-gap bound** for a Laplace-type integral away from the zero set of the phase. -/
theorem norm_setIntegral_exp_gap_le {X : Type*} [MeasurableSpace X] {μ : Measure X} (S : Set X)
    (hS : MeasurableSet S) (a g f : X → ℝ) (β N ε : ℝ) (hβN : 0 ≤ β * N)
    (ha : AEStronglyMeasurable a (μ.restrict S)) (hf : AEStronglyMeasurable f (μ.restrict S))
    (hg : IntegrableOn g S μ) (hbound : ∀ x ∈ S, ‖a x‖ ≤ g x) (hgap : ∀ x ∈ S, ε ≤ f x) :
    ‖∫ x in S, a x * Real.exp (-(β * N * f x)) ∂μ‖ ≤
      Real.exp (-(β * N * ε)) * ∫ x in S, g x ∂μ := by
  have _ := exp_gap_integrable S hS a g f β N ε hβN ha hf hg hbound hgap
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.const_mul _) ?_
  exact (ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
    exp_gap_pointwise_le a g f β N ε hβN x (hbound x hx) (hgap x hx))

/-- **Big-O form**: a family of amplitudes dominated by a fixed integrable `g` on the gap region
contributes `O(e^{-βNε})`. -/
theorem exp_gap_isBigO {X : Type*} [MeasurableSpace X] {μ : Measure X} (S : Set X)
    (hS : MeasurableSet S) (a : ℝ → X → ℝ) (g f : X → ℝ) (β ε : ℝ) (hβ : 0 ≤ β)
    (ha : ∀ N, AEStronglyMeasurable (a N) (μ.restrict S))
    (hf : AEStronglyMeasurable f (μ.restrict S)) (hg : IntegrableOn g S μ)
    (hbound : ∀ N, ∀ x ∈ S, ‖a N x‖ ≤ g x) (hgap : ∀ x ∈ S, ε ≤ f x) :
    (fun N => ∫ x in S, a N x * Real.exp (-(β * N * f x)) ∂μ) =O[atTop]
      fun N => Real.exp (-(β * N * ε)) := by
  refine IsBigO.of_bound (∫ x in S, g x ∂μ) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  rw [Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  exact (norm_setIntegral_exp_gap_le S hS (a N) g f β N ε (mul_nonneg hβ hN) (ha N) hf hg
    (hbound N) hgap).trans (le_of_eq (mul_comm _ _))

/-- `e^{-βNε}` is `o` of every power–log scale `N^{-λ} (log N)^r` for `β > 0`, `ε > 0` (stated
with `C > 0`; `C ≠ 0` would suffice). -/
theorem exp_gap_isLittleO_powLog (β ε C l : ℝ) (r : ℕ) (hβ : 0 < β) (hε : 0 < ε) (hC : 0 < C) :
    (fun N : ℝ => Real.exp (-(β * N * ε))) =o[atTop] powLog C l r := by
  have h1 : (fun N : ℝ => Real.exp (-(β * ε) * N)) =o[atTop] fun N : ℝ => N ^ (-l) :=
    isLittleO_exp_neg_mul_rpow_atTop (mul_pos hβ hε) (-l)
  have h2 : (fun N : ℝ => N ^ (-l)) =O[atTop] powLog C l r := by
    refine IsBigO.of_bound (1 / C) ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hN0]
      exact hN
    have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos hN0 _
    have hlr : 1 ≤ Real.log N ^ r := one_le_pow₀ hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow, powLog,
      abs_of_pos (by positivity : 0 < C * N ^ (-l) * Real.log N ^ r)]
    calc N ^ (-l) = 1 / C * (C * N ^ (-l) * 1) := by field_simp
      _ ≤ 1 / C * (C * N ^ (-l) * Real.log N ^ r) := by gcongr
  refine (h1.trans_isBigO h2).congr_left fun N => ?_
  congr 1
  ring

end Laplace.Grammar
