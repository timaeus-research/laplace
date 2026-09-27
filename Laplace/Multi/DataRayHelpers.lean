/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PathLengthPrimitive
import Laplace.Multi.FacetSchurBound

/-!
# Helpers for the reverse data-ray theorem

* the one-sided weighted variation inequality: for a nonnegative continuous weight `g` and a `C¹`
  coordinate `r ≥ R`, `∫_a^b g(r)|r'| ≤ ∫_R^∞ g + 2 ∫_a^b g(r) (r')₋`
  (`integral_mul_abs_deriv_le`), since `g(r)|r'| = (G ∘ r)' + 2 g(r) (r')₋` for the primitive
  `G` of `g`;
* the standard-deviation triangle inequality `√Var(f + g) ≤ √Var f + √Var g`
  (`sqrt_lawCov_add_self_le`);
* `Var f ≤ K²` for `|f| ≤ K` (`lawCov_self_le_sq`).
-/

open MeasureTheory Set Filter intervalIntegral

namespace Laplace.Multi

section Variation

variable {g r r' : ℝ → ℝ}

theorem abs_eq_add_two_mul_max_neg (x : ℝ) : |x| = x + 2 * max (-x) 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_right (neg_nonpos.2 h)]
    ring
  · rw [abs_of_neg h, max_eq_left (neg_nonneg.2 h.le)]
    ring

/-- **One-sided weighted variation**: the weighted length of a coordinate is controlled by the
integral of the weight beyond the lower bound and the weighted negative variation. -/
theorem integral_mul_abs_deriv_le (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {a b R : ℝ}
    (hr : ∀ s ∈ uIcc a b, HasDerivAt r (r' s) s) (hr' : ContinuousOn r' (uIcc a b))
    (hR : ∀ s ∈ uIcc a b, R ≤ r s) (hgint : IntegrableOn g (Ioi R)) :
    ∫ s in a..b, g (r s) * |r' s| ≤
      (∫ x in Ioi R, g x) + 2 * ∫ s in a..b, g (r s) * max (-r' s) 0 := by
  have hrc : ContinuousOn r (uIcc a b) := HasDerivAt.continuousOn hr
  have e : ∀ s, g (r s) * |r' s| = g (r s) * r' s + 2 * (g (r s) * max (-r' s) 0) := fun s ↦ by
    rw [abs_eq_add_two_mul_max_neg]
    ring
  have hint1 : IntervalIntegrable (fun s ↦ g (r s) * r' s) volume a b :=
    ((hg.comp_continuousOn hrc).mul hr').intervalIntegrable
  have hmax : ContinuousOn (fun s ↦ max (-r' s) 0) (uIcc a b) :=
    ContinuousOn.sup hr'.neg continuousOn_const
  have hint2 : IntervalIntegrable (fun s ↦ g (r s) * max (-r' s) 0) volume a b :=
    ((hg.comp_continuousOn hrc).mul hmax).intervalIntegrable
  simp_rw [e]
  rw [integral_add hint1 (hint2.const_mul 2), intervalIntegral.integral_const_mul]
  gcongr
  have hsub : ∫ s in a..b, g (r s) * r' s = ∫ x in r a..r b, g x := by
    have := integral_comp_mul_deriv' hr hr' hg.continuousOn
    simpa [Function.comp_def] using this
  rw [hsub]
  have hra : R ≤ r a := hR a left_mem_uIcc
  have hrb : R ≤ r b := hR b right_mem_uIcc
  have hpos : 0 ≤ ∫ x in Ioi R, g x := setIntegral_nonneg measurableSet_Ioi fun x _ ↦ hg0 x
  rcases le_or_gt (r a) (r b) with h | h
  · rw [integral_of_le h]
    refine setIntegral_mono_set hgint (ae_of_all _ fun x ↦ hg0 x) ?_
    exact (show Ioc (r a) (r b) ⊆ Ioi R from fun x hx ↦ lt_of_le_of_lt hra hx.1).eventuallyLE
  · rw [integral_symm, integral_of_le h.le]
    have : 0 ≤ ∫ x in Ioc (r b) (r a), g x :=
      setIntegral_nonneg measurableSet_Ioc fun x _ ↦ hg0 x
    linarith

end Variation

section Covariance

variable {X : Type*} [MeasurableSpace X] (q : Measure X) [IsProbabilityMeasure q]

/-- **The standard-deviation triangle inequality**: `√Var(f + g) ≤ √Var f + √Var g`. -/
theorem sqrt_lawCov_add_self_le {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    √(lawCov q (fun x ↦ f x + g x) (fun x ↦ f x + g x)) ≤ √(lawCov q f f) + √(lawCov q g g) := by
  have hVf := lawCov_self_nonneg q hf
  have hVg := lawCov_self_nonneg q hg
  rw [lawCov_add_self q hf hg]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hcs := lawCov_sq_le q hf hg
  have hcov : lawCov q f g ≤ √(lawCov q f f) * √(lawCov q g g) := by
    rw [← Real.sqrt_mul hVf]
    exact Real.le_sqrt_of_sq_le hcs
  have e : (√(lawCov q f f) + √(lawCov q g g)) ^ 2 =
      lawCov q f f + 2 * (√(lawCov q f f) * √(lawCov q g g)) + lawCov q g g := by
    rw [add_sq, Real.sq_sqrt hVf, Real.sq_sqrt hVg]
    ring
  rw [e]
  linarith

/-- `Var f ≤ K²` for `|f| ≤ K`. -/
theorem lawCov_self_le_sq {f : X → ℝ} (hf : Bdd f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    lawCov q f f ≤ K ^ 2 := by
  refine (lawCov_self_le_integral_sq q hf 0).trans ?_
  calc ∫ x, (f x - 0) * (f x - 0) ∂q ≤ ∫ _, K ^ 2 ∂q := by
        refine integral_mono (integrable_of_bdd_prob q ((hf.sub (Bdd.const 0)).mul
          (hf.sub (Bdd.const 0)))) (integrable_const _) fun x ↦ ?_
        rw [sub_zero, ← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
    _ = K ^ 2 := by simp

end Covariance

end Laplace.Multi
