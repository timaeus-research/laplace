/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Lengths along a reparametrised coordinate

For a nonnegative continuous weight `g` and a `C¹` coordinate `r`, the weighted length of the
coordinate's image is dominated by the weighted length of the parametrisation,

  `|∫_{r a}^{r b} g| ≤ ∫_a^b |r'(s)| g(r s) ds`   (`abs_integral_comp_le_integral_abs_deriv_mul`),

and if `r → ∞` along the parameter while `∫ |r'| g(r) < ∞`, then `g` is integrable on the whole
half-line (`integrableOn_Ioi_of_tendsto_atTop_of_integral_abs_deriv_mul_le`). This is the
real-analysis step of the facet accessibility theorem: a Fisher speed lower bound
`|η'|_F ≥ c |r'| g(r)` in the normal coordinate `r` plus finite path length force finite length of
the reference ray. No coarea formula or monotonicity of `r` is needed: the primitive of `g`
composed with `r` has derivative `g(r) r'`, and the fundamental theorem of calculus does the rest.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace Laplace.Multi

section Primitive

variable {g r r' : ℝ → ℝ}

/-- The substitution inequality on a compact parameter interval. -/
theorem abs_integral_comp_le_integral_abs_deriv_mul (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a b : ℝ} (hab : a ≤ b) (hr : ∀ s ∈ uIcc a b, HasDerivAt r (r' s) s)
    (hr' : ContinuousOn r' (uIcc a b)) :
    |∫ x in r a..r b, g x| ≤ ∫ s in a..b, |r' s| * g (r s) := by
  rw [← integral_comp_mul_deriv' hr hr' hg.continuousOn]
  refine (abs_integral_le_integral_abs hab).trans (le_of_eq ?_)
  refine integral_congr fun s _ ↦ ?_
  simp only [Function.comp_apply, abs_mul, abs_of_nonneg (hg0 _)]
  ring

/-- The weighted length of `[r a, R]` is dominated by the weighted parameter length up to any
time `b` with `R ≤ r b`. -/
theorem integral_le_integral_abs_deriv_mul_of_le (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a b R : ℝ} (hab : a ≤ b) (hr : ∀ s ∈ uIcc a b, HasDerivAt r (r' s) s)
    (hr' : ContinuousOn r' (uIcc a b)) (hRa : r a ≤ R) (hRb : R ≤ r b) :
    ∫ x in r a..R, g x ≤ ∫ s in a..b, |r' s| * g (r s) := by
  calc ∫ x in r a..R, g x ≤ ∫ x in r a..r b, g x :=
        integral_mono_interval le_rfl hRa hRb (ae_of_all _ fun x ↦ hg0 x)
          (hg.intervalIntegrable _ _)
    _ ≤ |∫ x in r a..r b, g x| := le_abs_self _
    _ ≤ ∫ s in a..b, |r' s| * g (r s) :=
        abs_integral_comp_le_integral_abs_deriv_mul hg hg0 hab hr hr'

/-- **Finite parameter length and an escaping coordinate give an integrable weight**: if
`r s → ∞` as `s → ∞`, `r` is `C¹` on `[a, ∞)`, and `∫_a^b |r'| g(r) ≤ I` for all `b`, then `g` is
integrable on `(r a, ∞)`. -/
theorem integrableOn_Ioi_of_tendsto_atTop_of_integral_abs_deriv_mul_le (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {a : ℝ} (hr : ∀ s, a ≤ s → HasDerivAt r (r' s) s)
    (hr' : ContinuousOn r' (Ici a)) (hlim : Tendsto r atTop atTop) {I : ℝ}
    (hI : ∀ b, a ≤ b → ∫ s in a..b, |r' s| * g (r s) ≤ I) :
    IntegrableOn g (Ioi (r a)) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded I (r a) (b := id) (l := atTop)
    (fun R ↦ hg.integrableOn_Ioc) tendsto_id ?_
  filter_upwards [eventually_ge_atTop (r a)] with R hR
  obtain ⟨b, hb⟩ := (hlim.eventually (eventually_ge_atTop R)).and (eventually_ge_atTop a)
    |>.exists
  have hsub : uIcc a b ⊆ Ici a := by
    rw [uIcc_of_le hb.2]
    exact Icc_subset_Ici_self
  calc ∫ x in r a..id R, ‖g x‖ = ∫ x in r a..R, g x := by
        simp only [id_eq]
        exact integral_congr fun x _ ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    _ ≤ ∫ s in a..b, |r' s| * g (r s) :=
        integral_le_integral_abs_deriv_mul_of_le hg hg0 hb.2 (fun s hs ↦ hr s (hsub hs))
          (hr'.mono hsub) hR hb.1
    _ ≤ I := hI b hb.2

end Primitive

end Laplace.Multi
