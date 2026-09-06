/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogTwoD

/-!
# The two-dimensional standard integral as a genuine double integral (grammar §4.2, `d = 2`)

`LogTwoD.lean` states `Z₂(n)` as an iterated integral. Here we identify it with the integral over
the product set `(0,b]² ⊆ ℝ²` against two-dimensional Lebesgue measure (Fubini for the continuous,
hence
compactly integrable, integrand), so that the `log n` asymptotic reads exactly as the paper's
`∫_{[0,b]^2} e^{-βn u^{2k} + β√n u^k ξ} du ~ (S_{1/2}(a)/4) n^{-1/2} log n`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- The `d = 2` chart standard integral over the product set `(0,b]²` against Lebesgue measure on
`ℝ²` (`k = (1,1)`, `h = (0,0)`, `ξ ≡ a`, `η ≡ 1`). -/
noncomputable def twoDIntegralProd (β a b n : ℝ) : ℝ :=
  ∫ z in Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b,
    Real.exp (-β * n * (z.1 * z.2) ^ 2 + β * Real.sqrt n * (z.1 * z.2) * a)

/-- **Fubini**: the double integral equals the iterated integral. -/
theorem twoDIntegralProd_eq (β a b n : ℝ) : twoDIntegralProd β a b n = twoDIntegral β a b n := by
  unfold twoDIntegralProd twoDIntegral
  have hcont : Continuous (fun z : ℝ × ℝ =>
      Real.exp (-β * n * (z.1 * z.2) ^ 2 + β * Real.sqrt n * (z.1 * z.2) * a)) := by fun_prop
  have hint : IntegrableOn (fun z : ℝ × ℝ =>
      Real.exp (-β * n * (z.1 * z.2) ^ 2 + β * Real.sqrt n * (z.1 * z.2) * a))
      (Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [show (volume : Measure (ℝ × ℝ)).restrict (Ioc (0 : ℝ) b ×ˢ Ioc (0 : ℝ) b)
      = ((volume : Measure ℝ).restrict (Ioc 0 b)).prod
          ((volume : Measure ℝ).restrict (Ioc 0 b)) from
      (Measure.prod_restrict _ _).symm]
  rw [integral_prod _ (by rw [Measure.prod_restrict]; exact hint)]

/-- **The first `log n`, as a double integral**: for the `d = 2`, `k = (1,1)`, `h = (0,0)` chart,
`∫_{(0,b]²} e^{-βn (uv)² + β√n uv a} d(u,v) ~ (S_{1/2}(a)/4) · n^{-1/2} · log n`. -/
theorem twoDIntegralProd_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => twoDIntegralProd β a b n) ~[atTop]
      fun n : ℝ => fluctuation β (1 / 2) a / 4 * (n ^ (-(1 / 2 : ℝ)) * Real.log n) := by
  have : (fun n : ℝ => twoDIntegralProd β a b n) = fun n : ℝ => twoDIntegral β a b n :=
    funext fun n => twoDIntegralProd_eq β a b n
  rw [this]
  exact twoDIntegral_isEquivalent β a b hβ hb

end Laplace.Grammar
