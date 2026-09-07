/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoordDeriv

/-!
# The Taylor tree with Taylor-derivative coefficient families (Stage 8c — Headline XXXIII)

Unit 268 (Astra #32, unit 4 of the derivative-identification sprint). The coefficient families of
Headline XXXII are identified with the normalised Taylor derivatives: `taylorFamily d F γ =
Re(∂^γ F(0)/γ!)` (`polyRealCoeff_eq_taylorFamily`), and the paper-facing theorem
`thm_TaylorTree_taylor` states `thm:TaylorTree` / `cor:standardintegralexp` for these families
directly: for real `ξ, η` on `(0,b]^d` with holomorphic `Fξ, Fη` on the polydisc of radius `R > b`
agreeing with `ξ, η` in real part on the box, the Taylor-tree conclusion holds for the families
`γ ↦ Re(∂^γ Fξ(0)/γ!)`, `γ ↦ Re(∂^γ Fη(0)/γ!)`, and the family integral is the original `Z(N)`.

**Non-claims.** `∂^γ` is the fixed-order iterated coordinate derivative `coordDeriv` (no
permutation-invariance theorem). The families are the Taylor coefficients of the canonical
real-analytic representative `Re F` at `0`, not derivatives of the supplied real functions `ξ, η`,
which are constrained only on the positive box `(0,b]^d` (in particular `taylorFamily Fξ 0 =
Re Fξ(0)`, which need not equal the supplied value `ξ(0)`); when `Fξ` is a genuine holomorphic
extension of a real-analytic `ξ` from a real neighbourhood of `0`, these are the Taylor coefficients
of `ξ`.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The normalised Taylor-derivative family `γ ↦ Re(∂^γ F(0)/γ!)`. -/
noncomputable def taylorFamily (d : ℕ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d :=
  fun γ => (coordDeriv d F γ / multiFactorial γ).re

/-- The real Cauchy-coefficient family of Headline XXXII is the Taylor-derivative family. -/
theorem polyRealCoeff_eq_taylorFamily {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    polyRealCoeff d r F = taylorFamily d F :=
  funext (polyRealCoeff_eq hr hrR hF)

/-- The constant coefficient is `Re F(0)`. -/
theorem taylorFamily_zero (d : ℕ) (F : (Fin d → ℂ) → ℂ) : taylorFamily d F 0 = (F 0).re := by
  unfold taylorFamily
  rw [coordDeriv_zero]
  simp [multiFactorial]

/-- **Headline XXXIII — `thm:TaylorTree` with Taylor-derivative coefficients, every dimension.**
For real `ξ, η` on `(0,b]^d` with holomorphic `Fξ, Fη` on the polydisc `{|zᵢ| < R}`, `R > b`,
whose real parts agree with `ξ, η` on the box, the Taylor-tree conclusion holds for the families
`γ ↦ Re(∂^γ Fξ(0)/γ!)`, `γ ↦ Re(∂^γ Fη(0)/γ!)` and the family integral is the original
`Z(N) = ∫_{(0,b]^d} η u^h e^{-βN u^{2k} + β√N u^k ξ(u)} du`. -/
theorem thm_TaylorTree_taylor (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (taylorFamily (n + 1) Fξ) (taylorFamily (n + 1) Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b (taylorFamily (n + 1) Fξ)
        (taylorFamily (n + 1) Fη) = origPhaseIntegral n h k β N b ξ η := by
  have hbr : b < (b + R) / 2 := by linarith
  have hrR : (b + R) / 2 < R := by linarith
  have hr : 0 < (b + R) / 2 := by linarith
  have H := thm_TaylorTree_analytic n h k hk β hβ hb hbr hrR hFξ hFη hξ hη
  rwa [polyRealCoeff_eq_taylorFamily hr hrR hFξ, polyRealCoeff_eq_taylorFamily hr hrR hFη] at H

end Laplace.Grammar
