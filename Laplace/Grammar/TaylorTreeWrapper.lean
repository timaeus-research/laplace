/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxTaylorTree
import Laplace.Grammar.FluctuationDerivativeMu

/-!
# The Taylor tree: end-to-end statement for coefficient-family data (Stage 5f)

Unit 256 (Astra #30 release task). One theorem assembling Headlines XXVIII, XXIX and XXX, with the
quantifier order `∃ coefficient system, ∀ cutoff`: for phase and amplitude given on `(0,b]^d` by
coefficient families with finite weighted mass `∑ |c_γ| b^{|γ|}`, `β > 0`, `kᵢ ≥ 1`, there is one
coefficient system `C μ j` (the family coefficients of the rescaled data) such that

* `C` is independent of the cutoff and of `N`, vanishes off the paper's candidate set `Λ(h,k)`, and
  equals the paper's explicit absolutely convergent Cauchy-product series `∑_p β^p/p! T_p(cη *
      J^{*p})`;
* for every cutoff `L > 0` the remainder of `Z_b(N) − b^{|h|+d} ∑_{μ ∈ Λ_L} (N b^{2|k|})^{-μ}
  ∑_{j ≤ d-1}
  C μ j (log(N b^{2|k|}))^j` is bounded by an explicit `N`-free constant times
  `(N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^{d-1}` whenever `N b^{2|k|} ≥ 1`, and is
  `O(N^{-L}(1+log N)^{d-1})` as `N → ∞`;
* the fluctuation moments in the kernel of `T_p` carry the paper's derivative notation
  `β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)` for `μ > 0`.

This is `thm:TaylorTree` / `cor:standardintegralexp` under the coefficient-summability form of the
analytic hypothesis (`thm_TaylorTree_coeffFamily`); the implication from holomorphy on a polydisc to
that hypothesis is not part of this development. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The conclusion of the Taylor-tree theorem for a coefficient system `C` on the box `(0,b]^d`. -/
structure TaylorTreeConclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ) : Prop where
  /-- `C` is the family spectral coefficient of the rescaled data. -/
  coeff_eq : ∀ μ j, C μ j = familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ j
  /-- Support: `C` vanishes off the paper's candidate exponent set `Λ(h,k)`. -/
  vanish : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0
  /-- The explicit series is absolutely convergent (`μ > 0`). -/
  summable : ∀ μ, 0 < μ → ∀ j,
    Summable fun p => |familyCoeffTerm n h k β (scale cξ b) (scale cη b) μ j p|
  /-- `C` equals the paper's Cauchy-product series `∑_p β^p/p! T_p(cη * J^{*p})`, every real `μ`. -/
  series : ∀ μ j, C μ j = familyCoeffSeries n h k β (scale cξ b) (scale cη b) μ j
  /-- Quantitative remainder for every cutoff, with `N b^{2|k|} ≥ 1`. -/
  remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N →
    |familyPhaseIntegralBox n h k β N b cξ cη - b ^ (∑ i, h i + (n + 1)) *
        ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) *
          ∑ j ∈ Finset.range (n + 1), C μ j * (Real.log (boxScale k b N)) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) *
        cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)
  /-- Asymptotic form in the sample size. -/
  isBigO : ∀ L, 0 < L →
    (fun N : ℝ => familyPhaseIntegralBox n h k β N b cξ cη - boxSpectralSum n h k β L b cξ cη N)
      =O[atTop] fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n
  /-- The paper's derivative dictionary for the kernel moments (`μ > 0`). -/
  dictionary : ∀ (a : ℝ) (p : ℕ) (μ : ℝ), 0 < μ → ∀ i : ℕ,
    β ^ p * fluctMoment β a p μ i =
      (-1) ^ i * iteratedDeriv i (fun ν => iteratedDeriv p (fluctuationFn β ν) a) μ

/-- **The Taylor tree for coefficient-family data** (`thm:TaylorTree` / `cor:standardintegralexp`
under `∑ |c_γ| b^{|γ|} < ∞`): one cutoff-independent coefficient system, equal to the paper's
explicit series, with the remainder bound for every cutoff and the derivative dictionary. -/
theorem thm_TaylorTree_coeffFamily (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) :
    ∃ C : ℝ → ℕ → ℝ, TaylorTreeConclusion n h k β b cξ cη C := by
  have hξ' : AbsSummable (scale cξ b) := AbsSummable.of_scale hb.le hξ
  have hη' : AbsSummable (scale cη b) := AbsSummable.of_scale hb.le hη
  refine ⟨familySpectralCoeff n h k β (scale cξ b) (scale cη b), ?_⟩
  refine
    { coeff_eq := fun _ _ => rfl
      vanish := fun μ j hμ =>
        familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ' hη' hμ j
      summable := fun μ hμ j => summable_familyCoeffSeries_terms n h k hk β hβ hξ' hη' hμ j
      series := fun μ j => familySpectralCoeff_eq_series' n h k hk β hβ hξ' hη' μ j
      remainder := fun L hL N hN hN' => ?_
      isBigO := fun L hL => boxTaylorTree_isBigO n h k hk β hβ hL hb hξ hη
      dictionary := fun a p μ hμ i => fluctMoment_eq_mixed_deriv β hβ p a hμ i }
  have := boxTaylorTree_cutoff_bound n h k hk β hβ hL hb hN hN' hξ hη
  unfold boxSpectralSum familySpectralSum at this
  exact this

end Laplace.Grammar
