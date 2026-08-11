/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.AsymptoticDivision
import Laplace.Multi.MonomialTests

/-!
# The forward theorems

Stage 7 of the forward-expansion programme, the public face: on a
`ForwardExpansionDomain` the rescaled posterior moment of any
continuous observable of polynomial growth is an order-`N` asymptotic
polynomial at `0⁺` (`rescaledMoment_hasExpansion`) — the
rescaled-moment core of the germbij note's forward direction in the
nondegenerate case. The observable is fixed in the RESCALED variable;
the Taylor expansion of a fixed original-scale observable, and the
Wick evaluation of the coefficient integrals into explicit
polynomials in `H⁻¹` and the higher derivatives, are not formalised
here. The coefficients are the division coefficients of the numerator
expansion by the partition expansion, whose constant coefficient
`∫ e^{-T₂}` is positive. Moment families agreeing to `o(q^N)` have
equal expansion coefficients through order `N`
(`momentCoeff_eq_of_isLittleO`), the comparison face consumed
together with the merged inverse-half recovery theorems.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d N : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The constant-one observable has polynomial growth. -/
theorem hasPolynomialGrowth_one :
    HasPolynomialGrowth (fun _ : EuclidD d ↦ (1 : ℝ)) :=
  ⟨1, 0, zero_le_one, fun z ↦ by norm_num⟩

namespace ForwardExpansionDomain

/-- **Positivity of the partition constant coefficient**:
`a_0(1) = ∫ e^{-T₂} > 0`. -/
theorem numeratorCoeff_one_zero_pos (D : ForwardExpansionDomain N L H) :
    0 < D.numeratorCoeff (fun _ ↦ (1 : ℝ)) 0 := by
  have heq : D.numeratorCoeff (fun _ ↦ (1 : ℝ)) 0 =
      ∫ z : EuclidD d, Real.exp (-taylorHomogeneousTerm 2 L z) := by
    unfold ForwardExpansionDomain.numeratorCoeff
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun z ↦ ?_)
    beta_reduce
    rw [correctionCoeffFn_zero, one_mul, mul_one]
  have hint : Integrable (fun z : EuclidD d ↦
      Real.exp (-taylorHomogeneousTerm 2 L z)) := by
    have h1 := D.integrable_coeff_integrand continuous_const
      hasPolynomialGrowth_one 0
    refine h1.congr (Filter.Eventually.of_forall fun z ↦ ?_)
    beta_reduce
    rw [correctionCoeffFn_zero, one_mul, mul_one]
  rw [heq, MeasureTheory.integral_pos_iff_support_of_nonneg
    (fun z ↦ (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun z : EuclidD d ↦
      Real.exp (-taylorHomogeneousTerm 2 L z)) = Set.univ :=
    Set.eq_univ_of_forall fun z ↦
      Function.mem_support.mpr (Real.exp_pos _).ne'
  rw [hsupp]
  exact MeasureTheory.Measure.measure_univ_pos.mpr (NeZero.ne _)

/-- The moment expansion coefficients: numerator divided by
partition. -/
noncomputable def momentCoeff (D : ForwardExpansionDomain N L H)
    (P : EuclidD d → ℝ) : ℕ → ℝ :=
  divisionCoeff (D.numeratorCoeff P) (D.numeratorCoeff fun _ ↦ (1 : ℝ))

/-- **The moment expansion** (the germbij forward direction, in the
nondegenerate case): the rescaled posterior moment of any continuous
observable of polynomial growth is an order-`N` asymptotic polynomial
at `0⁺`. -/
theorem rescaledMoment_hasExpansion (D : ForwardExpansionDomain N L H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Laplace.IsAsymptoticExpansionTo
      (fun q : ℝ ↦ D.toHigherLaplaceDomain.rescaledMoment P q)
      (D.momentCoeff P) N := by
  have hnum := D.numerator_hasExpansion hP_cont hP_growth
  have hden := D.numerator_hasExpansion continuous_const
    hasPolynomialGrowth_one
  exact isAsymptoticExpansionTo_div hnum hden
    (ne_of_gt D.numeratorCoeff_one_zero_pos)

/-- Existence form of the moment expansion. -/
theorem rescaledMoment_expansion_exists
    (D : ForwardExpansionDomain N L H) {P : EuclidD d → ℝ}
    (hP_cont : Continuous P) (hP_growth : HasPolynomialGrowth P) :
    ∃ c : ℕ → ℝ, Laplace.IsAsymptoticExpansionTo
      (fun q : ℝ ↦ D.toHigherLaplaceDomain.rescaledMoment P q) c N :=
  ⟨D.momentCoeff P, D.rescaledMoment_hasExpansion hP_cont hP_growth⟩

/-- The monomial moment expansions: the instances the inverse-half
recovery theorems consume. The bridge to the note's original-scale
observables: under `w = q • z` the cut monomial `φ_m(w) = w^m·χ(w)`
becomes `q^k · monomialTest m z` on the region where the cutoff is
one, so the rescaled monomial moment is the original monomial
posterior moment with the `q^k` prefactor removed, up to a tail
beyond all orders. A FIXED original-scale observable `φ(w)` would
become the `q`-dependent `z ↦ φ(q • z)`; that observable-Taylor
packaging is not formalised here — the monomial instances carry the
content the recovery theorems need. -/
theorem monomial_moment_hasExpansion (D : ForwardExpansionDomain N L H)
    {k : ℕ} (m : Fin k → Fin d) :
    Laplace.IsAsymptoticExpansionTo
      (fun q : ℝ ↦
        D.toHigherLaplaceDomain.rescaledMoment (monomialTest m) q)
      (D.momentCoeff (monomialTest m)) N :=
  D.rescaledMoment_hasExpansion (monomialTest_continuous m)
    (monomialTest_hasPolynomialGrowth m)

end ForwardExpansionDomain

/-- **Jet comparison**: moment families agreeing to `o(q^N)` have
equal expansion coefficients through order `N`. -/
theorem momentCoeff_eq_of_isLittleO {d N : ℕ}
    {L₁ L₂ : EuclidD d → ℝ} {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}
    (D₁ : ForwardExpansionDomain N L₁ H₁)
    (D₂ : ForwardExpansionDomain N L₂ H₂)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P)
    (hagree : (fun q : ℝ ↦
        D₁.toHigherLaplaceDomain.rescaledMoment P q -
          D₂.toHigherLaplaceDomain.rescaledMoment P q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N) :
    ∀ j ≤ N, D₁.momentCoeff P j = D₂.momentCoeff P j := by
  have h1 := D₁.rescaledMoment_hasExpansion hP_cont hP_growth
  have h2 := D₂.rescaledMoment_hasExpansion hP_cont hP_growth
  have h2' : Laplace.IsAsymptoticExpansionTo
      (fun q : ℝ ↦ D₂.toHigherLaplaceDomain.rescaledMoment P q)
      (D₁.momentCoeff P) N := by
    unfold Laplace.IsAsymptoticExpansionTo at h1 ⊢
    have hcomb := hagree.neg_left.add h1
    refine hcomb.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with q
    ring
  exact Laplace.isAsymptoticExpansionTo_coeff_eq h2' h2

end Laplace.Multi
