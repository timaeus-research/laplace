/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TreeSeries

/-!
# The monomial Taylor tree in `d` dimensions (grammar §4.2)

For `ξ = a + c₀ u^γ` (a single monomial perturbation) each layer of the exponential tree of unit 62
is one tree term of unit 60 with shift `p γ` and insertion order `p`, so the chart standard integral
is an exact convergent series of box integrals with shifted exponents:

  `Z(a + c₀ u^γ) = ∑_p ((β c₀ c)^p / p!) ∫ u^{h + pγ + pk} f(c u^k) du`

(`boxIntegralXi_monomial_hasSum`, `boxIntegralXi_monomial_hasSum'`). This is the `d`-dimensional
analogue of unit 26's one-dimensional monomial tree; by unit 60 every term has leading exponent in
`Λ(h,k)`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- For a monomial `J = c₀ u^γ`, the `p`-th layer is `(β c₀)^p/p!` times the tree term with shift
`p γ` and insertion order `p`. -/
theorem treeLayer_monomial (β a b c c₀ : ℝ) {d : ℕ} (k h γ : Fin d → ℕ) (p : ℕ) :
    treeLayer β a b c k h (fun u => c₀ * ∏ i, u i ^ γ i) p
      = (β * c₀) ^ p / p.factorial * treeTerm β a b c k h (fun i => γ i * p) p := by
  unfold treeLayer treeTerm
  have hpt : ∀ u : Fin d → ℝ, (∏ i, u i ^ h i) * ((c * ∏ i, u i ^ k i) * (c₀ * ∏ i, u i ^ γ i)) ^ p
      * quadKernel β a (c * ∏ i, u i ^ k i)
      = c₀ ^ p * ((∏ i, u i ^ (h i + γ i * p)) * (c * ∏ i, u i ^ k i) ^ p
        * quadKernel β a (c * ∏ i, u i ^ k i)) := by
    intro u
    simp only [pow_add, pow_mul, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul, mul_pow]
  ring

/-- **The monomial Taylor tree**: `Z(a + c₀ u^γ) = ∑_p ((β c₀)^p/p!) · treeTerm(pγ, p)`. -/
theorem boxIntegralXi_monomial_hasSum (β a b c c₀ : ℝ) (hβ : 0 < β) (hb : 0 < b) (hc : 0 ≤ c)
    {d : ℕ} (k h γ : Fin d → ℕ) :
    HasSum (fun p : ℕ => (β * c₀) ^ p / p.factorial * treeTerm β a b c k h (fun i => γ i * p) p)
      (boxIntegralXi β a b c k h (fun u => c₀ * ∏ i, u i ^ γ i)) := by
  have hJ : Continuous fun u : Fin d → ℝ => c₀ * ∏ i, u i ^ γ i :=
    continuous_const.mul (continuous_prod_pow γ)
  have := boxIntegralXi_hasSum β a b c hβ hb hc k h _ hJ
  refine this.congr_fun fun p => ?_
  exact (treeLayer_monomial β a b c c₀ k h γ p).symm

/-- **The monomial Taylor tree, box form**:
`Z(a + c₀ u^γ) = ∑_p ((β c₀ c)^p/p!) ∫ u^{h + pγ + kp} f(c u^k) du`. -/
theorem boxIntegralXi_monomial_hasSum' (β a b c c₀ : ℝ) (hβ : 0 < β) (hb : 0 < b) (hc : 0 ≤ c)
    {d : ℕ} (k h γ : Fin d → ℕ) :
    HasSum (fun p : ℕ => (β * c₀ * c) ^ p / p.factorial
        * boxIntegralFin β a b c k (fun i => h i + γ i * p + k i * p))
      (boxIntegralXi β a b c k h (fun u => c₀ * ∏ i, u i ^ γ i)) := by
  refine (boxIntegralXi_monomial_hasSum β a b c c₀ hβ hb hc k h γ).congr_fun fun p => ?_
  rw [treeTerm_eq, mul_pow (β * c₀) c]
  ring

end Laplace.Grammar
