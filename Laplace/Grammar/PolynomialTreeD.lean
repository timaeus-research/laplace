/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialTreeD
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The polynomial Taylor tree in `d` dimensions (grammar §4.2, `eq:flucttreeterms`)

For a polynomial perturbation `J(u) = ∑_{γ ∈ S} c_γ u^γ` the `p`-th layer of the exponential tree
(unit 62) expands by the multinomial theorem into a finite sum of tree terms (unit 60):

  `(J u)^p = ∑_{κ ∈ piAntidiag S p} multinomial(κ) ∏_γ c_γ^{κ_γ} · u^{∑_γ κ_γ γ}`,

so the chart standard integral with `ξ = a + J` is the exact double series

  `Z = ∑_p (β^p/p!) ∑_{κ} multinomial(κ) (∏_γ c_γ^{κ_γ}) · treeTerm(∑_γ κ_γ γ, p)`

(`boxIntegralXi_polynomial_hasSum`). The inner coefficients are the paper's `ξ_{n,p}` grouped by
composition; by unit 60 every term has leading exponent in `Λ(h,k)`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- A polynomial perturbation `J(u) = ∑_{γ ∈ S} c_γ u^γ`. -/
noncomputable def polyJ {d : ℕ} (S : Finset (Fin d → ℕ)) (coef : (Fin d → ℕ) → ℝ)
    (u : Fin d → ℝ) : ℝ :=
  ∑ γ ∈ S, coef γ * ∏ i, u i ^ γ i

theorem polyJ_continuous {d : ℕ} (S : Finset (Fin d → ℕ)) (coef : (Fin d → ℕ) → ℝ) :
    Continuous (polyJ S coef) :=
  continuous_finsetSum _ fun γ _ => continuous_const.mul (continuous_prod_pow γ)

/-- The multi-index shift `∑_γ κ_γ γ` of a composition `κ`. -/
def compShift {d : ℕ} (S : Finset (Fin d → ℕ)) (κ : (Fin d → ℕ) → ℕ) (i : Fin d) : ℕ :=
  ∑ γ ∈ S, κ γ * γ i

theorem integrable_box_of_continuous (b : ℝ) {d : ℕ} (F : (Fin d → ℝ) → ℝ) (hF : Continuous F) :
    Integrable F (boxMeasure b d) := by
  rw [boxMeasure_eq_restrict]
  exact (hF.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Ioc_subset_Icc_self)

/-- **Multinomial expansion of `J^p`** into monomials `u^{∑ κ_γ γ}`. -/
theorem polyJ_pow {d : ℕ} (S : Finset (Fin d → ℕ)) (coef : (Fin d → ℕ) → ℝ) (u : Fin d → ℝ)
    (p : ℕ) :
    polyJ S coef u ^ p = ∑ κ ∈ Finset.piAntidiag S p,
      (Nat.multinomial S κ : ℝ) * (∏ γ ∈ S, coef γ ^ κ γ) * ∏ i, u i ^ compShift S κ i := by
  rw [polyJ, Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold compShift
  exact Finset.sum_congr rfl fun γ _ => Nat.mul_comm _ _

/-- **Each layer is a finite sum of tree terms** for a polynomial perturbation. -/
theorem treeLayer_polynomial (β a b c : ℝ) {d : ℕ} (S : Finset (Fin d → ℕ))
    (coef : (Fin d → ℕ) → ℝ) (k h : Fin d → ℕ) (p : ℕ) :
    treeLayer β a b c k h (polyJ S coef) p
      = β ^ p / p.factorial * ∑ κ ∈ Finset.piAntidiag S p,
          (Nat.multinomial S κ : ℝ) * (∏ γ ∈ S, coef γ ^ κ γ)
            * treeTerm β a b c k h (compShift S κ) p := by
  unfold treeLayer
  congr 1
  have hcontS : Continuous fun u : Fin d → ℝ => c * ∏ i, u i ^ k i :=
    continuous_const.mul (continuous_prod_pow k)
  have hpt : ∀ u : Fin d → ℝ, (∏ i, u i ^ h i) * ((c * ∏ i, u i ^ k i) * polyJ S coef u) ^ p
      * quadKernel β a (c * ∏ i, u i ^ k i)
      = ∑ κ ∈ Finset.piAntidiag S p, (Nat.multinomial S κ : ℝ) * (∏ γ ∈ S, coef γ ^ κ γ)
        * ((∏ i, u i ^ (h i + compShift S κ i)) * (c * ∏ i, u i ^ k i) ^ p
          * quadKernel β a (c * ∏ i, u i ^ k i)) := by
    intro u
    rw [mul_pow, polyJ_pow]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [pow_add, Finset.prod_mul_distrib]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum (Finset.piAntidiag S p)
    (f := fun κ u => (Nat.multinomial S κ : ℝ) * (∏ γ ∈ S, coef γ ^ κ γ)
      * ((∏ i, u i ^ (h i + compShift S κ i)) * (c * ∏ i, u i ^ k i) ^ p
        * quadKernel β a (c * ∏ i, u i ^ k i)))
    (fun κ _ => integrable_box_of_continuous b _
      (continuous_const.mul (((continuous_prod_pow _).mul (hcontS.pow p)).mul
        ((quadKernel_continuous β a).comp hcontS))))]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- **The polynomial Taylor tree**: `Z(a + J)` is the exact double series over insertion orders `p`
and compositions `κ` of tree terms. -/
theorem boxIntegralXi_polynomial_hasSum (β a b c : ℝ) (hβ : 0 < β) (hb : 0 < b) (hc : 0 ≤ c)
    {d : ℕ} (S : Finset (Fin d → ℕ)) (coef : (Fin d → ℕ) → ℝ) (k h : Fin d → ℕ) :
    HasSum (fun p : ℕ => β ^ p / p.factorial * ∑ κ ∈ Finset.piAntidiag S p,
        (Nat.multinomial S κ : ℝ) * (∏ γ ∈ S, coef γ ^ κ γ)
          * treeTerm β a b c k h (compShift S κ) p)
      (boxIntegralXi β a b c k h (polyJ S coef)) :=
  (boxIntegralXi_hasSum β a b c hβ hb hc k h _ (polyJ_continuous S coef)).congr_fun
    fun p => (treeLayer_polynomial β a b c S coef k h p).symm

end Laplace.Grammar
