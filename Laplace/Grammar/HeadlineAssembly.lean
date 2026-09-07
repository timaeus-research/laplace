/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ChartAssembly

/-!
# Headline XV: the assembled leading posterior quotient over a finite family of charts

Unit 208 (programme B2, step 2). A finite family of normal-block charts `a : ι`, each with its own
dimension `d a + 1`, exponents `h a`, `k a`, minimum ratio `l a` (so `p_a = 2 l_a`), multiplicity
`m_a = multCount`, continuous phase `ξ a`, observable `φ a` and density `c a > 0` on the closed
cube, all sharing `β`. With `chartIntegral` the phase-dressed integral of Headline XIII,
```
∑_a chartIntegral_a[φ_a c_a](N) / ∑_a chartIntegral_a[c_a](N)
  → ∑_{a selected} phaseCoeff_a[φ_a c_a] / ∑_{a selected} phaseCoeff_a[c_a],
```
where the selected charts are those with `p_a = min_b p_b` and `m_a = max {m_b : p_b = min}`
(`headline_assembled_posterior`). The denominator is positive because every selected
`phaseCoeff_a[c_a] > 0` (unit 205) and the selection is nonempty.

This is the conditional chart assembly of unit 207 fed with Headlines XIII–XIV. **Not** included:
the resolution-of-singularities input (that the posterior integral equals such a sum of chart
integrals with these amplitudes), Jacobians, partitions of unity, tangential variables, or random
phases; the theorem says what the leading quotient is *once* the chart decomposition is given.
The densities `c a` are required to be strictly positive on the closed cube: partition-of-unity
weights vanish at chart boundaries and do not satisfy this as stated (the abstract theorem of unit
207 allows vanishing chart coefficients and needs only a positive selected denominator sum).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- The phase-dressed chart integral `∫_{(0,1]^d} η u^h e^{-β(Nu^k)² + β(Nu^k)ξ(u)} du`. -/
noncomputable def chartIntegral (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ u in unitBox d, η u * ((∏ i, u i ^ h i) * quadKernel β (ξ u) (N * ∏ i, u i ^ k i))

/-- The chart integral with the paper's kernel written out. -/
theorem chartIntegral_eq (d : ℕ) (h k : Fin d → ℕ) (β N : ℝ) (ξ η : (Fin d → ℝ) → ℝ) :
    chartIntegral d h k β N ξ η = ∫ u in unitBox d, η u * ((∏ i, u i ^ h i) *
      Real.exp (-(β * N ^ 2 * ∏ i, u i ^ (2 * k i)) + β * (N * ∏ i, u i ^ k i) * ξ u)) := by
  unfold chartIntegral
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u _ => ?_
  rw [paperKernel_eq_quadKernel]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Headline XV (assembled leading posterior quotient)**. -/
theorem headline_assembled_posterior (d : ι → ℕ) (h k : (a : ι) → Fin (d a + 1) → ℕ)
    (hk : ∀ a i, 0 < k a i) (l : ι → ℝ) (β : ℝ) (hl : ∀ a, 0 < l a) (hβ : 0 < β)
    (hmin : ∀ a i, l a ≤ ratioExp (h a) (k a) i) (hatt : ∀ a, ∃ i, ratioExp (h a) (k a) i = l a)
    (ξ φ c : (a : ι) → (Fin (d a + 1) → ℝ) → ℝ) (hξ : ∀ a, Continuous (ξ a))
    (hφ : ∀ a, Continuous (φ a)) (hc : ∀ a, Continuous (c a))
    (hcpos : ∀ a, ∀ x ∈ closedCube (d a + 1), 0 < c a x) :
    Tendsto (fun N : ℝ =>
        (∑ a, chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (fun x => φ a x * c a x)) /
          ∑ a, chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (c a)) atTop
      (𝓝 ((∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
            multCount (ratioExp (h a) (k a)) (l a) =
              leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
          phaseCoeff (h a) (k a) (l a) β (ξ a) (fun x => φ a x * c a x)) /
        ∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
            multCount (ratioExp (h a) (k a)) (l a) =
              leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
          phaseCoeff (h a) (k a) (l a) β (ξ a) (c a))) := by
  have hm : ∀ a, 1 ≤ multCount (ratioExp (h a) (k a)) (l a) := fun a =>
    multCount_pos_of_att (h a) (k a) (l a) (hatt a)
  have hnum : ∀ a, Tendsto (fun N : ℝ =>
      chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (fun x => φ a x * c a x) /
        (N ^ (-(2 * l a)) * Real.log N ^ (multCount (ratioExp (h a) (k a)) (l a) - 1))) atTop
      (𝓝 (phaseCoeff (h a) (k a) (l a) β (ξ a) (fun x => φ a x * c a x))) := fun a =>
    phase_leading_tendsto (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a) (hatt a) (ξ a)
      (fun x => φ a x * c a x) (hξ a) ((hφ a).mul (hc a))
  have hden : ∀ a, Tendsto (fun N : ℝ =>
      chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (c a) /
        (N ^ (-(2 * l a)) * Real.log N ^ (multCount (ratioExp (h a) (k a)) (l a) - 1))) atTop
      (𝓝 (phaseCoeff (h a) (k a) (l a) β (ξ a) (c a))) := fun a =>
    phase_leading_tendsto (d a) (h a) (k a) (hk a) (l a) β (hl a) hβ (hmin a) (hatt a) (ξ a) (c a)
      (hξ a) (hc a)
  have hpos : 0 < ∑ a ∈ Finset.univ.filter (fun a => 2 * l a = leadExp (fun b => 2 * l b) ∧
      multCount (ratioExp (h a) (k a)) (l a) =
        leadMult (fun b => 2 * l b) (fun b => multCount (ratioExp (h b) (k b)) (l b))),
      phaseCoeff (h a) (k a) (l a) β (ξ a) (c a) := by
    refine Finset.sum_pos (fun a _ => phaseCoeff_pos (d a + 1) (h a) (k a) (hk a) (l a) β (hl a) hβ
      (hmin a) (ξ a) (c a) (hξ a) (hc a) (hcpos a)) ?_
    obtain ⟨a, ha1, ha2⟩ := exists_leadMult (fun b => 2 * l b)
      (fun b => multCount (ratioExp (h b) (k b)) (l b)) hm
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, ha1, ha2⟩⟩
  exact assembly_ratio_tendsto
    (fun a N => chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (fun x => φ a x * c a x))
    (fun a N => chartIntegral (d a + 1) (h a) (k a) β N (ξ a) (c a)) (fun b => 2 * l b)
    (fun b => multCount (ratioExp (h b) (k b)) (l b)) hm _ _ hnum hden hpos

end Laplace.Grammar
