/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxGeneral

/-!
# Tree terms and the candidate exponent set (grammar §4.2)

In the proof of `thm:TaylorTree` the standard integral is expanded into **tree terms**

  `∫_{(0,b]^d} u^{h+s} (√n u^k)^p e^{-βn u^{2k} + β√n u^k ξ(0)} du`,

one for each shift `s = m + n ∈ ℕ^d` (from the Taylor coefficients of `η` and of `(ξ − ξ(0))^p`) and
insertion order `p`. Each such term is `n^{p/2}` times a box integral with exponents `h + s + p k`
(`treeTerm_eq`), so by unit 59 it is `~ C n^{-μ} (log n)^j` with

  `μ = min_i (h_i + s_i + 1)/(2k_i) ∈ Λ(h,k) = ⋃_i ((h_i+1)/(2k_i) + ℕ/(2k_i))`  and  `j ≤ d − 1`

(`treeTerm_isEquivalent`): exactly the exponent set and the degree bound of the theorem. The
insertion order `p` does not change the leading exponent. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The candidate exponent set `Λ(h,k) = ⋃_i ((h_i+1)/(2k_i) + ℕ/(2k_i))`. -/
def candidateSet {d : ℕ} (k h : Fin d → ℕ) : Set ℝ :=
  {μ | ∃ (i : Fin d) (s : ℕ), μ = ((h i : ℝ) + s + 1) / (2 * k i)}

/-- A tree term: exponents `h + s`, insertion `(c u^k)^p`, at scale `c`. -/
noncomputable def treeTerm (β a b c : ℝ) {d : ℕ} (k h s : Fin d → ℕ) (p : ℕ) : ℝ :=
  ∫ u : Fin d → ℝ, (∏ i, u i ^ (h i + s i)) * (c * ∏ i, u i ^ k i) ^ p
    * quadKernel β a (c * ∏ i, u i ^ k i) ∂(boxMeasure b d)

/-- **Insertion identity**: a tree term is `c^p` times a box integral with exponents
`h + s + p k`. -/
theorem treeTerm_eq (β a b c : ℝ) {d : ℕ} (k h s : Fin d → ℕ) (p : ℕ) :
    treeTerm β a b c k h s p = c ^ p * boxIntegralFin β a b c k (fun i => h i + s i + k i * p) := by
  unfold treeTerm boxIntegralFin
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [pow_add, pow_mul, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
  ring

/-- **Each tree term has a candidate exponent**: `~ C n^{-μ} (log n)^j` with `μ ∈ Λ(h,k)`,
`j ≤ d − 1`. -/
theorem treeTerm_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h s : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) (p : ℕ) :
    ∃ (μ : ℝ) (j : ℕ) (C : ℝ), μ ∈ candidateSet k h ∧ j ≤ D + 1 ∧ 0 < C ∧
      (fun n : ℝ => treeTerm β a b (Real.sqrt n) k h s p) ~[atTop]
        fun n : ℝ => C * (n ^ (-μ) * Real.log n ^ j) := by
  obtain ⟨p', m, C, hC, hmin, hcard, hE⟩ := boxIntegralFin_isEquivalent_general β a b hβ hb D k
    (fun i => h i + s i + k i * p) hk
  -- an index attaining the minimum
  have hne : (Finset.univ.filter
      fun i => finExp k (fun i => h i + s i + k i * p) i = p').Nonempty := by
    rw [← Finset.card_pos, ← hcard]; exact Nat.succ_pos m
  obtain ⟨i₀, hi₀⟩ := hne
  have hi₀' : finExp k (fun i => h i + s i + k i * p) i₀ = p' := by simpa using hi₀
  have hki₀ : (k i₀ : ℝ) ≠ 0 := by have := hk i₀; positivity
  -- the shifted exponent and the candidate exponent
  have hshift : p' = ((h i₀ : ℝ) + s i₀ + 1) / k i₀ + p := by
    rw [← hi₀', finExp]; push_cast; field_simp; try ring
  refine ⟨((h i₀ : ℝ) + s i₀ + 1) / (2 * k i₀), m, C, ⟨i₀, s i₀, rfl⟩, ?_, hC, ?_⟩
  · have : m + 1 ≤ D + 2 := by
      rw [hcard]; exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  · have hE' := (IsEquivalent.refl (u := fun n : ℝ => (Real.sqrt n) ^ p) (l := atTop)).mul hE
    refine (hE'.congr_left ?_).congr_right ?_
    · exact Filter.Eventually.of_forall fun n => by
        simp only [Pi.mul_apply]; rw [treeTerm_eq]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
      simp only [Pi.mul_apply]
      have hsq : (Real.sqrt n) ^ p = n ^ ((p : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; ring
      rw [hsq, hshift, show -((((h i₀ : ℝ) + s i₀ + 1) / k i₀ + p) / 2)
          = -(((h i₀ : ℝ) + s i₀ + 1) / (2 * k i₀)) - (p : ℝ) / 2 by field_simp; ring,
        Real.rpow_sub hn]
      field_simp

end Laplace.Grammar
