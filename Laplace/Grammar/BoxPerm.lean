/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SortedTower

/-!
# Permutation invariance of the box integral (grammar §4.2)

The box integral of unit 54 does not depend on the order of the coordinates: for a permutation `σ`
of `Fin d`, integrating with exponents `k ∘ σ, h ∘ σ` gives the same value (Lebesgue measure on the
box is permutation invariant, `measurePreserving_piCongrLeft`). Together with a bridge from
`Fin d`-indexed exponents to the `ℕ`-indexed ones used by the recursion, this lets the
sorted-exponent theorem of unit 57 be applied after relabelling the coordinates.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The box integral with `Fin d`-indexed exponents. -/
noncomputable def boxIntegralFin (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) : ℝ :=
  ∫ u : Fin d → ℝ, (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i) ∂(boxMeasure b d)

theorem boxIntegralFin_eq_boxIntegral (β a b c : ℝ) (k h : ℕ → ℕ) (d : ℕ) :
    boxIntegralFin β a b c (fun i : Fin d => k i) (fun i : Fin d => h i)
      = boxIntegral β a b c k h d := rfl

/-- **Permutation invariance.** -/
theorem boxIntegralFin_perm (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    boxIntegralFin β a b c (k ∘ σ) (h ∘ σ) = boxIntegralFin β a b c k h := by
  have hmp := measurePreserving_piCongrLeft
    (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b)) σ
  unfold boxIntegralFin boxMeasure
  have key := hmp.integral_comp'
    (fun v : Fin d → ℝ => (∏ i, v i ^ h i) * quadKernel β a (c * ∏ i, v i ^ k i))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ∀ g : Fin d → ℕ,
      ∏ i, (MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) σ x) i ^ g i
        = ∏ i, x i ^ g (σ i) := by
    intro g
    refine (Fintype.prod_equiv σ (fun i => x i ^ g (σ i))
      (fun i => (MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) σ x) i ^ g i) fun i => ?_).symm
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [Function.comp_apply]
  rw [h1 h, h1 k]

/-- Extension of a `Fin d`-indexed exponent vector to `ℕ`, with a default value beyond `d`. -/
def toNatFun {d : ℕ} (g : Fin d → ℕ) (v : ℕ) : ℕ → ℕ :=
  fun i => if hi : i < d then g ⟨i, hi⟩ else v

theorem toNatFun_coe {d : ℕ} (g : Fin d → ℕ) (v : ℕ) (i : Fin d) : toNatFun g v (i : ℕ) = g i := by
  simp [toNatFun, i.isLt]

theorem toNatFun_pos {d : ℕ} (g : Fin d → ℕ) (hg : ∀ i, 0 < g i) : ∀ i, 0 < toNatFun g 1 i := by
  intro i
  unfold toNatFun
  split_ifs with hi
  · exact hg _
  · exact one_pos

/-- The `Fin`-indexed box integral equals the `ℕ`-indexed one for the extended exponents. -/
theorem boxIntegralFin_eq_toNatFun (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) :
    boxIntegralFin β a b c k h = boxIntegral β a b c (toNatFun k 1) (toNatFun h 0) d := by
  rw [← boxIntegralFin_eq_boxIntegral]
  congr 1 <;> funext i <;> rw [toNatFun_coe]

/-- Exponents of the extended vector on `Fin d`. -/
theorem chartExp_toNatFun {d : ℕ} (k h : Fin d → ℕ) (i : Fin d) :
    chartExp (toNatFun k 1) (toNatFun h 0) (i : ℕ) = ((h i : ℝ) + 1) / k i := by
  rw [chartExp, toNatFun_coe, toNatFun_coe]

/-- **Only minimal exponents count, box form**: if a relabelling `σ` of the coordinates sorts the
exponents as in unit 57 (`r+1` non-increasing noncritical ones, then `m+1` equal to the minimum
`p`),
the box integral over `(0,b]^{r+2+m}` satisfies `∫ ~ K D · C/(2^m m!) · n^{-p/2} (log n)^m`. -/
theorem boxIntegralFin_isEquivalent_of_perm (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (r m : ℕ)
    (k h : Fin (r + 2 + m) → ℕ) (hk : ∀ i, 0 < k i) (σ : Equiv.Perm (Fin (r + 2 + m))) (p : ℝ)
    (hsort : ∀ i, i < r → chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (i + 1)
      ≤ chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) i)
    (hp : ∀ l, r + 1 ≤ l → l ≤ r + 1 + m →
      chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) l = p)
    (hlt : p < chartExp (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r) :
    (fun n : ℝ => boxIntegralFin β a b (Real.sqrt n) k h) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (r + 2 + m), (1 : ℝ) / toNatFun (k ∘ σ) 1 i)
        * genScale b (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) (r + 2 + m)
        * (sortedConst β a (toNatFun (k ∘ σ) 1) (toNatFun (h ∘ σ) 0) r p
            / (2 ^ m * (m.factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  have hk' := toNatFun_pos (k ∘ σ) (fun i => hk (σ i))
  refine (iterChartGen_sorted_isEquivalent β a b _ _ hβ hb hk' r m p hsort hp hlt).congr_left
    (Filter.Eventually.of_forall fun n => ?_)
  beta_reduce
  rw [← boxIntegralFin_perm β a b _ k h σ, boxIntegralFin_eq_toNatFun, boxIntegral_eq_iterChartGen]

end Laplace.Grammar
