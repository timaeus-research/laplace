/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IterChartExpansion

/-!
# The chart integral as a genuine `d`-dimensional integral (grammar §4.2)

The recursive `iterChartGen` of unit 50 integrates the coordinates one at a time. The paper writes
the standard integral over the box `(0, b]^d ⊆ ℝ^d`. This unit identifies the two:

  `∫_{(0,b]^d} ∏ u_i^{h_i} · f(c ∏ u_i^{k_i}) du = iterChartGen β a b k h d c`,

with the left side a Bochner integral on `Fin d → ℝ` against the product of the restricted Lebesgue
measures. The proof is an induction on `d`, splitting off the last coordinate with
`measurePreserving_piFinSuccAbove` and Fubini on the compact box. Consequently every asymptotic and
expansion proved for `iterChartGen` (units 50, 52, 53) holds verbatim for the box integral.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The product of the restricted Lebesgue measures on `Fin d → ℝ`, i.e. Lebesgue measure on the
box `(0, b]^d`. -/
noncomputable def boxMeasure (b : ℝ) (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 b)

/-- The `d`-dimensional chart standard integral in paper form. -/
noncomputable def boxIntegral (β a b c : ℝ) (k h : ℕ → ℕ) (d : ℕ) : ℝ :=
  ∫ u : Fin d → ℝ, (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i) ∂(boxMeasure b d)

theorem boxMeasure_eq_restrict (b : ℝ) (d : ℕ) :
    boxMeasure b d = (volume : Measure (Fin d → ℝ)).restrict (Set.pi univ fun _ => Ioc 0 b) := by
  rw [boxMeasure, ← Measure.restrict_pi_pi]
  rfl

instance boxMeasure_isFiniteMeasure (b : ℝ) (d : ℕ) : IsFiniteMeasure (boxMeasure b d) := by
  unfold boxMeasure
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc 0 b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  infer_instance

/-- **Box integral = iterated chart integral.** -/
theorem boxIntegral_eq_iterChartGen (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (c : ℝ) :
    boxIntegral β a b c k h d = iterChartGen β a b k h d c := by
  induction d generalizing c with
  | zero =>
    rw [boxIntegral, boxMeasure,
      Measure.pi_of_empty (fun _ => (volume : Measure ℝ).restrict (Ioc 0 b)), integral_dirac,
      iterChartGen_zero]
    simp
  | succ d ih =>
    rw [boxIntegral, boxMeasure, iterChartGen_succ]
    -- split off the last coordinate
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (d + 1) => (volume : Measure ℝ).restrict (Ioc 0 b)) (Fin.last d)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d) with he
    set g : ℝ × (Fin d → ℝ) → ℝ := fun y =>
      ((∏ j : Fin d, y.2 j ^ h j) * y.1 ^ h d)
        * quadKernel β a (c * ((∏ j : Fin d, y.2 j ^ k j) * y.1 ^ k d)) with hg
    have hcomp : ∀ u : Fin (d + 1) → ℝ,
        (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i) = g (e u) := by
      intro u
      have h1 : (e u).1 = u (Fin.last d) := rfl
      have h2 : ∀ j, (e u).2 j = u (Fin.castSucc j) := fun j => by
        rw [← Fin.succAbove_last_apply j]; rfl
      simp only [hg]
      rw [Fin.prod_univ_castSucc (fun i : Fin (d + 1) => u i ^ h i),
        Fin.prod_univ_castSucc (fun i : Fin (d + 1) => u i ^ k i)]
      simp only [h1, h2, Fin.val_castSucc, Fin.val_last]
    have hint : Integrable g (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))) := by
      have hpoly : Continuous fun y : ℝ × (Fin d → ℝ) => (∏ j, y.2 j ^ h j) * y.1 ^ h d :=
        (continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_snd).pow _).mul
          (continuous_fst.pow _)
      have hpoly2 : Continuous fun y : ℝ × (Fin d → ℝ) => c * ((∏ j, y.2 j ^ k j) * y.1 ^ k d) :=
        continuous_const.mul
          ((continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_snd).pow _).mul
            (continuous_fst.pow _))
      have hcont : Continuous g := hpoly.mul ((quadKernel_continuous β a).comp hpoly2)
      have hcpt : IsCompact (Icc (0 : ℝ) b ×ˢ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b) :=
        isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
      have h1 := hcont.continuousOn.integrableOn_compact (μ := volume) hcpt
      have h2 : IntegrableOn g (Ioc (0 : ℝ) b ×ˢ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b) :=
        h1.mono_set (prod_mono Ioc_subset_Icc_self (pi_mono fun _ _ => Ioc_subset_Icc_self))
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h2
      change Integrable g (((volume : Measure ℝ).restrict (Ioc 0 b)).prod
        ((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict
          (Set.pi univ fun _ => Ioc (0 : ℝ) b))) at h2
      rw [Measure.restrict_pi_pi] at h2
      exact h2
    calc (∫ u : Fin (d + 1) → ℝ, (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i)
          ∂(Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 b)))
        = ∫ u, g (e u) ∂(Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 b)) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hcomp)
      _ = ∫ y, g y ∂(((volume : Measure ℝ).restrict (Ioc 0 b)).prod
            (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))) :=
          hmp.integral_comp' g
      _ = ∫ t in Ioc (0 : ℝ) b, ∫ v, g (t, v)
            ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b)) :=
          integral_prod g hint
      _ = ∫ t in Ioc (0 : ℝ) b, t ^ h d * iterChartGen β a b k h d (c * t ^ k d) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
          rw [← ih (c * t ^ k d), boxIntegral, boxMeasure, ← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [hg]
          rw [show c * ((∏ j : Fin d, v j ^ k j) * t ^ k d) = c * t ^ k d * ∏ j : Fin d, v j ^ k j
            by ring]
          ring

/-- **Multiplicity theorem in paper form, all exponents equal**: the box integral over `(0,b]^{d+2}`
satisfies `∫ ~ (∏ k_i^{-1}) A_{p-1}/(2^{d+1}(d+1)!) n^{-p/2} (log n)^{d+1}`. -/
theorem boxIntegral_isEquivalent (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d + 1 → ((h i : ℝ) + 1) / k i = p) :
    (fun n : ℝ => boxIntegral β a b (Real.sqrt n) k h (d + 2)) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (d + 2), (1 : ℝ) / k i)
        * (weightedMass β a (p - 1) / (2 ^ (d + 1) * ((d + 1).factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ (d + 1)) := by
  refine (iterChartGen_isEquivalent β a b k h p hβ hb hk d hp).congr_left
    (Filter.Eventually.of_forall fun n => ?_)
  exact (boxIntegral_eq_iterChartGen β a b k h (d + 2) (Real.sqrt n)).symm

/-- **Mixed multiplicity theorem in paper form.** -/
theorem boxIntegral_mixed_isEquivalent (β a b : ℝ) (k h : ℕ → ℕ) (p q : ℝ) (hβ : 0 < β)
    (hb : 0 < b) (hk : ∀ i, 0 < k i) (hq : ((h 0 : ℝ) + 1) / k 0 = q) (m : ℕ) (hm : 0 < m)
    (hp : ∀ i, 1 ≤ i → i ≤ m + 1 → ((h i : ℝ) + 1) / k i = p) (hlt : p < q) :
    (fun n : ℝ => boxIntegral β a b (Real.sqrt n) k h (m + 2)) ~[atTop]
      fun n : ℝ => (∏ i ∈ Finset.range (m + 2), (1 : ℝ) / k i) * b ^ ((k 0 : ℝ) * (q - p))
        * (noLogConst β a p q / (2 ^ m * (m.factorial : ℝ)))
        * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  refine (iterChartGen_mixed_isEquivalent β a b k h p q hβ hb hk hq m hm hp hlt).congr_left
    (Filter.Eventually.of_forall fun n => ?_)
  exact (boxIntegral_eq_iterChartGen β a b k h (m + 2) (Real.sqrt n)).symm

end Laplace.Grammar
