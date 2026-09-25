/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthExample
import Laplace.Multi.ActiveTruthSpectator
import Laplace.Multi.DegenerateFace

/-!
# The three-coordinate example is an instance of the face theorem

Astra round 11, item (d): the model kernel of `ActiveTruthExample.lean` on `Fin 1 ⊕ Fin 2` is
the by-hand integral `I(t)` of `DegenerateFace.lean` (`modelKernel_degExample_eq`), so the
by-hand asymptotic `t⁴ I(t)/log t → 1` is recovered from the general face theorem
(`tendsto_degI_of_face`), a regression test connecting the abstract theorem to the motivating
example. The identification is Fubini bookkeeping: the `Fin 1 ⊕ Fin 2` integral splits along the
sum, the `Fin 1` and `Fin 2` factors become `ℝ` and `ℝ × ℝ`, the box indicators become the
`(0,1)` set integrals, and the cut `t^{-2}(xyz)^{-1} < 1` is `xyz > t^{-2}`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

theorem lintegral_indicator_one_mul {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * f x = ∫⁻ x in s, f x := by
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- The cut of the example: `t^{-2}(xyz)^{-1} < 1 ↔ xyz > t^{-2}`. -/
theorem deg_cutVar_lt_iff {t : ℝ} {x : Fin 1 ⊕ Fin 2 → ℝ} (hx : ∀ j, 0 < x j) :
    cutVar 1 2 1 degQ t x < 1 ↔
      t ^ (-2 : ℝ) < x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1) := by
  have hpos : 0 < x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1) :=
    mul_pos (mul_pos (hx _) (hx _)) (hx _)
  have e : cutVar 1 2 1 degQ t x =
      t ^ (-2 : ℝ) / (x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1)) := by
    unfold cutVar
    rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
    simp only [degQ, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      div_one, Real.rpow_neg_one, one_mul, Matrix.cons_val_fin_one]
    norm_num
    rw [div_eq_mul_inv, mul_inv, mul_inv]
    ring
  rw [e, div_lt_one hpos]

/-- The integrand of the example, pointwise: the three box indicators times `degIntegrand`. -/
theorem degIntegrand_eq (t : ℝ) (x : Fin 1 ⊕ Fin 2 → ℝ) :
    ENNReal.ofReal (modelIntegrand 1 1 1 2 1 3 degQ degκ degr (fun _ _ ↦ 1) (fun _ _ ↦ 1) t x) =
      (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (x (Sum.inr 1)) *
        ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (x (Sum.inr 0)) *
          ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (x (Sum.inl 0)) *
            degIntegrand t (x (Sum.inl 0)) (x (Sum.inr 0)) (x (Sum.inr 1)))) := by
  by_cases hbox : x ∈ Set.pi univ (fun _ : Fin 1 ⊕ Fin 2 ↦ Ioo (0 : ℝ) 1)
  · have hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1 := Set.mem_univ_pi.mp hbox
    have hx0 : ∀ j, 0 < x j := fun j ↦ (hx j).1
    rw [Set.indicator_of_mem (hx _), Set.indicator_of_mem (hx _), Set.indicator_of_mem (hx _),
      one_mul, one_mul, one_mul]
    unfold modelIntegrand degIntegrand
    have hprod_r : ∏ j, x j ^ degr j = x (Sum.inr 1) ^ 2 := by
      rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
      simp [degr]
    have hprod_κ : ∏ j, x j ^ degκ j = x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1) ^ 2 := by
      rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
      simp [degκ]
      ring
    have ht3 : t ^ (3 : ℝ) = t ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    by_cases hcut : cutVar 1 2 1 degQ t x < 1
    · have hmem : x ∈ modelDomain 1 1 2 1 degQ t := ⟨hbox, hcut⟩
      have hmemI : x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1) ∈ Ioi (t ^ (-2 : ℝ)) :=
        (deg_cutVar_lt_iff hx0).mp hcut
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemI, hprod_r, hprod_κ, ht3]
      beta_reduce
      congr 1
      ring_nf
    · have hmem : x ∉ modelDomain 1 1 2 1 degQ t := fun h ↦ hcut h.2
      have hmemI : x (Sum.inl 0) * x (Sum.inr 0) * x (Sum.inr 1) ∉ Ioi (t ^ (-2 : ℝ)) :=
        fun h ↦ hcut ((deg_cutVar_lt_iff hx0).mpr h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmemI, zero_mul]
  · have hmem : x ∉ modelDomain 1 1 2 1 degQ t := fun h ↦ hbox h.1
    unfold modelIntegrand
    rw [Set.indicator_of_notMem hmem, ENNReal.ofReal_zero]
    by_cases h1 : x (Sum.inl 0) ∈ Ioo (0 : ℝ) 1
    · by_cases h2 : x (Sum.inr 0) ∈ Ioo (0 : ℝ) 1
      · by_cases h3 : x (Sum.inr 1) ∈ Ioo (0 : ℝ) 1
        · exact absurd (Set.mem_univ_pi.mpr (Sum.forall.mpr
            ⟨Fin.forall_fin_one.mpr h1, Fin.forall_fin_two.mpr ⟨h2, h3⟩⟩)) hbox
        · rw [Set.indicator_of_notMem h3, zero_mul]
      · rw [Set.indicator_of_notMem h2, zero_mul, mul_zero]
    · rw [Set.indicator_of_notMem h1, zero_mul, mul_zero, mul_zero]

/-- The example's model integral, iterated: it is `degI t`. -/
theorem lintegral_degExample (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (modelIntegrand 1 1 1 2 1 3 degQ degκ degr (fun _ _ ↦ 1)
      (fun _ _ ↦ 1) t x) = degI t := by
  have hF : Measurable fun x : Fin 1 ⊕ Fin 2 → ℝ ↦ ENNReal.ofReal
      (modelIntegrand 1 1 1 2 1 3 degQ degκ degr (fun _ _ ↦ 1) (fun _ _ ↦ 1) t x) :=
    ENNReal.measurable_ofReal.comp (measurable_modelIntegrand
      (W := fun _ _ ↦ (1 : ℝ)) (a := fun _ _ ↦ (1 : ℝ)) measurable_const measurable_const t)
  rw [lintegral_sum_split hF]
  simp_rw [degIntegrand_eq t, Sum.elim_inl, Sum.elim_inr]
  set G : ℝ → ℝ → ℝ → ℝ≥0∞ := fun a b c ↦ (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) c *
    ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) b *
      ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) a * degIntegrand t a b c)) with hG
  have hGm : Measurable fun p : ℝ × (ℝ × ℝ) ↦ G p.1 p.2.1 p.2.2 := by
    rw [hG]
    have hI : Measurable fun p : ℝ × (ℝ × ℝ) ↦ degIntegrand t p.1 p.2.1 p.2.2 := by
      unfold degIntegrand
      have hz : Measurable fun p : ℝ × (ℝ × ℝ) ↦ p.2.2 := measurable_snd.comp measurable_snd
      have hy : Measurable fun p : ℝ × (ℝ × ℝ) ↦ p.2.1 := measurable_fst.comp measurable_snd
      have hm3 : Measurable fun p : ℝ × (ℝ × ℝ) ↦ p.1 * p.2.1 * p.2.2 :=
        (measurable_fst.mul hy).mul hz
      refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
      · exact (measurable_const.indicator measurableSet_Ioi).comp hm3
      · exact (hz.pow_const 2).mul (Real.measurable_exp.comp
          (measurable_const.mul ((measurable_fst.mul hy).mul (hz.pow_const 2))).neg)
    have hind : Measurable ((Ioo (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ≥0∞)) :=
      measurable_const.indicator measurableSet_Ioo
    exact (hind.comp (measurable_snd.comp measurable_snd)).mul
      ((hind.comp (measurable_fst.comp measurable_snd)).mul ((hind.comp measurable_fst).mul hI))
  have e1 : ∀ a : ℝ, ∫⁻ y : Fin 2 → ℝ, G a (y 0) (y 1) = ∫⁻ q : ℝ × ℝ, G a q.1 q.2 := by
    intro a
    rw [← (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun q : ℝ × ℝ ↦ G a q.1 q.2)]
    rfl
  have e2 : ∫⁻ x' : Fin 1 → ℝ, ∫⁻ y : Fin 2 → ℝ, G (x' 0) (y 0) (y 1) =
      ∫⁻ a : ℝ, ∫⁻ q : ℝ × ℝ, G a q.1 q.2 := by
    simp_rw [e1]
    rw [← (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun a : ℝ ↦ ∫⁻ q : ℝ × ℝ, G a q.1 q.2)]
    rfl
  change ∫⁻ x' : Fin 1 → ℝ, ∫⁻ y : Fin 2 → ℝ, G (x' 0) (y 0) (y 1) = degI t
  rw [e2, lintegral_lintegral_swap (f := fun a (q : ℝ × ℝ) ↦ G a q.1 q.2) hGm.aemeasurable,
    Measure.volume_eq_prod ℝ ℝ, lintegral_prod_symm' (fun q : ℝ × ℝ ↦ ∫⁻ a, G a q.1 q.2)
      hGm.lintegral_prod_left']
  unfold degI
  simp only [hG]
  have hne : ∀ x : ℝ, (Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≠ ⊤ := fun x ↦ by
    by_cases h : x ∈ Ioo (0 : ℝ) 1 <;> simp [h]
  simp_rw [lintegral_const_mul' _ _ (hne _), lintegral_indicator_one_mul measurableSet_Ioo]

/-- **The example's model kernel is `I(t)`.** -/
theorem modelKernel_degExample_eq (t : ℝ) :
    modelKernel 1 1 1 1 2 0 1 3 degQ degκ degr (fun _ _ ↦ 1) (fun _ _ ↦ 1) t = (degI t).toReal := by
  rw [modelKernel_const_eq_toReal, lintegral_degExample]
  simp [Real.rpow_zero]

/-- **The by-hand asymptotic recovered from the face theorem**: `t⁴ I(t)/log t → 1`. -/
theorem tendsto_degI_of_face : Tendsto (fun t ↦ t ^ 4 / log t * (degI t).toReal) atTop (𝓝 1) := by
  refine tendsto_modelKernel_degExample.congr' (Eventually.of_forall fun t ↦ ?_)
  rw [modelKernel_degExample_eq]

end Laplace.Multi
