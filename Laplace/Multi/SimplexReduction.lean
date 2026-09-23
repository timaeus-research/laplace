/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The simplex reduction

For measurable `G ≥ 0` on `ℝ`,
`∫⁻_{(0,∞)^{k+1}} G(∑ y_i) dy = ∫⁻_{(0,∞)} G(z) z^k/k! dz` (`lintegral_pi_Ioi_comp_sum`): the
Lebesgue measure of the simplex `{y ≥ 0 : ∑ y = z}` is `z^k/k!`. Proof by induction on `k` through
the coordinate splitting, with the power-convolution step
`∫⁻_{y>0} ∫⁻_{z>0} G(y+z) z^k/k! = ∫⁻_{w>0} G(w) w^{k+1}/(k+1)!` (`lintegral_conv_pow`):
translate the inner variable, swap the order over `{0 < z < w}`, and integrate the power.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- `∫⁻_{(0,w)} z^k/k! = w^{k+1}/(k+1)!` for `0 < w`. -/
theorem lintegral_Ioo_pow_div_factorial {w : ℝ} (hw : 0 < w) (k : ℕ) :
    ∫⁻ z in Ioo 0 w, ENNReal.ofReal (z ^ k / k.factorial) =
      ENNReal.ofReal (w ^ (k + 1) / (k + 1).factorial) := by
  have hint : IntegrableOn (fun z : ℝ ↦ z ^ k / k.factorial) (Ioo 0 w) :=
    ((continuous_pow k).div_const _).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 w)] fun z : ℝ ↦ z ^ k / k.factorial := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun z hz ↦ ?_
    have := hz.1
    change (0 : ℝ) ≤ z ^ k / k.factorial
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hw.le, intervalIntegral.integral_div, integral_pow,
    zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

/-- Translation of the inner variable: `∫⁻_{y>0} G(y + z) = ∫⁻_{w>z} G w`. -/
theorem lintegral_Ioi_comp_add (G : ℝ → ℝ≥0∞) (z : ℝ) :
    ∫⁻ y in Ioi 0, G (y + z) = ∫⁻ w in Ioi z, G w := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self (fun w ↦ (Ioi z).indicator G w) z]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : 0 < y
  · rw [indicator_of_mem (mem_Ioi.mpr hy), indicator_of_mem (show y + z ∈ Ioi z from
      lt_add_of_pos_left z hy)]
  · rw [indicator_of_notMem (show y ∉ Ioi 0 from hy), indicator_of_notMem
      (show y + z ∉ Ioi z from fun h ↦ hy ((lt_add_iff_pos_left z).mp h))]

/-- The power-convolution step. -/
theorem lintegral_conv_pow (G : ℝ → ℝ≥0∞) (hG : Measurable G) (k : ℕ) :
    ∫⁻ y in Ioi 0, ∫⁻ z in Ioi 0, G (y + z) * ENNReal.ofReal (z ^ k / k.factorial) =
      ∫⁻ w in Ioi 0, G w * ENNReal.ofReal (w ^ (k + 1) / (k + 1).factorial) := by
  -- swap the two half-line integrals
  have hF : Measurable (Function.uncurry fun (y z : ℝ) ↦
      G (y + z) * ENNReal.ofReal (z ^ k / k.factorial)) :=
    (hG.comp (measurable_fst.add measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const k).div_const _))
  rw [lintegral_lintegral_swap (f := fun y z ↦ G (y + z) * ENNReal.ofReal (z ^ k / k.factorial))
    hF.aemeasurable]
  -- translate the inner variable
  have h1 : ∀ z : ℝ, ∫⁻ y in Ioi 0, G (y + z) * ENNReal.ofReal (z ^ k / k.factorial) =
      ∫⁻ w in Ioi z, G w * ENNReal.ofReal (z ^ k / k.factorial) := by
    intro z
    have hm : Measurable fun y : ℝ ↦ G (y + z) := hG.comp (measurable_add_const z)
    rw [lintegral_mul_const _ hm, lintegral_Ioi_comp_add, lintegral_mul_const _ hG]
  simp_rw [h1]
  -- the kernel on the region `0 < z < w`
  set K : ℝ → ℝ → ℝ≥0∞ := fun z w ↦
    if 0 < z ∧ z < w then G w * ENNReal.ofReal (z ^ k / k.factorial) else 0 with hK
  have hKm : Measurable (Function.uncurry K) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd)
    · exact (hG.comp measurable_snd).mul
        (ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const k).div_const _))
  have h2 : ∫⁻ z in Ioi 0, ∫⁻ w in Ioi z, G w * ENNReal.ofReal (z ^ k / k.factorial) =
      ∫⁻ z, ∫⁻ w, K z w := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : 0 < z
    · rw [indicator_of_mem (mem_Ioi.mpr hz), ← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun w ↦ ?_
      by_cases hw : z < w
      · rw [indicator_of_mem (mem_Ioi.mpr hw), hK]
        simp only [hz, hw, and_self, if_true]
      · rw [indicator_of_notMem (show w ∉ Ioi z from hw), hK]
        simp only [hz, hw, and_false, if_false]
    · rw [indicator_of_notMem (show z ∉ Ioi 0 from hz), hK]
      simp only [hz, false_and, if_false, lintegral_zero]
  have h3 : ∀ w : ℝ, ∫⁻ z, K z w =
      (Ioi 0).indicator (fun w ↦ G w * ENNReal.ofReal (w ^ (k + 1) / (k + 1).factorial)) w := by
    intro w
    by_cases hw : 0 < w
    · have hm2 : Measurable fun z : ℝ ↦ ENNReal.ofReal (z ^ k / k.factorial) :=
        ENNReal.measurable_ofReal.comp ((measurable_id.pow_const k).div_const _)
      rw [indicator_of_mem (mem_Ioi.mpr hw), ← lintegral_Ioo_pow_div_factorial hw,
        ← lintegral_const_mul _ hm2, ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun z ↦ ?_
      by_cases hz : z ∈ Ioo 0 w
      · rw [indicator_of_mem hz, hK]
        simp only [hz.1, hz.2, and_self, if_true]
      · rw [indicator_of_notMem hz, hK]
        have : ¬ (0 < z ∧ z < w) := hz
        simp only [this, if_false]
    · rw [indicator_of_notMem (show w ∉ Ioi 0 from hw)]
      have : ∀ z, K z w = 0 := fun z ↦ by
        rw [hK]
        have : ¬ (0 < z ∧ z < w) := fun h ↦ hw (h.1.trans h.2)
        simp only [this, if_false]
      simp only [this, lintegral_zero]
  rw [h2, lintegral_lintegral_swap hKm.aemeasurable]
  simp_rw [h3]
  rw [lintegral_indicator measurableSet_Ioi]

/-- **The simplex reduction.** -/
theorem lintegral_pi_Ioi_comp_sum (G : ℝ → ℝ≥0∞) (hG : Measurable G) (k : ℕ) :
    ∫⁻ y in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)), G (∑ i, y i) =
      ∫⁻ z in Ioi 0, G z * ENNReal.ofReal (z ^ k / k.factorial) := by
  induction k generalizing G with
  | zero =>
    have hmp := volume_preserving_funUnique (Fin 1) ℝ
    have hset : Set.pi Set.univ (fun _ : Fin 1 ↦ Ioi (0 : ℝ)) =
        (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioi 0 := by
      ext y
      constructor
      · intro h
        exact h default (mem_univ _)
      · intro h i _
        rw [Subsingleton.elim i default]
        exact h
    have := (hmp.restrict_preimage (measurableSet_Ioi (a := (0 : ℝ)))).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding G
    rw [hset]
    simp only [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, mul_one]
    rw [← this]
    refine lintegral_congr fun y ↦ ?_
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  | succ k ih =>
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0
    have hT : MeasurableSet (Ioi (0 : ℝ) ×ˢ Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ))) :=
      measurableSet_Ioi.prod (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    have hset : Set.pi Set.univ (fun _ : Fin (k + 2) ↦ Ioi (0 : ℝ)) =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0) ⁻¹'
          (Ioi 0 ×ˢ Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ))) := by
      ext y
      constructor
      · intro h
        exact ⟨h 0 (mem_univ _), fun j _ ↦ h (Fin.succAbove 0 j) (mem_univ _)⟩
      · rintro ⟨h0, h'⟩ i _
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact h0
        · exact h' j (mem_univ _)
    have hsum : ∀ y : Fin (k + 2) → ℝ, ∑ i, y i =
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0) y).1 +
          ∑ j, ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0) y).2 j := by
      intro y
      rw [Fin.sum_univ_succ]
      rfl
    have hmeas : Measurable fun p : ℝ × (Fin (k + 1) → ℝ) ↦ G (p.1 + ∑ j, p.2 j) :=
      hG.comp (measurable_fst.add (Finset.measurable_sum _ fun j _ ↦
        (measurable_pi_apply j).comp measurable_snd))
    have := (hmp.restrict_preimage hT).lintegral_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0).measurableEmbedding
      (fun p : ℝ × (Fin (k + 1) → ℝ) ↦ G (p.1 + ∑ j, p.2 j))
    simp_rw [hsum, hset]
    rw [this, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
    have hin : ∀ y₀ : ℝ, ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
        G (y₀ + ∑ j, y' j) = ∫⁻ z in Ioi 0, G (y₀ + z) * ENNReal.ofReal (z ^ k / k.factorial) :=
      fun y₀ ↦ ih (fun s ↦ G (y₀ + s)) (hG.comp (measurable_const.add measurable_id))
    simp_rw [hin]
    exact lintegral_conv_pow G hG k

end Laplace.Multi
