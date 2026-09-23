/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSubstitution

/-!
# The logarithmic substitution on a tied block

For exponents `A_i > 0`, `h_i` with `(h_i + 1)/A_i = λ` for every `i` (a tied block) and measurable
`G ≥ 0`,
`∫⁻_{(0,1)^{k+1}} ∏ x_i^{h_i} · G(∏ x_i^{A_i}) dx
  = ∏ (1/A_i) · ∫⁻_{(0,∞)^{k+1}} e^{−λ ∑ y} G(e^{−∑ y}) dy`
(`lintegral_pi_Ioo_tied`): the coordinatewise substitution `x_i = e^{−y_i/A_i}` through the
coordinate splitting, by induction on the number of coordinates.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- A constant cube splits off its first coordinate. -/
theorem pi_const_eq_preimage {k : ℕ} (S : Set ℝ) :
    Set.pi Set.univ (fun _ : Fin (k + 2) ↦ S) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0) ⁻¹'
        (S ×ˢ Set.pi Set.univ (fun _ : Fin (k + 1) ↦ S)) := by
  ext y
  constructor
  · intro h
    exact ⟨h 0 (mem_univ _), fun j _ ↦ h (Fin.succAbove 0 j) (mem_univ _)⟩
  · rintro ⟨h0, h'⟩ i _
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h0
    · exact h' j (mem_univ _)

/-- **The logarithmic substitution on a tied block.** -/
theorem lintegral_pi_Ioo_tied (k : ℕ) :
    ∀ (A h : Fin (k + 1) → ℝ), (∀ i, 0 < A i) → ∀ lam : ℝ, (∀ i, (h i + 1) / A i = lam) →
    ∀ G : ℝ → ℝ≥0∞, Measurable G →
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        (∏ i, ENNReal.ofReal (x i ^ h i)) * G (∏ i, x i ^ A i) =
      (∏ i, ENNReal.ofReal (1 / A i)) *
        ∫⁻ y in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * ∑ i, y i))) * G (exp (-(∑ i, y i))) := by
  induction k with
  | zero =>
    intro A h hA lam hlam G hG
    have hmp := volume_preserving_funUnique (Fin 1) ℝ
    have hset : ∀ S : Set ℝ, Set.pi Set.univ (fun _ : Fin 1 ↦ S) =
        (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' S := by
      intro S
      ext y
      constructor
      · intro h'
        exact h' default (mem_univ _)
      · intro h' i _
        rw [Subsingleton.elim i default]
        exact h'
    have h1 := (hmp.restrict_preimage
      (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (fun x ↦ ENNReal.ofReal (x ^ h 0) * G (x ^ A 0))
    have h2 := (hmp.restrict_preimage (measurableSet_Ioi (a := (0 : ℝ)))).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (fun y ↦ ENNReal.ofReal (exp (-(lam * y))) * G (exp (-y)))
    have e1 : ∫⁻ x in Set.pi Set.univ (fun _ : Fin (0 + 1) ↦ Ioo (0 : ℝ) 1),
        (∏ i, ENNReal.ofReal (x i ^ h i)) * G (∏ i, x i ^ A i) =
        ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ h 0) * G (x ^ A 0) := by
      rw [hset, ← h1]
      refine lintegral_congr fun x ↦ ?_
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      rfl
    have e2 : ∫⁻ y in Set.pi Set.univ (fun _ : Fin (0 + 1) ↦ Ioi (0 : ℝ)),
        ENNReal.ofReal (exp (-(lam * ∑ i, y i))) * G (exp (-(∑ i, y i))) =
        ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(lam * y))) * G (exp (-y)) := by
      rw [hset, ← h2]
      refine lintegral_congr fun y ↦ ?_
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      rfl
    have hm : Measurable fun y : ℝ ↦ ENNReal.ofReal (exp (-(lam * y))) * G (exp (-y)) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id).neg.exp).mul
        (hG.comp measurable_neg.exp)
    rw [e1, e2, lintegral_Ioo_rpow_mul_comp_rpow (hA 0) (h 0) G, hlam 0,
      Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun y ↦ ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.mpr (hA 0)).le]
    congr 2
    ring
  | succ k ih =>
    intro A h hA lam hlam G hG
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0 with he
    have hmp : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) 0
    have hesymm : ∀ p : ℝ × (Fin (k + 1) → ℝ), e.symm p = Fin.insertNth 0 p.1 p.2 := fun p ↦ rfl
    -- the tied exponents of the remaining coordinates
    have hA' : ∀ j : Fin (k + 1), 0 < A (Fin.succ j) := fun j ↦ hA _
    have hlam' : ∀ j : Fin (k + 1), (h (Fin.succ j) + 1) / A (Fin.succ j) = lam := fun j ↦ hlam _
    -- split the cube integral
    have hTx : MeasurableSet
        (Ioo (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1)) :=
      measurableSet_Ioo.prod (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)
    have hTy : MeasurableSet (Ioi (0 : ℝ) ×ˢ Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ))) :=
      measurableSet_Ioi.prod (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    have hprod : ∀ (B : Fin (k + 2) → ℝ) (x : Fin (k + 2) → ℝ),
        ∏ i, x i ^ B i = (e x).1 ^ B 0 * ∏ j, (e x).2 j ^ B (Fin.succ j) := by
      intro B x
      rw [Fin.prod_univ_succ]
      rfl
    have hprodE : ∀ (B : Fin (k + 2) → ℝ) (x : Fin (k + 2) → ℝ),
        ∏ i, ENNReal.ofReal (x i ^ B i) =
          ENNReal.ofReal ((e x).1 ^ B 0) * ∏ j, ENNReal.ofReal ((e x).2 j ^ B (Fin.succ j)) := by
      intro B x
      rw [Fin.prod_univ_succ]
      rfl
    have hsum : ∀ y : Fin (k + 2) → ℝ, ∑ i, y i = (e y).1 + ∑ j, (e y).2 j := by
      intro y
      rw [Fin.sum_univ_succ]
      rfl
    -- measurability of the split integrands
    have hmx : Measurable fun p : ℝ × (Fin (k + 1) → ℝ) ↦
        ENNReal.ofReal (p.1 ^ h 0) * (∏ j, ENNReal.ofReal (p.2 j ^ h (Fin.succ j))) *
          G (p.1 ^ A 0 * ∏ j, p.2 j ^ A (Fin.succ j)) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (hG.comp (Measurable.mul ?_ ?_))
      · exact ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
      · exact Finset.measurable_prod _ fun j _ ↦
          ENNReal.measurable_ofReal.comp (((measurable_pi_apply j).comp measurable_snd).pow_const _)
      · exact measurable_fst.pow_const _
      · exact Finset.measurable_prod _ fun j _ ↦
          ((measurable_pi_apply j).comp measurable_snd).pow_const _
    have hmy : Measurable fun p : ℝ × (Fin (k + 1) → ℝ) ↦
        ENNReal.ofReal (exp (-(lam * (p.1 + ∑ j, p.2 j)))) * G (exp (-(p.1 + ∑ j, p.2 j))) := by
      have hs : Measurable fun p : ℝ × (Fin (k + 1) → ℝ) ↦ p.1 + ∑ j, p.2 j :=
        measurable_fst.add (Finset.measurable_sum _ fun j _ ↦
          (measurable_pi_apply j).comp measurable_snd)
      exact (ENNReal.measurable_ofReal.comp (measurable_const.mul hs).neg.exp).mul
        (hG.comp hs.neg.exp)
    -- left side
    have hL := (hmp.restrict_preimage hTx).lintegral_comp_emb e.measurableEmbedding
      (fun p : ℝ × (Fin (k + 1) → ℝ) ↦ ENNReal.ofReal (p.1 ^ h 0) *
        (∏ j, ENNReal.ofReal (p.2 j ^ h (Fin.succ j))) *
          G (p.1 ^ A 0 * ∏ j, p.2 j ^ A (Fin.succ j)))
    have hR := (hmp.restrict_preimage hTy).lintegral_comp_emb e.measurableEmbedding
      (fun p : ℝ × (Fin (k + 1) → ℝ) ↦ ENNReal.ofReal (exp (-(lam * (p.1 + ∑ j, p.2 j)))) *
        G (exp (-(p.1 + ∑ j, p.2 j))))
    simp_rw [hprodE, hprod, hsum]
    rw [pi_const_eq_preimage, pi_const_eq_preimage, ← he, hL, hR, Measure.volume_eq_prod,
      ← Measure.prod_restrict, ← Measure.prod_restrict, lintegral_prod _ hmx.aemeasurable,
      lintegral_prod _ hmy.aemeasurable]
    -- inner integrals: the induction hypothesis on the remaining coordinates
    have hin : ∀ x₀ : ℝ, ∫⁻ x' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        ENNReal.ofReal (x₀ ^ h 0) * (∏ j, ENNReal.ofReal (x' j ^ h (Fin.succ j))) *
          G (x₀ ^ A 0 * ∏ j, x' j ^ A (Fin.succ j)) =
        ENNReal.ofReal (x₀ ^ h 0) * ((∏ j, ENNReal.ofReal (1 / A (Fin.succ j))) *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
            ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (x₀ ^ A 0 * exp (-(∑ j, y' j)))) := by
      intro x₀
      have hG' : Measurable fun c ↦ G (x₀ ^ A 0 * c) := hG.comp (measurable_const.mul measurable_id)
      have hm' : Measurable fun x' : Fin (k + 1) → ℝ ↦
          (∏ j, ENNReal.ofReal (x' j ^ h (Fin.succ j))) *
            G (x₀ ^ A 0 * ∏ j, x' j ^ A (Fin.succ j)) :=
        (Finset.measurable_prod _ fun j _ ↦
          ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).pow_const _)).mul
          (hG'.comp (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _))
      rw [← ih (fun j ↦ A (Fin.succ j)) (fun j ↦ h (Fin.succ j)) hA' lam hlam' _ hG',
        ← lintegral_const_mul _ hm']
      refine lintegral_congr fun x' ↦ ?_
      ring
    simp_rw [hin]
    -- the first coordinate: the one-dimensional substitution
    set P' : ℝ≥0∞ := ∏ j, ENNReal.ofReal (1 / A (Fin.succ j)) with hP'
    have hs' : Measurable fun p : ℝ × (Fin (k + 1) → ℝ) ↦ ∑ j, p.2 j :=
      Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_snd
    have hF : Measurable (Function.uncurry fun (c : ℝ) (y' : Fin (k + 1) → ℝ) ↦
        ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (c * exp (-(∑ j, y' j)))) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hs').neg.exp).mul
        (hG.comp (measurable_fst.mul hs'.neg.exp))
    have hsub : ∫⁻ x₀ in Ioo (0 : ℝ) 1, ENNReal.ofReal (x₀ ^ h 0) * (P' *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (x₀ ^ A 0 * exp (-(∑ j, y' j)))) =
        ∫⁻ y₀ in Ioi (0 : ℝ), ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * y₀)) / A 0) * (P' *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
            ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (exp (-y₀) * exp (-(∑ j, y' j)))) :=
      lintegral_Ioo_rpow_mul_comp_rpow (hA 0) (h 0) (fun c ↦ P' *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (c * exp (-(∑ j, y' j))))
    have hmy₀ : Measurable fun y₀ : ℝ ↦
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (exp (-y₀) * exp (-(∑ j, y' j))) :=
      hF.lintegral_prod_right'.comp measurable_neg.exp
    have hmy₀' : Measurable fun y₀ : ℝ ↦
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * (y₀ + ∑ j, y' j)))) * G (exp (-(y₀ + ∑ j, y' j))) :=
      hmy.lintegral_prod_right'
    have hmy₀'' : Measurable fun y₀ : ℝ ↦ P' *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
          ENNReal.ofReal (exp (-(lam * (y₀ + ∑ j, y' j)))) * G (exp (-(y₀ + ∑ j, y' j))) :=
      measurable_const.mul hmy₀'
    rw [hsub, hlam 0, Fin.prod_univ_succ, ← hP', mul_assoc, ← lintegral_const_mul _ hmy₀',
      ← lintegral_const_mul _ hmy₀'']
    refine lintegral_congr fun y₀ ↦ ?_
    have hinner : ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
        ENNReal.ofReal (exp (-(lam * (y₀ + ∑ j, y' j)))) * G (exp (-(y₀ + ∑ j, y' j))) =
        ENNReal.ofReal (exp (-(lam * y₀))) *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioi (0 : ℝ)),
            ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (exp (-y₀) * exp (-(∑ j, y' j))) := by
      have hm'' : Measurable fun y' : Fin (k + 1) → ℝ ↦
          ENNReal.ofReal (exp (-(lam * ∑ j, y' j))) * G (exp (-y₀) * exp (-(∑ j, y' j))) :=
        hF.of_uncurry_left
      rw [← lintegral_const_mul _ hm'']
      refine lintegral_congr fun y' ↦ ?_
      have e1 : exp (-(lam * (y₀ + ∑ j, y' j))) = exp (-(lam * y₀)) * exp (-(lam * ∑ j, y' j)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : exp (-(y₀ + ∑ j, y' j)) = exp (-y₀) * exp (-(∑ j, y' j)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e1, e2, ENNReal.ofReal_mul (exp_pos _).le, mul_assoc]
    have e3 : exp (-(lam * y₀)) / A 0 = 1 / A 0 * exp (-(lam * y₀)) := by ring
    rw [hinner, e3, ENNReal.ofReal_mul (one_div_pos.mpr (hA 0)).le]
    ring

end Laplace.Multi
