/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSubstitution

/-!
# The logarithmic substitution on a block (general exponents)

For exponents `A_j > 0`, arbitrary `h_j`, and measurable `G ≥ 0`,
`∫⁻_{(0,1)^m} ∏ x_j^{h_j} · G(∏ x_j^{A_j}) dx
  = ∏ (1/A_j) · ∫⁻_{(0,∞)^m} ∏ e^{−(h_j+1)/A_j · y_j} G(e^{−∑ y}) dy`
(`lintegral_pi_Ioo_log`), including the empty block `m = 0`. This is the untied version of
`lintegral_pi_Ioo_tied`, needed for the untied coordinates of the single-monomial power–log theorem.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- A constant cube splits off its first coordinate (any dimension `≥ 1`). -/
theorem pi_const_eq_preimage' {m : ℕ} (S : Set ℝ) :
    Set.pi Set.univ (fun _ : Fin (m + 1) ↦ S) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0) ⁻¹'
        (S ×ˢ Set.pi Set.univ (fun _ : Fin m ↦ S)) := by
  ext y
  constructor
  · intro h
    exact ⟨h 0 (mem_univ _), fun j _ ↦ h (Fin.succAbove 0 j) (mem_univ _)⟩
  · rintro ⟨h0, h'⟩ i _
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact h0
    · exact h' j (mem_univ _)

/-- **The logarithmic substitution on a block.** -/
theorem lintegral_pi_Ioo_log (m : ℕ) :
    ∀ (A h : Fin m → ℝ), (∀ j, 0 < A j) → ∀ G : ℝ → ℝ≥0∞, Measurable G →
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin m ↦ Ioo (0 : ℝ) 1),
        (∏ j, ENNReal.ofReal (x j ^ h j)) * G (∏ j, x j ^ A j) =
      (∏ j, ENNReal.ofReal (1 / A j)) *
        ∫⁻ y in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h j + 1) / A j * y j)))) * G (exp (-(∑ j, y j))) := by
  induction m with
  | zero =>
    intro A h hA G hG
    have hpi : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default := by
      rw [volume_pi, Measure.pi_of_empty (x := default)]
    have huniv : ∀ S : Set ℝ, Set.pi Set.univ (fun _ : Fin 0 ↦ S) = Set.univ := by
      intro S
      ext y
      simp only [mem_univ, iff_true]
      intro i
      exact i.elim0
    rw [huniv, huniv, Measure.restrict_univ, hpi, lintegral_dirac, lintegral_dirac]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, one_mul, neg_zero,
      Real.exp_zero]
  | succ m ih =>
    intro A h hA G hG
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0 with he
    have hmp : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
    have hA' : ∀ j : Fin m, 0 < A (Fin.succ j) := fun j ↦ hA _
    have hTx : MeasurableSet
        (Ioo (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin m ↦ Ioo (0 : ℝ) 1)) :=
      measurableSet_Ioo.prod (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)
    have hTy : MeasurableSet (Ioi (0 : ℝ) ×ˢ Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ))) :=
      measurableSet_Ioi.prod (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi)
    have hprod : ∀ (B : Fin (m + 1) → ℝ) (x : Fin (m + 1) → ℝ),
        ∏ i, x i ^ B i = (e x).1 ^ B 0 * ∏ j, (e x).2 j ^ B (Fin.succ j) := by
      intro B x
      rw [Fin.prod_univ_succ]
      rfl
    have hprodE : ∀ (B : Fin (m + 1) → ℝ) (x : Fin (m + 1) → ℝ),
        ∏ i, ENNReal.ofReal (x i ^ B i) =
          ENNReal.ofReal ((e x).1 ^ B 0) * ∏ j, ENNReal.ofReal ((e x).2 j ^ B (Fin.succ j)) := by
      intro B x
      rw [Fin.prod_univ_succ]
      rfl
    have hsum : ∀ y : Fin (m + 1) → ℝ, ∑ i, y i = (e y).1 + ∑ j, (e y).2 j := by
      intro y
      rw [Fin.sum_univ_succ]
      rfl
    have hprodExp : ∀ y : Fin (m + 1) → ℝ,
        ∏ i, ENNReal.ofReal (exp (-((h i + 1) / A i * y i))) =
          ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * (e y).1))) *
            ∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * (e y).2 j))) := by
      intro y
      rw [Fin.prod_univ_succ]
      rfl
    have hmx : Measurable fun p : ℝ × (Fin m → ℝ) ↦
        ENNReal.ofReal (p.1 ^ h 0) * (∏ j, ENNReal.ofReal (p.2 j ^ h (Fin.succ j))) *
          G (p.1 ^ A 0 * ∏ j, p.2 j ^ A (Fin.succ j)) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (hG.comp (Measurable.mul ?_ ?_))
      · exact ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
      · exact Finset.measurable_prod _ fun j _ ↦
          ENNReal.measurable_ofReal.comp (((measurable_pi_apply j).comp measurable_snd).pow_const _)
      · exact measurable_fst.pow_const _
      · exact Finset.measurable_prod _ fun j _ ↦
          ((measurable_pi_apply j).comp measurable_snd).pow_const _
    have hs : Measurable fun p : ℝ × (Fin m → ℝ) ↦ p.1 + ∑ j, p.2 j :=
      measurable_fst.add (Finset.measurable_sum _ fun j _ ↦
        (measurable_pi_apply j).comp measurable_snd)
    have hmy : Measurable fun p : ℝ × (Fin m → ℝ) ↦
        ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * p.1))) *
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * p.2 j)))) *
            G (exp (-(p.1 + ∑ j, p.2 j))) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) (hG.comp hs.neg.exp)
      · exact ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_fst).neg.exp
      · exact Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
          (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)).neg.exp
    have hL := (hmp.restrict_preimage hTx).lintegral_comp_emb e.measurableEmbedding
      (fun p : ℝ × (Fin m → ℝ) ↦ ENNReal.ofReal (p.1 ^ h 0) *
        (∏ j, ENNReal.ofReal (p.2 j ^ h (Fin.succ j))) *
          G (p.1 ^ A 0 * ∏ j, p.2 j ^ A (Fin.succ j)))
    have hR := (hmp.restrict_preimage hTy).lintegral_comp_emb e.measurableEmbedding
      (fun p : ℝ × (Fin m → ℝ) ↦ ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * p.1))) *
        (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * p.2 j)))) *
          G (exp (-(p.1 + ∑ j, p.2 j))))
    simp_rw [hprodE, hprod, hsum, hprodExp]
    rw [pi_const_eq_preimage', pi_const_eq_preimage', ← he, hL, hR, Measure.volume_eq_prod,
      ← Measure.prod_restrict, ← Measure.prod_restrict, lintegral_prod _ hmx.aemeasurable,
      lintegral_prod _ hmy.aemeasurable]
    -- the remaining coordinates by the induction hypothesis
    have hin : ∀ x₀ : ℝ, ∫⁻ x' in Set.pi Set.univ (fun _ : Fin m ↦ Ioo (0 : ℝ) 1),
        ENNReal.ofReal (x₀ ^ h 0) * (∏ j, ENNReal.ofReal (x' j ^ h (Fin.succ j))) *
          G (x₀ ^ A 0 * ∏ j, x' j ^ A (Fin.succ j)) =
        ENNReal.ofReal (x₀ ^ h 0) * ((∏ j, ENNReal.ofReal (1 / A (Fin.succ j))) *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
            (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
              G (x₀ ^ A 0 * exp (-(∑ j, y' j)))) := by
      intro x₀
      have hG' : Measurable fun c ↦ G (x₀ ^ A 0 * c) := hG.comp (measurable_const.mul measurable_id)
      have hm' : Measurable fun x' : Fin m → ℝ ↦
          (∏ j, ENNReal.ofReal (x' j ^ h (Fin.succ j))) *
            G (x₀ ^ A 0 * ∏ j, x' j ^ A (Fin.succ j)) :=
        (Finset.measurable_prod _ fun j _ ↦
          ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).pow_const _)).mul
          (hG'.comp (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _))
      rw [← ih (fun j ↦ A (Fin.succ j)) (fun j ↦ h (Fin.succ j)) hA' _ hG',
        ← lintegral_const_mul _ hm']
      refine lintegral_congr fun x' ↦ ?_
      ring
    simp_rw [hin]
    -- the first coordinate: the one-dimensional substitution
    set P' : ℝ≥0∞ := ∏ j, ENNReal.ofReal (1 / A (Fin.succ j)) with hP'
    have hs' : Measurable fun p : ℝ × (Fin m → ℝ) ↦ ∑ j, p.2 j :=
      Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_snd
    have hF : Measurable (Function.uncurry fun (c : ℝ) (y' : Fin m → ℝ) ↦
        (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
          G (c * exp (-(∑ j, y' j)))) :=
      (Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
        (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)).neg.exp).mul
        (hG.comp (measurable_fst.mul hs'.neg.exp))
    have hsub : ∫⁻ x₀ in Ioo (0 : ℝ) 1, ENNReal.ofReal (x₀ ^ h 0) * (P' *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (x₀ ^ A 0 * exp (-(∑ j, y' j)))) =
        ∫⁻ y₀ in Ioi (0 : ℝ), ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * y₀)) / A 0) * (P' *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
            (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
              G (exp (-y₀) * exp (-(∑ j, y' j)))) :=
      lintegral_Ioo_rpow_mul_comp_rpow (hA 0) (h 0) (fun c ↦ P' *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (c * exp (-(∑ j, y' j))))
    have hmy₀' : Measurable fun y₀ : ℝ ↦
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(y₀ + ∑ j, y' j))) := by
      have : Measurable (Function.uncurry fun (y₀ : ℝ) (y' : Fin m → ℝ) ↦
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(y₀ + ∑ j, y' j)))) :=
        (Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
          (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)).neg.exp).mul
          (hG.comp hs.neg.exp)
      exact this.lintegral_prod_right'
    have hin2 : ∀ x₀ : ℝ, ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
        ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * x₀))) *
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(x₀ + ∑ j, y' j))) =
        ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * x₀))) *
          ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
            (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
              G (exp (-(x₀ + ∑ j, y' j))) := by
      intro x₀
      have hm : Measurable fun y' : Fin m → ℝ ↦
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(x₀ + ∑ j, y' j))) :=
        (Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
          (measurable_const.mul (measurable_pi_apply j)).neg.exp).mul
          (hG.comp (measurable_const.add (Finset.measurable_sum _ fun j _ ↦
            measurable_pi_apply j)).neg.exp)
      rw [← lintegral_const_mul _ hm]
      refine lintegral_congr fun y' ↦ ?_
      ring
    simp_rw [hin2]
    have hI2 : Measurable fun y₀ : ℝ ↦ ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * y₀))) *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(y₀ + ∑ j, y' j))) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id).neg.exp).mul hmy₀'
    have hI3 : Measurable fun y₀ : ℝ ↦ P' * (ENNReal.ofReal (exp (-((h 0 + 1) / A 0 * y₀))) *
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-(y₀ + ∑ j, y' j)))) :=
      measurable_const.mul hI2
    rw [hsub, Fin.prod_univ_succ, ← hP', mul_assoc, ← lintegral_const_mul _ hI2,
      ← lintegral_const_mul _ hI3]
    refine lintegral_congr fun y₀ ↦ ?_
    have hinner : ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
        (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
          G (exp (-(y₀ + ∑ j, y' j))) =
        ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
          (∏ j, ENNReal.ofReal (exp (-((h (Fin.succ j) + 1) / A (Fin.succ j) * y' j)))) *
            G (exp (-y₀) * exp (-(∑ j, y' j))) := by
      refine lintegral_congr fun y' ↦ ?_
      have e2 : exp (-(y₀ + ∑ j, y' j)) = exp (-y₀) * exp (-(∑ j, y' j)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e2]
    have e3 : exp (-((h 0 + 1) / A 0 * y₀)) / A 0 = 1 / A 0 * exp (-((h 0 + 1) / A 0 * y₀)) := by
      ring
    rw [hinner, e3, ENNReal.ofReal_mul (one_div_pos.mpr (hA 0)).le]
    ring

end Laplace.Multi
