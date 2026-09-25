/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Laplace.Multi.RecessionDirection

/-!
# Integrability of the single-scale profile: the recession-cone criterion

Astra round 14, item 4 ("LP uniqueness ⇔ profile integrability", for the anchored unquotiented
profile). Under a strict truth constraint an integrable dominant-scale profile has at most one
scaled coordinate (`not_integrable_envelope_of_two_scaled`); for one scaled coordinate `j` the
profile is
`Ψ(u) = 1_{u_j > 0} ∏_{i ≠ j} 1_{0 < u_i < ρ} ∏_i u_i^{r_i} e^{-c ∏_i u_i^{κ_i}}`
(`singleScaleProfile`), and **it is integrable if and only if `r_j > −1` and every other
coordinate has effective exponent `r_i − κ_i (r_j + 1)/κ_j > −1`**
(`integrable_singleScaleProfile_iff`, `c > 0`, `κ_j > 0`). The condition says that the ratio
`(r_j + 1)/κ_j` of the scaled coordinate is strictly below the ratio `(r_i + 1)/κ_i` of every
other coordinate with `κ_i > 0` — the strict (unique) optimum of the phase-constrained LP
`min ∑ (r_i + 1) α_i` over `α ≥ 0`, `κ · α ≥ δ`, whose value is attained at the vertex
`α = (δ/κ_j) e_j` of minimal ratio — while coordinates with `κ_i ≤ 0` only need their effective
exponent above `−1`. Sufficiency is Fubini in the scaled coordinate and the Gamma integral
`∫_0^∞ v^{r_j} e^{-b v^{κ_j}} dv = b^{-(r_j+1)/κ_j} Γ((r_j+1)/κ_j)/κ_j` with
`b = c ∏_{i ≠ j} u_i^{κ_i}`, leaving a product of powers on the box; necessity is the
recession-direction obstruction (`not_integrable_of_recession_direction`) along `d = −e_j`
(`r_j ≤ −1`) or along
`d = κ_i e_j − κ_j e_i` (effective exponent of `i` at most `−1`): both directions keep the domain
invariant, have `d · κ ≤ 0` and `d · (r + 1) ≥ 0`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-- The domain of the single-scale profile: `u_j > 0`, `0 < u_i < ρ` for `i ≠ j`. -/
def singleScaleDomain (ρ : ℝ) (j : Fin (m + 1)) : Set (Fin (m + 1) → ℝ) :=
  Set.pi univ fun i ↦ if i = j then Ioi (0 : ℝ) else Ioo 0 ρ

/-- The box `(0, ρ)^m` of the unscaled coordinates. -/
def unscaledBox (ρ : ℝ) : Set (Fin m → ℝ) := Set.pi univ fun _ ↦ Ioo (0 : ℝ) ρ

theorem measurableSet_singleScaleDomain (ρ : ℝ) (j : Fin (m + 1)) :
    MeasurableSet (singleScaleDomain ρ j) :=
  MeasurableSet.pi countable_univ fun i _ ↦ by
    split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Ioo

theorem measurableSet_unscaledBox (ρ : ℝ) : MeasurableSet (unscaledBox (m := m) ρ) :=
  MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo

theorem singleScaleDomain_pos {ρ : ℝ} {j : Fin (m + 1)} {u : Fin (m + 1) → ℝ}
    (hu : u ∈ singleScaleDomain ρ j) (i : Fin (m + 1)) : 0 < u i := by
  have := Set.mem_univ_pi.mp hu i
  split_ifs at this with h
  · exact this
  · exact this.1

/-- The single-scale profile `1_{domain} ∏ u^r e^{-c ∏ u^κ}`. -/
noncomputable def singleScaleProfile (ρ c : ℝ) (j : Fin (m + 1)) (r κ : Fin (m + 1) → ℝ)
    (u : Fin (m + 1) → ℝ) : ℝ :=
  (singleScaleDomain ρ j).indicator (fun u ↦ ∏ i, u i ^ r i) u * exp (-(c * ∏ i, u i ^ κ i))

theorem insertNth_mem_singleScaleDomain_iff (ρ : ℝ) (j : Fin (m + 1)) (v : ℝ) (w : Fin m → ℝ) :
    j.insertNth (α := fun _ ↦ ℝ) v w ∈ singleScaleDomain ρ j ↔ 0 < v ∧ w ∈ unscaledBox ρ := by
  unfold singleScaleDomain unscaledBox
  rw [Set.mem_univ_pi, Set.mem_univ_pi, Fin.forall_iff_succAbove j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, if_true,
    Fin.succAbove_ne j, if_false, mem_Ioi]

/-- The profile in the split coordinates `(v, w) = (u_j, (u_i)_{i ≠ j})`. -/
theorem singleScaleProfile_insertNth (ρ c : ℝ) (j : Fin (m + 1)) (r κ : Fin (m + 1) → ℝ) (v : ℝ)
    (w : Fin m → ℝ) :
    singleScaleProfile ρ c j r κ (j.insertNth (α := fun _ ↦ ℝ) v w) =
      ((Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j) v *
        (unscaledBox ρ).indicator (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) w) *
        exp (-(c * (v ^ κ j * ∏ i, w i ^ κ (j.succAbove i)))) := by
  unfold singleScaleProfile
  rw [Fin.prod_univ_succAbove _ j, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]
  congr 1
  by_cases hm : j.insertNth (α := fun _ ↦ ℝ) v w ∈ singleScaleDomain ρ j
  · rw [indicator_of_mem hm]
    obtain ⟨hv, hw⟩ := (insertNth_mem_singleScaleDomain_iff ρ j v w).mp hm
    rw [indicator_of_mem (show v ∈ Ioi 0 from hv), indicator_of_mem hw,
      Fin.prod_univ_succAbove _ j, Fin.insertNth_apply_same]
    simp only [Fin.insertNth_apply_succAbove]
  · rw [indicator_of_notMem hm]
    rw [insertNth_mem_singleScaleDomain_iff, not_and_or] at hm
    rcases hm with hv | hw
    · rw [indicator_of_notMem (show v ∉ Ioi 0 from hv), zero_mul]
    · rw [indicator_of_notMem hw, mul_zero]

theorem measurable_singleScaleProfile (ρ c : ℝ) (j : Fin (m + 1)) (r κ : Fin (m + 1) → ℝ) :
    Measurable (singleScaleProfile ρ c j r κ) := by
  unfold singleScaleProfile
  refine Measurable.mul (Measurable.indicator ?_ (measurableSet_singleScaleDomain ρ j)) ?_
  · exact Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  · exact Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg

theorem singleScaleProfile_nonneg (ρ c : ℝ) (j : Fin (m + 1)) (r κ : Fin (m + 1) → ℝ)
    (u : Fin (m + 1) → ℝ) : 0 ≤ singleScaleProfile ρ c j r κ u := by
  unfold singleScaleProfile
  refine mul_nonneg (Set.indicator_nonneg (fun u hu ↦ ?_) u) (exp_pos _).le
  exact Finset.prod_nonneg fun i _ ↦ rpow_nonneg (singleScaleDomain_pos hu i).le _

/-! ### Sufficiency: Fubini and the Gamma integral -/

/-- The inner integral at fixed unscaled coordinates in the box. -/
theorem integral_singleScale_inner {ρ c : ℝ} (hc : 0 < c) {j : Fin (m + 1)}
    {r κ : Fin (m + 1) → ℝ} (hrj : -1 < r j) (hκj : 0 < κ j) {w : Fin m → ℝ}
    (hw : w ∈ unscaledBox ρ) :
    ∫ v, singleScaleProfile ρ c j r κ (j.insertNth (α := fun _ ↦ ℝ) v w) =
      (c * ∏ i, w i ^ κ (j.succAbove i)) ^ (-(r j + 1) / κ j) * (1 / κ j) *
        Gamma ((r j + 1) / κ j) * ∏ i, w i ^ r (j.succAbove i) := by
  have hw0 : ∀ i, 0 < w i := fun i ↦ (Set.mem_univ_pi.mp hw i).1
  have hP : 0 < ∏ i, w i ^ κ (j.succAbove i) := Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (hw0 i) _
  have hb : 0 < c * ∏ i, w i ^ κ (j.succAbove i) := mul_pos hc hP
  simp_rw [singleScaleProfile_insertNth, indicator_of_mem hw]
  have e : (fun v ↦ (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j) v *
      (∏ i, w i ^ r (j.succAbove i)) * exp (-(c * (v ^ κ j * ∏ i, w i ^ κ (j.succAbove i))))) =
      (Ioi (0 : ℝ)).indicator (fun v ↦ (∏ i, w i ^ r (j.succAbove i)) *
        (v ^ r j * exp (-(c * ∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) := by
    funext v
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hv, indicator_of_mem hv]
      ring_nf
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul, zero_mul]
  rw [e, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow hκj hrj hb]
  ring

/-- **Sufficiency.** `r_j > −1` and effective exponents `> −1` give an integrable profile. -/
theorem integrable_singleScaleProfile {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) {j : Fin (m + 1)}
    {r κ : Fin (m + 1) → ℝ} (hrj : -1 < r j) (hκj : 0 < κ j)
    (hi : ∀ i, -1 < r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j) :
    Integrable (singleScaleProfile ρ c j r κ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) j with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) j
  rw [← hmp.symm.integrable_comp_emb e.symm.measurableEmbedding]
  have hf : (singleScaleProfile ρ c j r κ ∘ e.symm) =
      fun p : ℝ × (Fin m → ℝ) ↦ singleScaleProfile ρ c j r κ (j.insertNth p.1 p.2) := rfl
  rw [hf, Measure.volume_eq_prod]
  have hmeas : Measurable fun p : ℝ × (Fin m → ℝ) ↦
      singleScaleProfile ρ c j r κ (j.insertNth p.1 p.2) :=
    (measurable_singleScaleProfile ρ c j r κ).comp
      (measurable_pi_iff.mpr fun i ↦ by
        rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨k, hk⟩
        · subst h
          simp only [Fin.insertNth_apply_same]
          exact measurable_fst
        · subst hk
          simp only [Fin.insertNth_apply_succAbove]
          exact (measurable_pi_apply k).comp measurable_snd)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun w ↦ ?_, ?_⟩
  · -- the inner integrability
    change Integrable (fun v ↦ singleScaleProfile ρ c j r κ (j.insertNth v w)) volume
    by_cases hw : w ∈ unscaledBox ρ
    · have hw0 : ∀ i, 0 < w i := fun i ↦ (Set.mem_univ_pi.mp hw i).1
      have hP : 0 < ∏ i, w i ^ κ (j.succAbove i) :=
        Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (hw0 i) _
      have hb : 0 < c * ∏ i, w i ^ κ (j.succAbove i) := mul_pos hc hP
      simp_rw [singleScaleProfile_insertNth, indicator_of_mem hw]
      have e : (fun v ↦ (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j) v *
          (∏ i, w i ^ r (j.succAbove i)) *
          exp (-(c * (v ^ κ j * ∏ i, w i ^ κ (j.succAbove i))))) =
          (Ioi (0 : ℝ)).indicator (fun v ↦ (∏ i, w i ^ r (j.succAbove i)) *
            (v ^ r j * exp (-(c * ∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) := by
        funext v
        by_cases hv : v ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hv, indicator_of_mem hv]
          ring_nf
        · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul, zero_mul]
      rw [e, integrable_indicator_iff measurableSet_Ioi]
      exact (integrableOn_rpow_mul_exp_neg_mul_rpow hrj hκj hb).const_mul _
    · have e : (fun v ↦ singleScaleProfile ρ c j r κ (j.insertNth v w)) = fun _ ↦ 0 := by
        funext v
        rw [singleScaleProfile_insertNth, indicator_of_notMem hw, mul_zero, zero_mul]
      rw [e]
      exact integrable_zero _ _ _
  · -- the outer integrability: a product of powers on the box
    change Integrable (fun w : Fin m → ℝ ↦
      ∫ v, ‖singleScaleProfile ρ c j r κ (j.insertNth v w)‖) volume
    have hnn : ∀ w v, 0 ≤ singleScaleProfile ρ c j r κ (j.insertNth v w) := fun w v ↦
      singleScaleProfile_nonneg ρ c j r κ _
    have hout : (fun w : Fin m → ℝ ↦ ∫ v, ‖singleScaleProfile ρ c j r κ (j.insertNth v w)‖) =
        fun w ↦ (unscaledBox ρ).indicator (fun w ↦ c ^ (-(r j + 1) / κ j) * (1 / κ j) *
          Gamma ((r j + 1) / κ j) *
          ∏ i, w i ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j)) w := by
      funext w
      simp_rw [Real.norm_of_nonneg (hnn w _)]
      by_cases hw : w ∈ unscaledBox ρ
      · rw [indicator_of_mem hw, integral_singleScale_inner hc hrj hκj hw]
        have hw0 : ∀ i, 0 < w i := fun i ↦ (Set.mem_univ_pi.mp hw i).1
        have hP : 0 ≤ ∏ i, w i ^ κ (j.succAbove i) :=
          Finset.prod_nonneg fun i _ ↦ (rpow_pos_of_pos (hw0 i) _).le
        rw [Real.mul_rpow hc.le hP, ← Real.finsetProd_rpow _ _ fun i _ ↦
          (rpow_pos_of_pos (hw0 i) _).le]
        have e : ∀ i, (w i ^ κ (j.succAbove i)) ^ (-(r j + 1) / κ j) * w i ^ r (j.succAbove i) =
            w i ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j) := fun i ↦ by
          rw [← Real.rpow_mul (hw0 i).le, ← Real.rpow_add (hw0 i)]
          congr 1
          ring
        have hprod : (∏ i, (w i ^ κ (j.succAbove i)) ^ (-(r j + 1) / κ j)) *
            ∏ i, w i ^ r (j.succAbove i) =
            ∏ i, w i ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ ↦ e i
        rw [← hprod]
        ring
      · rw [indicator_of_notMem hw]
        have e : (fun v ↦ singleScaleProfile ρ c j r κ (j.insertNth v w)) = fun _ ↦ 0 := by
          funext v
          rw [singleScaleProfile_insertNth, indicator_of_notMem hw, mul_zero, zero_mul]
        rw [e, integral_zero]
    rw [hout]
    have hbox : (fun w : Fin m → ℝ ↦ (unscaledBox ρ).indicator
        (fun w ↦ ∏ i, w i ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j)) w) =
        fun w ↦ ∏ i, (Ioo (0 : ℝ) ρ).indicator
          (fun x ↦ x ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j)) (w i) := by
      funext w
      by_cases hw : w ∈ unscaledBox ρ
      · rw [indicator_of_mem hw]
        exact Finset.prod_congr rfl fun i _ ↦ by
          rw [indicator_of_mem (Set.mem_univ_pi.mp hw i)]
      · rw [indicator_of_notMem hw]
        obtain ⟨i, hi⟩ : ∃ i, w i ∉ Ioo (0 : ℝ) ρ := by
          by_contra h
          push Not at h
          exact hw (Set.mem_univ_pi.mpr h)
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)
    have hint : Integrable (fun w : Fin m → ℝ ↦ (unscaledBox ρ).indicator
        (fun w ↦ ∏ i, w i ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j)) w) := by
      rw [hbox, volume_pi]
      refine Integrable.fintype_prod (f := fun i (x : ℝ) ↦ (Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ x ^ (r (j.succAbove i) - κ (j.succAbove i) * (r j + 1) / κ j)) x) fun i ↦ ?_
      rw [integrable_indicator_iff measurableSet_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff hρ).mpr (hi i)
    refine (hint.const_mul (c ^ (-(r j + 1) / κ j) * (1 / κ j) * Gamma ((r j + 1) / κ j))).congr
      (Eventually.of_forall fun w ↦ ?_)
    by_cases hw : w ∈ unscaledBox ρ
    · simp only [indicator_of_mem hw]
    · simp only [indicator_of_notMem hw, mul_zero]

/-! ### Necessity: recession directions -/

theorem singleScaleDomain_flow_mem {ρ : ℝ} {j : Fin (m + 1)} {d : Fin (m + 1) → ℝ}
    (hd : ∀ i, i ≠ j → d i ≤ 0) {s : ℝ} (hs : 0 ≤ s) {u : Fin (m + 1) → ℝ}
    (hu : u ∈ singleScaleDomain ρ j) : flow d s u ∈ singleScaleDomain ρ j := by
  unfold singleScaleDomain at hu ⊢
  rw [Set.mem_univ_pi] at hu ⊢
  intro i
  have hi := hu i
  by_cases hij : i = j
  · simp only [hij, if_true] at hi ⊢
    exact mul_pos (exp_pos _) hi
  · simp only [hij, if_false] at hi ⊢
    refine ⟨mul_pos (exp_pos _) hi.1, ?_⟩
    have hexp : exp (s * d i) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos hs (hd i hij)
    calc flow d s u i = exp (s * d i) * u i := rfl
      _ ≤ 1 * u i := mul_le_mul_of_nonneg_right hexp hi.1.le
      _ < ρ := by rw [one_mul]; exact hi.2

theorem box_subset_singleScaleDomain {ρ : ℝ} (hρ : 0 < ρ) (j : Fin (m + 1)) :
    (Set.pi univ fun _ : Fin (m + 1) ↦ Icc (ρ / 4) (ρ / 2)) ⊆ singleScaleDomain ρ j := by
  intro u hu
  unfold singleScaleDomain
  rw [Set.mem_univ_pi] at hu ⊢
  intro i
  have hi := hu i
  split_ifs
  · exact show (0 : ℝ) < u i by linarith [hi.1]
  · exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- **Necessity, the scaled coordinate.** `r_j ≤ −1` forbids integrability. -/
theorem not_integrable_singleScaleProfile_of_le {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    {j : Fin (m + 1)} {r κ : Fin (m + 1) → ℝ} (hrj : r j ≤ -1) (hκj : 0 ≤ κ j) :
    ¬ Integrable (singleScaleProfile ρ c j r κ) := by
  classical
  unfold singleScaleProfile
  refine not_integrable_of_recession_direction (measurableSet_singleScaleDomain ρ j)
    (fun u hu i ↦ singleScaleDomain_pos hu i) (-Pi.single j 1) ?_ ?_ (fun _ ↦ ρ / 4)
    (fun _ ↦ ρ / 2) (fun _ ↦ ⟨by positivity, by linarith⟩) (box_subset_singleScaleDomain hρ j)
    (r := r) (κ := κ) ?_ ?_ (Φ := fun u ↦ c * ∏ i, u i ^ κ i) (K := c) hc (fun u _ ↦ le_rfl)
  · intro h
    have := congrFun h j
    simp at this
  · intro s hs u hu
    refine singleScaleDomain_flow_mem (fun i hij ↦ ?_) hs hu
    simp [hij]
  · simp only [Pi.neg_apply, Pi.single_apply, neg_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith
  · simp only [Pi.neg_apply, Pi.single_apply, neg_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith

/-- **Necessity, an unscaled coordinate.** An effective exponent at most `−1` forbids
integrability (direction `κ_i e_j − κ_j e_i`). -/
theorem not_integrable_singleScaleProfile_of_effective_le {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    {j : Fin (m + 1)} {r κ : Fin (m + 1) → ℝ} (hκj : 0 < κ j) {i : Fin (m + 1)} (hij : i ≠ j)
    (hi : r i - κ i * (r j + 1) / κ j ≤ -1) :
    ¬ Integrable (singleScaleProfile ρ c j r κ) := by
  classical
  unfold singleScaleProfile
  refine not_integrable_of_recession_direction (measurableSet_singleScaleDomain ρ j)
    (fun u hu i ↦ singleScaleDomain_pos hu i) (Pi.single j (κ i) - Pi.single i (κ j)) ?_ ?_
    (fun _ ↦ ρ / 4) (fun _ ↦ ρ / 2) (fun _ ↦ ⟨by positivity, by linarith⟩)
    (box_subset_singleScaleDomain hρ j) (r := r) (κ := κ) ?_ ?_
    (Φ := fun u ↦ c * ∏ i, u i ^ κ i) (K := c) hc (fun u _ ↦ le_rfl)
  · intro h
    have := congrFun h i
    rw [Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.single_eq_same, Pi.zero_apply, zero_sub,
      neg_eq_zero] at this
    exact hκj.ne' this
  · intro s hs u hu
    refine singleScaleDomain_flow_mem (fun l hlj ↦ ?_) hs hu
    simp only [Pi.sub_apply, Pi.single_apply, hlj, if_false, zero_sub]
    split_ifs
    · exact neg_nonpos.mpr hκj.le
    · simp
  · simp only [Pi.sub_apply, Pi.single_apply, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h1 : κ j * (r i + 1) ≤ κ i * (r j + 1) := by
      have := hi
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hκj] at this
      linarith
    linarith
  · simp only [Pi.sub_apply, Pi.single_apply, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith

/-- **The recession-cone criterion for the single-scale profile.** -/
theorem integrable_singleScaleProfile_iff {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) {j : Fin (m + 1)}
    {r κ : Fin (m + 1) → ℝ} (hκj : 0 < κ j) :
    Integrable (singleScaleProfile ρ c j r κ) ↔
      -1 < r j ∧ ∀ i, i ≠ j → -1 < r i - κ i * (r j + 1) / κ j := by
  constructor
  · intro hint
    refine ⟨?_, fun i hij ↦ ?_⟩
    · by_contra h
      exact not_integrable_singleScaleProfile_of_le hρ hc.le (not_lt.mp h) hκj.le hint
    · by_contra h
      exact not_integrable_singleScaleProfile_of_effective_le hρ hc.le hκj hij (not_lt.mp h) hint
  · rintro ⟨hrj, hi⟩
    exact integrable_singleScaleProfile hρ hc hrj hκj fun i ↦ hi _ (Fin.succAbove_ne j i)

end Laplace.Multi
