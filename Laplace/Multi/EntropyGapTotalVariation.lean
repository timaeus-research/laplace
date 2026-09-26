/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EntropyGapStability

/-!
# The entropy gap as a total-variation modulus of continuity on the finite-rate domain

The entropy-gap inequality in its total-variation form: for finite-rate responses `A, B` with
reconstruction densities `r_A = dΠ(A)/dν`, `r_B = dΠ(B)/dν` and weights `a + b = 1`,

`(∫ |r_A − r_B| dν)² ≤ (2/(ab)) [a 𝓘(A) + b 𝓘(B) − 𝓘(aA + bB)]`
(`sq_integral_abs_rnDeriv_sub_le`),

by the sign test in the bounded-observable inequality. Consequently the reconstruction is
continuous in total variation on the whole finite-rate domain for the topology of `M ↦ (M, 𝓘(M))`
(`tendsto_integral_abs_rnDeriv_sub_of_tendsto_genRate`): the entropy gap at the midpoints tends to
zero (`tendsto_entropy_gap_zero`), so the total-variation distance does. This is the final form of
the map across the data manifold: no interior hypothesis, no radial restriction, and no natural
parameter at the boundary.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The response of a bounded observable through the reconstruction density. -/
theorem integral_responseProjection_eq_rnDeriv {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (F : X → ℝ) :
    ∫ x, F x ∂responseProjection hS ν M =
      ∫ x, ((responseProjection hS ν M).rnDeriv ν x).toReal * F x ∂ν := by
  have hP := (responseProjection_spec hS ν hfin).1
  rw [← integral_rnDeriv_smul (responseProjection_absolutelyContinuous hS ν hfin)]
  simp only [smul_eq_mul]

/-- **The entropy-gap inequality in total variation**: for finite-rate `A, B` and weights
`a + b = 1`, `(∫ |r_A − r_B| dν)² ≤ (2/(ab)) [a𝓘(A) + b𝓘(B) − 𝓘(aA + bB)]`. -/
theorem sq_integral_abs_rnDeriv_sub_le {A B : J → ℝ} (hA : genRate ν S A ≠ ⊤)
    (hB : genRate ν S B ≠ ⊤) {a b : ℝ≥0} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ x, |((responseProjection hS ν A).rnDeriv ν x).toReal -
      ((responseProjection hS ν B).rnDeriv ν x).toReal| ∂ν) ^ 2 ≤
      2 / ((a : ℝ) * b) * ((a : ℝ≥0∞) * genRate ν S A + (b : ℝ≥0∞) * genRate ν S B -
        genRate ν S ((a : ℝ) • A + (b : ℝ) • B)).toReal := by
  have hPA := (responseProjection_spec hS ν hA).1
  have hPB := (responseProjection_spec hS ν hB).1
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun x ↦
      if 0 ≤ ((responseProjection hS ν A).rnDeriv ν x).toReal -
        ((responseProjection hS ν B).rnDeriv ν x).toReal then (1 : ℝ) else -1 := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact Measurable.ite (measurableSet_le measurable_const
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
        (Measure.measurable_rnDeriv _ _).ennreal_toReal)) measurable_const measurable_const
  have hF1 : ∀ x, |F x - 0| ≤ 1 := fun x ↦ by
    rw [hF, sub_zero]
    beta_reduce
    split_ifs <;> simp
  have hFb : Bdd F := ⟨hFm, 1, fun x ↦ by simpa using hF1 x⟩
  have hgap := ofReal_sq_sub_le_gap hS ν hA hB hab ha hb hFb one_pos hF1
  -- the sign test
  have hI : ∀ (M : J → ℝ), genRate ν S M ≠ ⊤ →
      Integrable (fun x ↦ ((responseProjection hS ν M).rnDeriv ν x).toReal * F x) ν :=
    fun M hM ↦ by
      have hP := (responseProjection_spec hS ν hM).1
      exact (Measure.integrable_toReal_rnDeriv).mul_bdd hFm.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; simpa using hF1 x)
  have e : (∫ x, F x ∂responseProjection hS ν A) - ∫ x, F x ∂responseProjection hS ν B =
      ∫ x, |((responseProjection hS ν A).rnDeriv ν x).toReal -
        ((responseProjection hS ν B).rnDeriv ν x).toReal| ∂ν := by
    rw [integral_responseProjection_eq_rnDeriv hS ν hA,
      integral_responseProjection_eq_rnDeriv hS ν hB, ← integral_sub (hI A hA) (hI B hB)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hF]
    beta_reduce
    split_ifs with h0
    · rw [abs_of_nonneg h0]
      ring
    · rw [abs_of_neg (lt_of_not_ge h0)]
      ring
  rw [e] at hgap
  -- extract the real inequality
  have hne : (a : ℝ≥0∞) * genRate ν S A + (b : ℝ≥0∞) * genRate ν S B ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hA,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hB⟩
  have hmidne : genRate ν S ((a : ℝ) • A + (b : ℝ) • B) ≠ ⊤ :=
    ne_top_of_le_ne_top hne (le_add_self.trans hgap)
  have hG : ENNReal.ofReal ((a : ℝ) * b * (∫ x, |((responseProjection hS ν A).rnDeriv ν x).toReal -
      ((responseProjection hS ν B).rnDeriv ν x).toReal| ∂ν) ^ 2 / (2 * 1 ^ 2)) ≤
      (a : ℝ≥0∞) * genRate ν S A + (b : ℝ≥0∞) * genRate ν S B -
        genRate ν S ((a : ℝ) • A + (b : ℝ) • B) :=
    ENNReal.le_sub_of_add_le_right hmidne hgap
  have hr := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.sub_ne_top hne)).1 hG
  have hab0 : 0 < (a : ℝ) * b := by
    have ha' : 0 < (a : ℝ) := by
      rcases lt_or_eq_of_le a.coe_nonneg with h | h
      · exact h
      · exact absurd (NNReal.coe_eq_zero.1 h.symm) ha
    have hb' : 0 < (b : ℝ) := by
      rcases lt_or_eq_of_le b.coe_nonneg with h | h
      · exact h
      · exact absurd (NNReal.coe_eq_zero.1 h.symm) hb
    positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hab0]
  have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * 1 ^ 2)).1 hr
  linarith

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **The entropy gap at the midpoints tends to zero** along any approach `M_i → M_*` with
`𝓘(M_i) → 𝓘(M_*) < ∞`. -/
theorem tendsto_entropy_gap_zero {ι : Type*} {l : Filter ι} {M : ι → J → ℝ} {M₀ : J → ℝ}
    (hM₀ : genRate ν S M₀ ≠ ⊤) (hM : Tendsto M l (𝓝 M₀))
    (hI : Tendsto (fun i ↦ genRate ν S (M i)) l (𝓝 (genRate ν S M₀))) {a : ℝ≥0} (haa : a + a = 1) :
    Tendsto (fun i ↦ (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ -
      genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀)) l (𝓝 0) := by
  have haa' : (a : ℝ≥0∞) + a = 1 := by rw [← ENNReal.coe_add, haa, ENNReal.coe_one]
  have hmidt : Tendsto (fun i ↦ (a : ℝ) • M i + (a : ℝ) • M₀) l (𝓝 M₀) := by
    have h := (hM.const_smul (a : ℝ)).add (tendsto_const_nhds (x := (a : ℝ) • M₀))
    have hlim : (a : ℝ) • M₀ + (a : ℝ) • M₀ = M₀ := by
      rw [← add_smul, ← NNReal.coe_add, haa, NNReal.coe_one, one_smul]
    rw [hlim] at h
    exact h
  have hup : Tendsto (fun i ↦ (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀) l
      (𝓝 (genRate ν S M₀)) := by
    have h1 : Tendsto (fun i ↦ (a : ℝ≥0∞) * genRate ν S (M i)) l
        (𝓝 ((a : ℝ≥0∞) * genRate ν S M₀)) :=
      ENNReal.Tendsto.const_mul hI (Or.inr ENNReal.coe_ne_top)
    have h := h1.add (tendsto_const_nhds (x := (a : ℝ≥0∞) * genRate ν S M₀))
    rwa [← add_mul, haa', one_mul] at h
  have hlow : ∀ y < genRate ν S M₀,
      ∀ᶠ i in l, y < genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀) := fun y hy ↦
    hmidt.eventually (lowerSemicontinuous_genRate ν S M₀ y hy)
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have h1 : ∀ᶠ i in l, (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ ≤
      genRate ν S M₀ + ε / 2 :=
    hup.eventually (Iic_mem_nhds (ENNReal.lt_add_right hM₀ hε2))
  have h2 : ∀ᶠ i in l, genRate ν S M₀ ≤ genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀) + ε / 2 := by
    by_cases h0 : genRate ν S M₀ ≤ ε / 2
    · exact Eventually.of_forall fun i ↦ h0.trans le_add_self
    · push Not at h0
      have hy : genRate ν S M₀ - ε / 2 < genRate ν S M₀ :=
        ENNReal.sub_lt_self hM₀ (pos_of_gt h0).ne' hε2
      filter_upwards [hlow _ hy] with i hi
      exact tsub_le_iff_right.1 hi.le
  filter_upwards [h1, h2] with i h1 h2
  calc (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ -
        genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀)
      ≤ (genRate ν S M₀ + ε / 2) - genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀) :=
        tsub_le_tsub_right h1 _
    _ ≤ ε := by
        rw [tsub_le_iff_right]
        calc genRate ν S M₀ + ε / 2
            ≤ (genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀) + ε / 2) + ε / 2 :=
              add_le_add h2 le_rfl
          _ = ε + genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀) := by
              rw [add_assoc, ENNReal.add_halves, add_comm]

/-- **Total-variation continuity of the reconstruction on the finite-rate domain** for the topology
of `M ↦ (M, 𝓘(M))`: if finite-rate `M_i → M_*` with `𝓘(M_i) → 𝓘(M_*) < ∞`, then
`∫ |r_{M_i} − r_{M_*}| dν → 0`. -/
theorem tendsto_integral_abs_rnDeriv_sub_of_tendsto_genRate {ι : Type*} {l : Filter ι}
    {M : ι → J → ℝ} {M₀ : J → ℝ} (hM₀ : genRate ν S M₀ ≠ ⊤)
    (hfin : ∀ᶠ i in l, genRate ν S (M i) ≠ ⊤) (hM : Tendsto M l (𝓝 M₀))
    (hI : Tendsto (fun i ↦ genRate ν S (M i)) l (𝓝 (genRate ν S M₀))) :
    Tendsto (fun i ↦ ∫ x, |((responseProjection hS ν (M i)).rnDeriv ν x).toReal -
      ((responseProjection hS ν M₀).rnDeriv ν x).toReal| ∂ν) l (𝓝 0) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, a = 2⁻¹ := ⟨_, rfl⟩
  have haa : a + a = 1 := by
    rw [ha]
    ext
    push_cast
    norm_num
  have ha0 : a ≠ 0 := by rw [ha]; exact inv_ne_zero two_ne_zero
  have haR : (0 : ℝ) < a := by rw [ha]; positivity
  have hG := tendsto_entropy_gap_zero ν hM₀ hM hI haa
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 / ((a : ℝ) * a) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hGr : Tendsto (fun i ↦ ((a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ -
      genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀)).toReal) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG
    rw [ENNReal.toReal_zero] at this
    exact this
  have hsq : Tendsto (fun i ↦ √(κ * ((a : ℝ≥0∞) * genRate ν S (M i) +
      (a : ℝ≥0∞) * genRate ν S M₀ - genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀)).toReal)) l
      (𝓝 0) := by
    have h2 : Tendsto (fun i ↦ κ * ((a : ℝ≥0∞) * genRate ν S (M i) +
        (a : ℝ≥0∞) * genRate ν S M₀ - genRate ν S ((a : ℝ) • M i + (a : ℝ) • M₀)).toReal) l
        (𝓝 0) := by
      have := hGr.const_mul κ
      rwa [mul_zero] at this
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
    (Eventually.of_forall fun i ↦ integral_nonneg fun x ↦ abs_nonneg _) ?_
  filter_upwards [hfin] with i hfi
  have h := sq_integral_abs_rnDeriv_sub_le hS ν hfi hM₀ haa ha0 ha0
  rw [← hκ] at h
  exact Real.le_sqrt_of_sq_le h

end Laplace.Multi
