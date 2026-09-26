/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixtureCompensation
import Laplace.Multi.VisibleBudget

/-!
# Closing the Legendre diagram

The rate is defined as the Fenchel conjugate of the log-partition function,
`𝓘(M) = sup_q [⟨q, M⟩ − Λ(q)]` with `Λ(q) = log ∫ e^{⟨q,S⟩} dν`. Conversely, on the finite domain
of the rate,

  `Λ(q) = sup { ⟨q, M⟩ − 𝓘(M) : 𝓘(M) < ∞ }`                     (`isGreatest_featCgf`)

with the supremum **attained exactly at the tilted mean** `M = m(−q)`, the response of
`P_{−q} ∝ e^{⟨q,S⟩} ν` (`featCgf_eq_dotJ_sub_genRate_meanMap`), and **at no other response**
(`eq_meanMap_of_dotJ_sub_genRate_eq`, by strict convexity of the rate). The Fenchel inequality is
the definition of the rate; attainment is the Bregman identity `𝓘(m(θ)) = KL(P_θ ‖ ν)`; uniqueness
is `genRate_mixture_lt`. Together with `∇Λ(q) = m(−q)` (`hasFDerivAt_affLogZ`) this closes the
Legendre diagram between natural coordinates and responses on the whole finite domain.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] hS [IsProbabilityMeasure ν] in
/-- **The Fenchel inequality**: `⟨q, M⟩ − 𝓘(M) ≤ Λ(q)` for every finite-rate response. -/
theorem dotJ_sub_genRate_le_featCgf {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) (q : J → ℝ) :
    dotJ q M - (genRate ν S M).toReal ≤ featCgf ν S q := by
  have h : ENNReal.ofReal (dotJ q M - featCgf ν S q) ≤ genRate ν S M :=
    le_iSup (fun q' ↦ ENNReal.ofReal (dotJ q' M - featCgf ν S q')) q
  rw [ENNReal.ofReal_le_iff_le_toReal hfin] at h
  linarith

/-- **The rate of the tilted mean** `m(−q)` is `⟨q, m(−q)⟩ − Λ(q)`. -/
theorem genRate_meanMap_neg (q : J → ℝ) :
    genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) =
      ENNReal.ofReal (dotJ q (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) -
        featCgf ν S q) := by
  rw [genRate_eq_rateFun ν S, rateFun_meanMap (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS one_pos (-q),
    famKL_eq measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      measurable_const (M₀ := 0) (fun _ ↦ by simp) hS, affLogZ_one_zero_eq_featCgf,
    affLogZ_one_zero_eq_featCgf, neg_zero, featCgf_zero', neg_neg]
  congr 1
  simp only [Pi.zero_apply, zero_sub, one_mul, Pi.neg_apply, neg_neg, dotJ]
  ring

/-- **Attainment**: `Λ(q) = ⟨q, m(−q)⟩ − 𝓘(m(−q))`, and the rate there is finite. -/
theorem featCgf_eq_dotJ_sub_genRate_meanMap (q : J → ℝ) :
    genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) ≠ ⊤ ∧
      dotJ q (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) -
        (genRate ν S (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q))).toReal =
      featCgf ν S q := by
  have h := genRate_meanMap_neg hS ν q
  refine ⟨by rw [h]; exact ENNReal.ofReal_ne_top, ?_⟩
  have hnn : 0 ≤ dotJ q (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) -
      featCgf ν S q := by
    have h0 := famKL_nonneg (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
      (fun _ ↦ by simp) hS one_pos (-q) 0
    rw [famKL_eq measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
      measurable_const (M₀ := 0) (fun _ ↦ by simp) hS, affLogZ_one_zero_eq_featCgf,
      affLogZ_one_zero_eq_featCgf, neg_zero, featCgf_zero', neg_neg] at h0
    simp only [Pi.zero_apply, zero_sub, one_mul, Pi.neg_apply, neg_neg] at h0
    have e : ∑ i, q i * meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q) i =
        dotJ q (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) := rfl
    linarith
  rw [h, ENNReal.toReal_ofReal hnn]
  ring

/-- **Uniqueness of the attaining response**: a finite-rate `M` with `⟨q, M⟩ − 𝓘(M) = Λ(q)` is the
tilted mean `m(−q)`. -/
theorem eq_meanMap_of_dotJ_sub_genRate_eq [Nonempty J] {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    {q : J → ℝ}
    (hM : dotJ q M - (genRate ν S M).toReal = featCgf ν S q) :
    M = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q) := by
  obtain ⟨hfin', hM'⟩ := featCgf_eq_dotJ_sub_genRate_meanMap hS ν q
  by_contra hne
  have hlt := genRate_mixture_lt hS ν hfin hfin' hne (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨Mmid, hmid⟩ : ∃ Mmid : J → ℝ, Mmid = ((1 / 2 : ℝ≥0) : ℝ) • M +
      ((1 / 2 : ℝ≥0) : ℝ) • meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q) := ⟨_, rfl⟩
  rw [← hmid] at hlt
  have hRfin : ((1 / 2 : ℝ≥0) : ℝ≥0∞) * genRate ν S M +
      ((1 / 2 : ℝ≥0) : ℝ≥0∞) * genRate ν S
        (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hfin,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hfin'⟩
  have hmidfin : genRate ν S Mmid ≠ ⊤ := ne_top_of_lt hlt
  have hreal := ENNReal.toReal_strict_mono hRfin hlt
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin'), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal] at hreal
  have hup := dotJ_sub_genRate_le_featCgf ν hmidfin q
  have hlin : dotJ q Mmid = ((1 / 2 : ℝ≥0) : ℝ) * dotJ q M +
      ((1 / 2 : ℝ≥0) : ℝ) * dotJ q (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (-q)) := by
    rw [hmid, (isLinearMap_dotJ q).map_add, (isLinearMap_dotJ q).map_smul,
      (isLinearMap_dotJ q).map_smul, smul_eq_mul, smul_eq_mul]
  have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hhalf] at hreal hlin
  linarith

/-- **The Legendre closure**: `Λ(q)` is the greatest value of `⟨q, M⟩ − 𝓘(M)` over the finite
domain of the rate. -/
theorem isGreatest_featCgf (q : J → ℝ) :
    IsGreatest {r : ℝ | ∃ M : J → ℝ, genRate ν S M ≠ ⊤ ∧ r = dotJ q M - (genRate ν S M).toReal}
      (featCgf ν S q) := by
  obtain ⟨hfin', hM'⟩ := featCgf_eq_dotJ_sub_genRate_meanMap hS ν q
  refine ⟨⟨_, hfin', hM'.symm⟩, ?_⟩
  rintro r ⟨M, hfin, rfl⟩
  exact dotJ_sub_genRate_le_featCgf ν hfin q

end Laplace.Multi
