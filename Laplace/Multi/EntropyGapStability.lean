/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MixtureCompensation
import Laplace.Multi.PinskerObservable

/-!
# Entropy-gap control of the reconstruction: non-radial boundary stability

Unrestricted convergence of responses to a finite-rate boundary response does not force convergence
of the reconstructions. Convergence of the responses *together with convergence of the visible
information* does. Two ingredients:

* the rate `𝓘 = genRate` is lower semicontinuous (`lowerSemicontinuous_genRate`), being a supremum
  of continuous affine functions;
* the **entropy-gap inequality** (`ofReal_sq_sub_le_gap`): for finite-rate responses `A, B`, weights
  `a + b = 1`, and a bounded test `|F − c| ≤ L`,
  `ab (E_{Π(A)}F − E_{Π(B)}F)² / (2L²) ≤ a𝓘(A) + b𝓘(B) − 𝓘(aA + bB)`,
  from the mixture compensation identity (Jensen–Shannon) and Pinsker's inequality for bounded
  observables. No natural parameter at the boundary is needed.

Hence (`tendsto_integral_responseProjection_of_tendsto_genRate`): if finite-rate responses
`M_i → M_*` with `𝓘(M_i) → 𝓘(M_*) < ∞`, then `E_{Π(M_i)}F → E_{Π(M_*)}F` for every bounded `F`.
The natural completion topology of the reconstruction is that of `M ↦ (M, 𝓘(M))`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

section LSC

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]

/-- **The rate is lower semicontinuous** (a supremum of continuous affine functions). -/
theorem lowerSemicontinuous_genRate (ν : Measure X) (S : J → X → ℝ) :
    LowerSemicontinuous (genRate ν S) := by
  unfold genRate
  refine lowerSemicontinuous_iSup fun q ↦ Continuous.lowerSemicontinuous ?_
  refine ENNReal.continuous_ofReal.comp (Continuous.sub ?_ continuous_const)
  unfold dotJ
  exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_apply j)

end LSC

section Gap

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The response of a bounded observable to a mixture is the mixture of the responses. -/
theorem integral_mixture_eq (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (a b : ℝ≥0) {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x ∂(a • P + b • Q) = (a : ℝ) * (∫ x, F x ∂P) + (b : ℝ) * ∫ x, F x ∂Q := by
  have h1 : Integrable F (a • P) := (integrable_of_bdd_prob P hF).smul_measure ENNReal.coe_ne_top
  have h2 : Integrable F (b • Q) := (integrable_of_bdd_prob Q hF).smul_measure ENNReal.coe_ne_top
  rw [integral_add_measure h1 h2, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]

/-- **The entropy-gap inequality**: for finite-rate responses `A, B`, weights `a + b = 1` and a
bounded test `|F − c| ≤ L`,
`ab (E_{Π(A)}F − E_{Π(B)}F)²/(2L²) + 𝓘(aA + bB) ≤ a 𝓘(A) + b 𝓘(B)`. -/
theorem ofReal_sq_sub_le_gap {A B : J → ℝ} (hA : genRate ν S A ≠ ⊤) (hB : genRate ν S B ≠ ⊤)
    {a b : ℝ≥0} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0) {F : X → ℝ} (hF : Bdd F) {c L : ℝ}
    (hL : 0 < L) (hFc : ∀ x, |F x - c| ≤ L) :
    ENNReal.ofReal ((a : ℝ) * b * ((∫ x, F x ∂responseProjection hS ν A) -
        ∫ x, F x ∂responseProjection hS ν B) ^ 2 / (2 * L ^ 2)) +
      genRate ν S ((a : ℝ) • A + (b : ℝ) • B) ≤
      (a : ℝ≥0∞) * genRate ν S A + (b : ℝ≥0∞) * genRate ν S B := by
  have hPA := (responseProjection_spec hS ν hA).1
  have hPB := (responseProjection_spec hS ν hB).1
  obtain ⟨H, hH⟩ : ∃ H : Measure X,
      H = a • responseProjection hS ν A + b • responseProjection hS ν B := ⟨_, rfl⟩
  have hHP : IsProbabilityMeasure H := hH ▸ isProbabilityMeasure_mixture _ _ hab
  have hgap := genRate_mixture_gap hS ν hA hB hab ha hb
  rw [← hH] at hgap
  have hEH : ∫ x, F x ∂H = (a : ℝ) * (∫ x, F x ∂responseProjection hS ν A) +
      (b : ℝ) * ∫ x, F x ∂responseProjection hS ν B := by
    rw [hH]
    exact integral_mixture_eq _ _ a b hF
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (∫ x, F x ∂responseProjection hS ν A) -
      ∫ x, F x ∂responseProjection hS ν B := ⟨_, rfl⟩
  have habR : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have h1 : ENNReal.ofReal (((b : ℝ) * d) ^ 2 / (2 * L ^ 2)) ≤
      klDiv (responseProjection hS ν A) H := by
    have := pinsker_observable (responseProjection hS ν A) H hF hL hFc
    have e : (∫ x, F x ∂responseProjection hS ν A) - ∫ x, F x ∂H = (b : ℝ) * d := by
      rw [hEH, hd]
      have : (a : ℝ) = 1 - b := by linarith
      rw [this]
      ring
    rwa [e] at this
  have h2 : ENNReal.ofReal (((a : ℝ) * d) ^ 2 / (2 * L ^ 2)) ≤
      klDiv (responseProjection hS ν B) H := by
    have := pinsker_observable (responseProjection hS ν B) H hF hL hFc
    have e : (∫ x, F x ∂responseProjection hS ν B) - ∫ x, F x ∂H = -((a : ℝ) * d) := by
      rw [hEH, hd]
      have : (b : ℝ) = 1 - a := by linarith
      rw [this]
      ring
    rwa [e, neg_sq] at this
  have e : (a : ℝ) * b * d ^ 2 / (2 * L ^ 2) =
      (a : ℝ) * (((b : ℝ) * d) ^ 2 / (2 * L ^ 2)) +
        (b : ℝ) * (((a : ℝ) * d) ^ 2 / (2 * L ^ 2)) := by
    have : (b : ℝ) = 1 - a := by linarith
    rw [this]
    ring
  rw [← hd, e, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg, ← ENNReal.coe_nnreal_eq,
    ← ENNReal.coe_nnreal_eq]
  calc (a : ℝ≥0∞) * ENNReal.ofReal (((b : ℝ) * d) ^ 2 / (2 * L ^ 2)) +
        (b : ℝ≥0∞) * ENNReal.ofReal (((a : ℝ) * d) ^ 2 / (2 * L ^ 2)) +
        genRate ν S ((a : ℝ) • A + (b : ℝ) • B)
      ≤ (a : ℝ≥0∞) * klDiv (responseProjection hS ν A) H +
        (b : ℝ≥0∞) * klDiv (responseProjection hS ν B) H +
        genRate ν S ((a : ℝ) • A + (b : ℝ) • B) := by gcongr
    _ ≤ ((a : ℝ≥0∞) * klDiv (responseProjection hS ν A) H +
          (b : ℝ≥0∞) * klDiv (responseProjection hS ν B) H +
          klDiv H (responseProjection hS ν ((a : ℝ) • A + (b : ℝ) • B))) +
        genRate ν S ((a : ℝ) • A + (b : ℝ) • B) := add_le_add le_self_add le_rfl
    _ = genRate ν S ((a : ℝ) • A + (b : ℝ) • B) +
        ((a : ℝ≥0∞) * klDiv (responseProjection hS ν A) H +
          (b : ℝ≥0∞) * klDiv (responseProjection hS ν B) H +
          klDiv H (responseProjection hS ν ((a : ℝ) • A + (b : ℝ) • B))) := add_comm _ _
    _ = (a : ℝ≥0∞) * genRate ν S A + (b : ℝ≥0∞) * genRate ν S B := hgap.symm

/-- **Entropy-gap stability of the reconstruction**: if finite-rate responses `M_i → M_*` with
`𝓘(M_i) → 𝓘(M_*) < ∞`, then `E_{Π(M_i)}F → E_{Π(M_*)}F` for every bounded observable `F`. No
interior hypothesis is made on `M_*` or on the approach. -/
theorem tendsto_integral_responseProjection_of_tendsto_genRate {ι : Type*} {l : Filter ι}
    {M : ι → J → ℝ} {M₀ : J → ℝ} (hM₀ : genRate ν S M₀ ≠ ⊤)
    (hfin : ∀ᶠ i in l, genRate ν S (M i) ≠ ⊤) (hM : Tendsto M l (𝓝 M₀))
    (hI : Tendsto (fun i ↦ genRate ν S (M i)) l (𝓝 (genRate ν S M₀))) {F : X → ℝ}
    (hF : Bdd F) :
    Tendsto (fun i ↦ ∫ x, F x ∂responseProjection hS ν (M i)) l
      (𝓝 (∫ x, F x ∂responseProjection hS ν M₀)) := by
  obtain ⟨hFm, L₀, hL₀⟩ := hF
  have hL₀0 : 0 ≤ L₀ := (abs_nonneg _).trans (hL₀ (Classical.arbitrary X))
  obtain ⟨L, hL, hFc⟩ : ∃ L : ℝ, 0 < L ∧ ∀ x, |F x - 0| ≤ L :=
    ⟨L₀ + 1, by linarith, fun x ↦ by rw [sub_zero]; linarith [hL₀ x]⟩
  -- the midpoint weights
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, a = 2⁻¹ := ⟨_, rfl⟩
  have haa : a + a = 1 := by
    rw [ha]
    ext
    push_cast
    norm_num
  have ha0 : a ≠ 0 := by rw [ha]; exact inv_ne_zero two_ne_zero
  have haR : (0 : ℝ) < a := by rw [ha]; positivity
  have haa' : (a : ℝ≥0∞) + a = 1 := by rw [← ENNReal.coe_add, haa, ENNReal.coe_one]
  -- the midpoints converge to `M₀`
  obtain ⟨mid, hmid⟩ : ∃ mid : ι → J → ℝ, mid = fun i ↦ (a : ℝ) • M i + (a : ℝ) • M₀ := ⟨_, rfl⟩
  have hmidt : Tendsto mid l (𝓝 M₀) := by
    have h := (hM.const_smul (a : ℝ)).add (tendsto_const_nhds (x := (a : ℝ) • M₀))
    have hlim : (a : ℝ) • M₀ + (a : ℝ) • M₀ = M₀ := by
      rw [← add_smul, ← NNReal.coe_add, haa, NNReal.coe_one, one_smul]
    rw [hlim] at h
    rw [hmid]
    exact h
  -- the entropy gap tends to zero
  obtain ⟨G, hG⟩ : ∃ G : ι → ℝ≥0∞, G = fun i ↦
      (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ - genRate ν S (mid i) :=
    ⟨_, rfl⟩
  have hup : Tendsto (fun i ↦ (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀) l
      (𝓝 (genRate ν S M₀)) := by
    have h1 : Tendsto (fun i ↦ (a : ℝ≥0∞) * genRate ν S (M i)) l
        (𝓝 ((a : ℝ≥0∞) * genRate ν S M₀)) :=
      ENNReal.Tendsto.const_mul hI (Or.inr ENNReal.coe_ne_top)
    have h := h1.add (tendsto_const_nhds (x := (a : ℝ≥0∞) * genRate ν S M₀))
    rwa [← add_mul, haa', one_mul] at h
  have hlow : ∀ y < genRate ν S M₀, ∀ᶠ i in l, y < genRate ν S (mid i) := fun y hy ↦
    hmidt.eventually (lowerSemicontinuous_genRate ν S M₀ y hy)
  have hG0 : Tendsto G l (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
    have h1 : ∀ᶠ i in l, (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ ≤
        genRate ν S M₀ + ε / 2 :=
      hup.eventually (Iic_mem_nhds (ENNReal.lt_add_right hM₀ hε2))
    have h2 : ∀ᶠ i in l, genRate ν S M₀ ≤ genRate ν S (mid i) + ε / 2 := by
      by_cases h0 : genRate ν S M₀ ≤ ε / 2
      · exact Eventually.of_forall fun i ↦ h0.trans le_add_self
      · push Not at h0
        have hy : genRate ν S M₀ - ε / 2 < genRate ν S M₀ :=
          ENNReal.sub_lt_self hM₀ (pos_of_gt h0).ne' hε2
        filter_upwards [hlow _ hy] with i hi
        exact tsub_le_iff_right.1 hi.le
    filter_upwards [h1, h2] with i h1 h2
    rw [hG]
    calc (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ - genRate ν S (mid i)
        ≤ (genRate ν S M₀ + ε / 2) - genRate ν S (mid i) := tsub_le_tsub_right h1 _
      _ ≤ ε := by
          rw [tsub_le_iff_right]
          calc genRate ν S M₀ + ε / 2 ≤ (genRate ν S (mid i) + ε / 2) + ε / 2 :=
                add_le_add h2 le_rfl
            _ = ε + genRate ν S (mid i) := by rw [add_assoc, ENNReal.add_halves, add_comm]
  -- the gap controls the observable defect
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 * L ^ 2 / ((a : ℝ) * a) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hbound : ∀ᶠ i in l, |(∫ x, F x ∂responseProjection hS ν (M i)) -
      ∫ x, F x ∂responseProjection hS ν M₀| ≤ √(κ * (G i).toReal) := by
    filter_upwards [hfin] with i hfi
    have h := ofReal_sq_sub_le_gap hS ν hfi hM₀ haa ha0 ha0 ⟨hFm, L₀, hL₀⟩ hL hFc
    have emid : (a : ℝ) • M i + (a : ℝ) • M₀ = mid i := by rw [hmid]
    rw [emid] at h
    have hne : (a : ℝ≥0∞) * genRate ν S (M i) + (a : ℝ≥0∞) * genRate ν S M₀ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hfi,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hM₀⟩
    have hmidne : genRate ν S (mid i) ≠ ⊤ := ne_top_of_le_ne_top hne (le_add_self.trans h)
    have hGi : ENNReal.ofReal ((a : ℝ) * a * ((∫ x, F x ∂responseProjection hS ν (M i)) -
        ∫ x, F x ∂responseProjection hS ν M₀) ^ 2 / (2 * L ^ 2)) ≤ G i := by
      rw [hG]
      exact ENNReal.le_sub_of_add_le_right hmidne h
    have hGne : G i ≠ ⊤ := by
      rw [hG]
      exact ENNReal.sub_ne_top hne
    have hr := (ENNReal.ofReal_le_iff_le_toReal hGne).1 hGi
    refine Real.abs_le_sqrt ?_
    rw [hκ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ 2)).1 hr
    linarith
  have hGr : Tendsto (fun i ↦ (G i).toReal) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG0
    rw [ENNReal.toReal_zero] at this
    exact this
  have hsq : Tendsto (fun i ↦ √(κ * (G i).toReal)) l (𝓝 0) := by
    have h2 : Tendsto (fun i ↦ κ * (G i).toReal) l (𝓝 0) := by
      have := hGr.const_mul κ
      rwa [mul_zero] at this
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
    (Eventually.of_forall fun i ↦ norm_nonneg _) ?_
  filter_upwards [hbound] with i hi
  rw [Real.norm_eq_abs]
  exact hi

end Gap

end Laplace.Multi
