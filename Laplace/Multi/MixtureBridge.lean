/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DataResponseMap

/-!
# The mixture bridge to arbitrary finite-entropy data

Let `D` be any probability law of finite information `KL(D ‖ ν) < ∞` and `M_D = E_D S` its
response, `m₀ = E_ν S` the featureless response. The **straight mean path**
`M_s = (1 − s) m₀ + s M_D` reaches `M_D` from `m₀`:

* **the divergence is convex in its first argument** (`klDiv_mixture_le`, from the convexity of
  `klFun` and the Radon–Nikodym derivative of a mixture), hence **the rate is convex along the
  path**: `𝓘(M_s) ≤ s 𝓘(M_D)` (`genRate_segment_le`) and `s ↦ 𝓘(M_s)` is monotone on `[0, 1]`
  (`genRate_segment_mono`);
* for `s < 1` the mixture law `(1 − s) ν + s D` is equivalent to `ν`, so `M_s` lies in the relative
  interior of the moment body (`segment_mem_intrinsicInterior`): the path stays in the ordinary
  intrinsic chart until the endpoint;
* at the endpoint the rate converges, `𝓘(M_s) → 𝓘(M_D)` as `s → 1⁻`
  (`tendsto_genRate_segment`), by lower semicontinuity from below and convexity from above.

Every finite-information data response is thus reached by a straight mean path whose canonical
representatives stay in the intrinsic chart and whose information cost increases continuously to
that of the completed representative at the endpoint. (The total-variation convergence of the
representatives themselves needs Pinsker's inequality, not yet in Mathlib.)
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X]

section Convexity

variable (ν : Measure X) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem mixture_absolutelyContinuous {ν' ρ : Measure X} (hν' : ν' ≪ ν) (hρ : ρ ≪ ν) (a b : ℝ≥0) :
    a • ν' + b • ρ ≪ ν := by
  intro A hA
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hν' hA, hρ hA]
  simp

theorem isProbabilityMeasure_mixture (ν' ρ : Measure X) [IsProbabilityMeasure ν']
    [IsProbabilityMeasure ρ] {a b : ℝ≥0} (hab : a + b = 1) :
    IsProbabilityMeasure (a • ν' + b • ρ) := by
  refine ⟨?_⟩
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ]
  simp only [ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add, hab, ENNReal.coe_one]

/-- **Convexity of the Kullback–Leibler divergence in its first argument.** -/
theorem klDiv_mixture_le (ν' ρ : Measure X) [IsProbabilityMeasure ν'] [IsProbabilityMeasure ρ]
    (hν' : ν' ≪ ν) (hρ : ρ ≪ ν) {a b : ℝ≥0} (hab : a + b = 1) :
    klDiv (a • ν' + b • ρ) ν ≤ (a : ℝ≥0∞) * klDiv ν' ν + (b : ℝ≥0∞) * klDiv ρ ν := by
  have hmix := mixture_absolutelyContinuous ν hν' hρ a b
  rw [klDiv_eq_lintegral_klFun_of_ac hmix, klDiv_eq_lintegral_klFun_of_ac hν',
    klDiv_eq_lintegral_klFun_of_ac hρ]
  have hrn : (a • ν' + b • ρ).rnDeriv ν =ᵐ[ν] a • ν'.rnDeriv ν + b • ρ.rnDeriv ν := by
    filter_upwards [Measure.rnDeriv_add' (a • ν') (b • ρ) ν, Measure.rnDeriv_smul_left' ν' ν a,
      Measure.rnDeriv_smul_left' ρ ν b] with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, hx3]
    rfl
  have hm1 : Measurable fun x ↦ ENNReal.ofReal (klFun (ν'.rnDeriv ν x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (ν'.rnDeriv ν x).toReal).ennreal_ofReal
  have hm2 : Measurable fun x ↦ ENNReal.ofReal (klFun (ρ.rnDeriv ν x).toReal) :=
    (by fun_prop : Measurable fun x ↦ klFun (ρ.rnDeriv ν x).toReal).ennreal_ofReal
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  calc ∫⁻ x, ENNReal.ofReal (klFun ((a • ν' + b • ρ).rnDeriv ν x).toReal) ∂ν
      ≤ ∫⁻ x, ((a : ℝ≥0∞) * ENNReal.ofReal (klFun (ν'.rnDeriv ν x).toReal) +
          (b : ℝ≥0∞) * ENNReal.ofReal (klFun (ρ.rnDeriv ν x).toReal)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hrn, Measure.rnDeriv_lt_top ν' ν, Measure.rnDeriv_lt_top ρ ν]
          with x hx hx1 hx2
        rw [hx, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
        simp only [ENNReal.smul_def, smul_eq_mul]
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hx1.ne)
            (ENNReal.mul_ne_top ENNReal.coe_ne_top hx2.ne),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
        have hconv := convexOn_klFun.2
          (Set.mem_Ici.2 (ENNReal.toReal_nonneg (a := ν'.rnDeriv ν x)))
          (Set.mem_Ici.2 (ENNReal.toReal_nonneg (a := ρ.rnDeriv ν x))) a.coe_nonneg b.coe_nonneg
          hab'
        simp only [smul_eq_mul] at hconv
        calc ENNReal.ofReal (klFun ((a : ℝ) * (ν'.rnDeriv ν x).toReal +
              (b : ℝ) * (ρ.rnDeriv ν x).toReal))
            ≤ ENNReal.ofReal ((a : ℝ) * klFun (ν'.rnDeriv ν x).toReal +
                (b : ℝ) * klFun (ρ.rnDeriv ν x).toReal) := ENNReal.ofReal_le_ofReal hconv
          _ = (a : ℝ≥0∞) * ENNReal.ofReal (klFun (ν'.rnDeriv ν x).toReal) +
                (b : ℝ≥0∞) * ENNReal.ofReal (klFun (ρ.rnDeriv ν x).toReal) := by
              rw [ENNReal.ofReal_add (mul_nonneg a.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg))
                  (mul_nonneg b.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg)),
                ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
                ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    _ = (a : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (klFun (ν'.rnDeriv ν x).toReal) ∂ν +
          (b : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (klFun (ρ.rnDeriv ν x).toReal) ∂ν := by
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]

end Convexity

section Bridge

variable [Nonempty X] {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- The response of a mixture is the mixture of the responses. -/
theorem mean_mixture (ν' ρ : Measure X) [IsProbabilityMeasure ν'] [IsProbabilityMeasure ρ]
    (a b : ℝ≥0) :
    (fun i ↦ ∫ x, S i x ∂(a • ν' + b • ρ)) =
      (a : ℝ) • (fun i ↦ ∫ x, S i x ∂ν') + (b : ℝ) • (fun i ↦ ∫ x, S i x ∂ρ) := by
  funext i
  have h1 : Integrable (S i) (a • ν') :=
    (integrable_of_bdd_prob ν' (hS i)).smul_measure ENNReal.coe_ne_top
  have h2 : Integrable (S i) (b • ρ) :=
    (integrable_of_bdd_prob ρ (hS i)).smul_measure ENNReal.coe_ne_top
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    integral_add_measure h1 h2, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]

/-- **Convexity of the rate along the segment from the featureless response**:
`𝓘((1 − s) m₀ + s M) ≤ s 𝓘(M)` for `s ∈ [0, 1]`. -/
theorem genRate_segment_le {M : J → ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) ≤ ENNReal.ofReal s * genRate ν S M := by
  by_cases hfin : genRate ν S M = ⊤
  · rcases eq_or_ne s 0 with hs | hs
    · rw [hs, zero_smul, add_zero, sub_zero, one_smul, genRate_mean_eq_zero ν hS]
      exact zero_le
    · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (lt_of_le_of_ne hs0 (Ne.symm hs))).ne']
      exact le_top
  obtain ⟨hρP, hρM, hρkl, -⟩ := responseProjection_spec hS ν hfin
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (a : ℝ) = 1 - s := ⟨⟨1 - s, by linarith⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, (b : ℝ) = s := ⟨⟨s, hs0⟩, rfl⟩
  have hab : a + b = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, ha, hb, NNReal.coe_one]
    ring
  have hP := isProbabilityMeasure_mixture ν (responseProjection hS ν M) hab
  have hac : responseProjection hS ν M ≪ ν := (klDiv_ne_top_iff.1 (by rw [hρkl]; exact hfin)).1
  have hmean : (fun i ↦ ∫ x, S i x ∂(a • ν + b • responseProjection hS ν M)) =
      (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M := by
    rw [mean_mixture hS ν (responseProjection hS ν M) a b, hρM, ha, hb]
  calc genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)
      ≤ klDiv (a • ν + b • responseProjection hS ν M) ν := by
        rw [← entropyProj_eq_genRate hS ν]
        exact entropyProj_le_klDiv ν _ hmean
    _ ≤ (a : ℝ≥0∞) * klDiv ν ν + (b : ℝ≥0∞) * klDiv (responseProjection hS ν M) ν :=
        klDiv_mixture_le ν ν (responseProjection hS ν M) (fun _ h ↦ h) hac hab
    _ = ENNReal.ofReal s * genRate ν S M := by
        rw [klDiv_self, mul_zero, zero_add, hρkl, ← hb, ENNReal.ofReal_coe_nnreal]

/-- **The rate is monotone along the straight mean path.** -/
theorem genRate_segment_mono {M : J → ℝ} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) ≤
      genRate ν S ((1 - t) • (fun i ↦ ∫ x, S i x ∂ν) + t • M) := by
  rcases eq_or_ne t 0 with ht | ht
  · have hs : s = 0 := le_antisymm (ht ▸ hst) hs0
    rw [hs, ht]
  have ht0 : 0 < t := lt_of_le_of_ne (hs0.trans hst) (Ne.symm ht)
  -- `M_s` is the point at parameter `s/t` of the segment from `m₀` to `M_t`
  have e : (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M =
      (1 - s / t) • (fun i ↦ ∫ x, S i x ∂ν) +
        (s / t) • ((1 - t) • (fun i ↦ ∫ x, S i x ∂ν) + t • M) := by
    have : (s / t) * t = s := div_mul_cancel₀ s ht
    rw [smul_add, smul_smul, smul_smul, this, ← add_assoc, ← add_smul]
    congr 1
    congr 1
    field_simp
    ring
  rw [e]
  calc genRate ν S ((1 - s / t) • (fun i ↦ ∫ x, S i x ∂ν) +
        (s / t) • ((1 - t) • (fun i ↦ ∫ x, S i x ∂ν) + t • M))
      ≤ ENNReal.ofReal (s / t) * genRate ν S ((1 - t) • (fun i ↦ ∫ x, S i x ∂ν) + t • M) :=
        genRate_segment_le hS ν (div_nonneg hs0 ht0.le) ((div_le_one ht0).2 hst)
    _ ≤ 1 * genRate ν S ((1 - t) • (fun i ↦ ∫ x, S i x ∂ν) + t • M) := by
        gcongr
        exact ENNReal.ofReal_le_one.2 ((div_le_one ht0).2 hst)
    _ = _ := one_mul _

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- **The straight mean path stays in the intrinsic chart until the endpoint.** -/
theorem segment_mem_intrinsicInterior (D : Measure X) [IsProbabilityMeasure D] (hD : D ≪ ν)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • (fun i ↦ ∫ x, S i x ∂D) ∈
      intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (a : ℝ) = 1 - s := ⟨⟨1 - s, by linarith⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, (b : ℝ) = s := ⟨⟨s, hs0⟩, rfl⟩
  have hab : a + b = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, ha, hb, NNReal.coe_one]
    ring
  have hP := isProbabilityMeasure_mixture ν D hab
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, ha]
    linarith
  have hac : a • ν + b • D ≪ ν := mixture_absolutelyContinuous ν (fun _ h ↦ h) hD a b
  have hac' : ν ≪ a • ν + b • D := by
    intro A hA
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, add_eq_zero] at hA
    simp only [ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hA
    rcases hA.1 with h | h
    · exact absurd h ha0
    · exact h
  have := mean_mem_intrinsicInterior_of_equiv hS ν (a • ν + b • D) hac hac'
  rw [mean_mixture hS ν D a b, ha, hb] at this
  exact this

/-- **The rate converges at the endpoint of the straight mean path**: `𝓘(M_s) → 𝓘(M_D)` as
`s → 1⁻`, for a response of finite rate. -/
theorem tendsto_genRate_segment {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    Tendsto (fun s : ℝ ↦ genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) (𝓝[<] 1)
      (𝓝 (genRate ν S M)) := by
  have hpath : Tendsto (fun s : ℝ ↦ (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) (𝓝[<] 1)
      (𝓝 M) := by
    have h : Continuous fun s : ℝ ↦ (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M := by fun_prop
    have h1 : Tendsto (fun s : ℝ ↦ (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) (𝓝[<] 1)
        (𝓝 ((1 - (1 : ℝ)) • (fun i ↦ ∫ x, S i x ∂ν) + (1 : ℝ) • M)) :=
      (h.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using h1
  have hlsc := lowerSemicontinuous_rateFun (μ := ν) (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    (R := S) (t := 1)
  rw [tendsto_order]
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- lower semicontinuity
    have hc' : c < rateFun ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 M := by
      rw [← genRate_eq_rateFun ν S M]
      exact hc
    have h := hlsc M c hc'
    filter_upwards [hpath.eventually h] with s hs
    rw [genRate_eq_rateFun ν S]
    exact hs
  · -- convexity: `𝓘(M_s) ≤ s 𝓘(M) < c` eventually
    have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal s * genRate ν S M) (𝓝[<] 1)
        (𝓝 (genRate ν S M)) := by
      have h1 : Tendsto (fun s : ℝ ↦ ENNReal.ofReal s) (𝓝[<] 1) (𝓝 (ENNReal.ofReal 1)) :=
        (ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hfin)
      rwa [ENNReal.ofReal_one, one_mul] at h2
    filter_upwards [hlim.eventually (gt_mem_nhds hc), Ioo_mem_nhdsLT (zero_lt_one' ℝ)]
      with s hs hs01
    exact lt_of_le_of_lt (genRate_segment_le hS ν hs01.1.le hs01.2.le) hs

end Bridge

end Laplace.Multi
