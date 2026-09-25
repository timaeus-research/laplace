/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MixtureBridge
import Laplace.Multi.ConditioningCertificate

/-!
# Endpoint convergence of the canonical representatives

The mixture bridge (`MixtureBridge`) carries the rate along the straight mean path
`M_s = (1 − s) m₀ + s M` from the featureless response `m₀ = E_ν S` to a response `M` of finite
rate, and shows `𝓘(M_s) → 𝓘(M)`. This file shows that the *canonical representatives* converge as
well, in Kullback–Leibler divergence, with an explicit certificate:

* `klDiv_tilted_right_eq`: for a law `ρ ≪ ν` of finite information and a bounded `f`,
  `KL(ρ ‖ ν_f) = KL(ρ ‖ ν) − E_ρ f + log E_ν e^f`.
* `genRate_eq_zero_iff`: **zero information characterises the featureless response**,
  `𝓘_ν(M) = 0 ↔ M = E_ν S`.
* `responseProjection_eq_tilted`: a response in the relative interior of the moment body is
  represented by a bounded exponential tilt of `ν` itself (the root of the conditioning chain).
* `klDiv_responseProjection_segment_le`: **the endpoint certificate**
  `KL(Π(M) ‖ Π(M_s)) ≤ 𝓘(M) − 𝓘(M_s)` for `0 < s < 1`.
* `tendsto_klDiv_responseProjection_segment`: `KL(Π(M) ‖ Π(M_s)) → 0` as `s ↑ 1`.

The certificate is the bounded-tilt identity above, applied to `Π(M_s) = ν_{f_s}`, together with the
sign of the pairing `⟨θ_s, M − M_s⟩`, which is controlled by Gibbs' inequality at the featureless
law: `⟨θ_s, M_s − m₀⟩ = −(𝓘(M_s) + KL(ν ‖ Π(M_s))) ≤ 0`. No Pinsker inequality and no
differentiability of the chart is needed. The divergence in the other order, `KL(Π(M_s) ‖ Π(M))`,
can be infinite for every `s < 1` when `Π(M)` lives on a proper face, so the order is essential.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X]

section Tilt

variable (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The Kullback–Leibler divergence to a bounded tilt**: for a law `ρ ≪ ν` of finite
information, `KL(ρ ‖ ν_f) = KL(ρ ‖ ν) − E_ρ f + log E_ν e^f`. -/
theorem klDiv_tilted_right_eq (ρ : Measure X) [IsProbabilityMeasure ρ] (hρν : ρ ≪ ν)
    (hfin : klDiv ρ ν ≠ ⊤) {f : X → ℝ} (hf : Bdd f) :
    klDiv ρ (ν.tilted f) = ENNReal.ofReal
      ((klDiv ρ ν).toReal - ∫ x, f x ∂ρ + Real.log (∫ x, Real.exp (f x) ∂ν)) := by
  have hfν := integrable_exp_of_bdd ν hf
  have hint : Integrable (llr ρ ν) ρ := (klDiv_ne_top_iff.1 hfin).2
  have hac : ρ ≪ ν.tilted f := hρν.trans (absolutelyContinuous_tilted hfν)
  have hint' := integrable_llr_tilted_right hρν (integrable_of_bdd_prob ρ hf) hint hfν
  have hprob : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hnn := integral_llr_add_sub_measure_univ_nonneg hρν hint
  rw [klDiv_of_ac_of_integrable hac hint', klDiv_of_ac_of_integrable hρν hint,
    integral_llr_tilted_right hρν (integrable_of_bdd_prob ρ hf) hfν hint]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hnn ⊢
  rw [ENNReal.toReal_ofReal hnn]
  congr 1
  ring

end Tilt

section Endpoint

variable [Nonempty X] {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Zero information characterises the featureless response**: `𝓘_ν(M) = 0 ↔ M = E_ν S`. -/
theorem genRate_eq_zero_iff (M : J → ℝ) :
    genRate ν S M = 0 ↔ M = fun i ↦ ∫ x, S i x ∂ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ genRate_mean_eq_zero ν hS⟩
  have hfin : genRate ν S M ≠ ⊤ := by
    rw [h]
    exact ENNReal.zero_ne_top
  obtain ⟨hP, hM, hkl, -⟩ := responseProjection_spec hS ν hfin
  have := hP
  rw [h, klDiv_eq_zero_iff] at hkl
  rw [← hM, hkl]

/-- **A response in the relative interior is represented by a bounded tilt of `ν` itself.** -/
theorem responseProjection_eq_tilted {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ θ : J → ℝ, responseProjection hS ν M = ν.tilted (fun x ↦ -(1 : ℝ) * dirLoss S θ x) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂ν := by simp
  have hπi : Integrable (fun _ : X ↦ (1 : ℝ)) ν := integrable_const _
  have hπ : ∀ x, (0 : ℝ) < (fun _ : X ↦ (1 : ℝ)) x := fun _ ↦ one_pos
  have hrel' :
      M ∈ intrinsicInterior ℝ (momentBody (faceMeasure ν Set.univ) (fun _ ↦ (1 : ℝ)) S) := by
    rw [faceMeasure_univ ν]
    exact hrel
  obtain ⟨θ, -, hθ⟩ := responseProjection_eq_of_exposedChain hS ν ExposedChain.root hrel'
  refine ⟨θ, ?_⟩
  rw [hθ, faceMeasure_univ ν,
    familyMeasure_eq_tilted measurable_const hπi hπ hπpos measurable_const h0 hS one_pos θ,
    familyMeasure_one_zero ν S]

/-- **The endpoint certificate**: along the straight mean path from the featureless response to a
response `M` of finite rate, `KL(Π(M) ‖ Π(M_s)) ≤ 𝓘(M) − 𝓘(M_s)` for `0 < s < 1`. -/
theorem klDiv_responseProjection_segment_le {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    klDiv (responseProjection hS ν M)
        (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) ≤
      genRate ν S M - genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) := by
  obtain ⟨hQP, hQM, hQkl, -⟩ := responseProjection_spec hS ν hfin
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = responseProjection hS ν M := ⟨_, rfl⟩
  rw [← hQ] at hQM hQkl ⊢
  have hQP' : IsProbabilityMeasure Q := by
    rw [hQ]
    exact hQP
  have hQkl' : klDiv Q ν ≠ ⊤ := by
    rw [hQkl]
    exact hfin
  have hQν : Q ≪ ν := (klDiv_ne_top_iff.1 hQkl').1
  -- the path point lies in the relative interior, so its representative is a tilt of `ν`
  have hrel := segment_mem_intrinsicInterior hS ν Q hQν hs0.le hs1
  rw [hQM] at hrel
  obtain ⟨θ, hθ⟩ := responseProjection_eq_tilted hS ν hrel
  obtain ⟨f, hf⟩ : ∃ f : X → ℝ, f = fun x ↦ -(1 : ℝ) * dirLoss S θ x := ⟨_, rfl⟩
  rw [← hf] at hθ
  have hbdd : Bdd f := hf ▸ Bdd.const_mul (-1) (bdd_dirLoss hS θ)
  have hfν := integrable_exp_of_bdd ν hbdd
  have hsP : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  obtain ⟨Ms, hMs⟩ : ∃ Ms : J → ℝ, Ms = (1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M := ⟨_, rfl⟩
  rw [← hMs] at hθ ⊢
  have hfinS : genRate ν S Ms ≠ ⊤ := by
    intro h
    have := genRate_segment_le hS ν hs0.le hs1.le (M := M)
    rw [← hMs, h, top_le_iff, ENNReal.mul_eq_top] at this
    rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hfin h2
    · exact ENNReal.ofReal_ne_top h1
  obtain ⟨-, hsM, hskl, -⟩ := responseProjection_spec hS ν hfinS
  rw [hθ] at hsM hskl ⊢
  -- the three means of `f`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (∫ x, Real.exp (f x) ∂ν) := ⟨_, rfl⟩
  have hmean : ∀ ρ : Measure X, [IsProbabilityMeasure ρ] →
      ∫ x, f x ∂ρ = -dotJ θ (fun i ↦ ∫ x, S i x ∂ρ) := by
    intro ρ _
    rw [hf, integral_const_mul, ← dotJ_integral_eq ρ hS θ]
    ring
  have hQmean : ∫ x, f x ∂Q = -dotJ θ M := by rw [hmean Q, hQM]
  have hsmean : ∫ x, f x ∂ν.tilted f = -dotJ θ Ms := by rw [hmean (ν.tilted f), hsM]
  have hνmean : ∫ x, f x ∂ν = -dotJ θ (fun i ↦ ∫ x, S i x ∂ν) := hmean ν
  -- the rate of the path point and Gibbs' inequality at the featureless law
  have hb : 0 ≤ -dotJ θ Ms - L := by
    have := integral_sub_log_nonneg ν hbdd
    rwa [hsmean, ← hL] at this
  have hν0 : -dotJ θ (fun i ↦ ∫ x, S i x ∂ν) - L ≤ 0 := by
    have hint0 : Integrable (llr ν ν) ν := (integrable_const (0 : ℝ)).congr (llr_self ν).symm
    have := integral_sub_log_le_toReal_klDiv ν ν (fun _ h ↦ h) hint0 hbdd
    rw [klDiv_self, ENNReal.toReal_zero, hνmean, ← hL] at this
    linarith
  have hrate : genRate ν S Ms = ENNReal.ofReal (-dotJ θ Ms - L) := by
    rw [← hskl, klDiv_tilted_eq ν hbdd, hsmean, hL]
  -- the divergence to the path representative
  have hKL : klDiv Q (ν.tilted f) =
      ENNReal.ofReal ((genRate ν S M).toReal + dotJ θ M + L) := by
    rw [klDiv_tilted_right_eq ν Q hQν hQkl' hbdd, hQkl, hQmean, hL]
    ring_nf
  -- linearity of the pairing along the segment
  have hlin : dotJ θ Ms = (1 - s) * dotJ θ (fun i ↦ ∫ x, S i x ∂ν) + s * dotJ θ M := by
    rw [hMs]
    simp only [dotJ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hMle : dotJ θ M ≤ dotJ θ (fun i ↦ ∫ x, S i x ∂ν) := by
    have h1 : s * (dotJ θ M - dotJ θ (fun i ↦ ∫ x, S i x ∂ν)) ≤ 0 := by linarith
    nlinarith
  have hI : genRate ν S M = ENNReal.ofReal (genRate ν S M).toReal :=
    (ENNReal.ofReal_toReal hfin).symm
  rw [hKL, hrate]
  nth_rewrite 2 [hI]
  rw [← ENNReal.ofReal_sub _ hb]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (1 - s) * (dotJ θ (fun i ↦ ∫ x, S i x ∂ν) - dotJ θ M) ≥ 0 :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **Endpoint convergence of the canonical representatives**: `KL(Π(M) ‖ Π(M_s)) → 0` as
`s ↑ 1` along the straight mean path from the featureless response. -/
theorem tendsto_klDiv_responseProjection_segment {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    Tendsto (fun s : ℝ ↦ klDiv (responseProjection hS ν M)
        (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)))
      (𝓝[<] 1) (𝓝 0) := by
  have hup : Tendsto (fun s : ℝ ↦ genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) (𝓝[<] 1)
      (𝓝 (genRate ν S M - genRate ν S M)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_genRate_segment hS ν hfin) (Or.inl hfin)
  rw [tsub_self] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
  exact klDiv_responseProjection_segment_le hS ν hfin hs.1 hs.2

end Endpoint

end Laplace.Multi
