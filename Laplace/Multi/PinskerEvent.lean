/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.StraightPathAtlas

/-!
# Pinsker's inequality for events, and convergence of all event probabilities along the bridge

Mathlib has no Pinsker inequality. The landed second-order bound on cumulant generating functions
gives it directly for events: a statistic with values in an interval of length `2r` has tilted
variance at most `r²` under every tilt, so `log E_η e^g ≤ E_η g + r²/2` (Hoeffding's lemma in the
form `log_integral_exp_le_of_ae_abs_sub_le`), and the Donsker–Varadhan inequality at
`g = 4(μ(A) − η(A)) 1_A` yields

  `2 (μ(A) − η(A))² ≤ KL(μ ‖ η)`   (`pinsker_event`).

Along the straight bridge to a response of finite rate this converts the endpoint certificate into a
uniform quantitative statement for every event, `2 (Π(M)(A) − Π(M_s)(A))² ≤ 𝓘(M) − 𝓘(M_s)`
(`sq_real_responseProjection_segment_le`), hence `Π(M_s)(A) → Π(M)(A)` as `s ↑ 1`
(`tendsto_real_responseProjection_segment`): the canonical representatives converge in every event
probability, not only in information.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Hoeffding

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (η : Measure X) [IsProbabilityMeasure η]

/-- **Hoeffding's lemma** in cumulant form: a bounded statistic within distance `r` of a centre has
`log E_η e^g ≤ E_η g + r² / 2`. -/
theorem log_integral_exp_le_of_ae_abs_sub_le {g : X → ℝ} (hg : Bdd g) {c r : ℝ}
    (hgr : ∀ᵐ x ∂η, |g x - c| ≤ r) :
    Real.log (∫ x, Real.exp (g x) ∂η) ≤ (∫ x, g x ∂η) + r ^ 2 / 2 := by
  refine log_integral_exp_le_of_var_le η hg (K := r ^ 2) fun s _ ↦ ?_
  have hP : IsProbabilityMeasure (η.tilted (fun x ↦ s * g x)) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd η (Bdd.const_mul s hg))
  refine (lawCov_self_le_integral_sq (η.tilted (fun x ↦ s * g x)) hg c).trans ?_
  have hbdd : Bdd fun x ↦ (g x - c) * (g x - c) :=
    (hg.sub (Bdd.const c)).mul (hg.sub (Bdd.const c))
  calc ∫ x, (g x - c) * (g x - c) ∂η.tilted (fun x ↦ s * g x)
      ≤ ∫ _, r ^ 2 ∂η.tilted (fun x ↦ s * g x) := by
        refine integral_mono_ae (integrable_of_bdd_prob _ hbdd) (integrable_const _) ?_
        filter_upwards [(tilted_absolutelyContinuous η _).ae_le hgr] with x hx
        have h0 : 0 ≤ |g x - c| := abs_nonneg _
        calc (g x - c) * (g x - c) = |g x - c| * |g x - c| := (abs_mul_abs_self _).symm
          _ ≤ r * r := mul_self_le_mul_self h0 hx
          _ = r ^ 2 := (sq r).symm
    _ = r ^ 2 := by
        rw [integral_const]
        simp [measureReal_def]

end Hoeffding

section Pinsker

variable {X : Type*} [MeasurableSpace X] [Nonempty X]

/-- **Pinsker's inequality for events**: `2 (μ(A) − η(A))² ≤ KL(μ ‖ η)`. -/
theorem pinsker_event (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    {A : Set X} (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - η.real A) ^ 2) ≤ klDiv μ η := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = μ.real A - η.real A := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : X → ℝ, g = A.indicator (fun _ ↦ 4 * d) := ⟨_, rfl⟩
  have hgb : Bdd g := ⟨hg ▸ measurable_const.indicator hA, |4 * d|, fun x ↦ by
    rw [hg]
    simpa [Real.norm_eq_abs] using
      norm_indicator_le_norm_self (s := A) (f := fun _ : X ↦ 4 * d) (a := x)⟩
  have hDV := ofReal_integral_sub_log_le_klDiv η μ hgb
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hDV
  have hμ : ∫ x, g x ∂μ = μ.real A * (4 * d) := by
    rw [hg, integral_indicator_const _ hA, smul_eq_mul]
  have hη : ∫ x, g x ∂η = η.real A * (4 * d) := by
    rw [hg, integral_indicator_const _ hA, smul_eq_mul]
  have hlog : Real.log (∫ x, Real.exp (g x) ∂η) ≤ (∫ x, g x ∂η) + |2 * d| ^ 2 / 2 := by
    refine log_integral_exp_le_of_ae_abs_sub_le η hgb (c := 2 * d) (Eventually.of_forall fun x ↦ ?_)
    rw [hg]
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, show 4 * d - 2 * d = 2 * d by ring]
    · rw [Set.indicator_of_notMem hx, zero_sub, abs_neg]
  rw [sq_abs] at hlog
  rw [hμ]
  have hμA : μ.real A = d + η.real A := by linarith
  rw [hμA]
  nlinarith [hlog, hη]

end Pinsker

section Bridge

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- **Every event probability of the representatives is controlled by the information gap**:
`2 (Π(M)(A) − Π(M_s)(A))² ≤ 𝓘(M) − 𝓘(M_s)` for `0 < s < 1`. -/
theorem sq_real_responseProjection_segment_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {A : Set X}
    (hA : MeasurableSet A) :
    2 * ((responseProjection hS ν M).real A -
        (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).real A) ^ 2 ≤
      (genRate ν S M - genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).toReal := by
  have hP := (responseProjection_spec hS ν hfin).1
  have hfinS : genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M) ≠ ⊤ := by
    intro h
    have := genRate_segment_le hS ν hs0.le hs1.le (M := M)
    rw [h, top_le_iff, ENNReal.mul_eq_top] at this
    rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hfin h2
    · exact ENNReal.ofReal_ne_top h1
  have hPs := (responseProjection_spec hS ν hfinS).1
  have h := (pinsker_event (responseProjection hS ν M)
    (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) hA).trans
    (klDiv_responseProjection_segment_le hS ν hfin hs0 hs1)
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.sub_ne_top hfin)).1 h

/-- **The representatives converge in every event probability at the endpoint of the bridge.** -/
theorem tendsto_real_responseProjection_segment {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun s : ℝ ↦
        (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).real A)
      (𝓝[<] 1) (𝓝 ((responseProjection hS ν M).real A)) := by
  have hsub : Tendsto (fun s : ℝ ↦ genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)) (𝓝[<] 1) (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_genRate_segment hS ν hfin)
      (Or.inl hfin)
    rwa [tsub_self] at this
  have hup : Tendsto (fun s : ℝ ↦ (genRate ν S M -
      genRate ν S ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).toReal / 2) (𝓝[<] 1) (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsub).div_const 2
    simpa using this
  have hsq : Tendsto (fun s : ℝ ↦ ((responseProjection hS ν M).real A -
      (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).real A) ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ ↦ sq_nonneg _) ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
    have := sq_real_responseProjection_segment_le hS ν hfin hs.1 hs.2 hA
    linarith
  have habs : Tendsto (fun s : ℝ ↦ |(responseProjection hS ν M).real A -
      (responseProjection hS ν ((1 - s) • (fun i ↦ ∫ x, S i x ∂ν) + s • M)).real A|)
      (𝓝[<] 1) (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  have hd := (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have := (tendsto_const_nhds (x := (responseProjection hS ν M).real A)).sub hd
  simpa using this

end Bridge

end Laplace.Multi
