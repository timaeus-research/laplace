/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.BoxPeel

/-!
# Tangential integration of the normal block

First geometric bridge after the normal block (Astra #17). A continuous amplitude
`η : ℝ^t × ℝ^r → ℝ` depends on tangential variables `v` ranging over a compact set `K` with an
integrable density `q`, and on the normal variables `u`. Averaging over the tangential variables,

  `η̄(u) = ∫_K q(v) η(v,u) dv`,

produces a continuous normal amplitude (`continuous_tangentialAvg`, by dominated continuity, locally
in `u`), and Fubini identifies the tangentially integrated dressed normal moment with the dressed
normal moment of `η̄` (`integral_tangential_swap`). Applying the amplitude theorem once and
swapping again gives the **tangentially integrated normal-block asymptotic**

  `(∫_K q(v) I_{η(v,·)}(N) dv) / (N^{-λ}(log N)^{|J|-1}) → ∫_K q(v) amplitudeCoeff(η(v,·)) dv`

(`tangential_amplitude_tendsto`). Signed densities and amplitudes are allowed; the coefficient may
vanish by tangential cancellation, so asymptotic equivalence is only asserted when it is nonzero.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

variable {t r : ℕ}

/-- The tangential average `η̄(u) = ∫_K q(v) η(v,u) dv`. -/
noncomputable def tangentialAvg (K : Set (Fin t → ℝ)) (q : (Fin t → ℝ) → ℝ)
    (η : (Fin t → ℝ) × (Fin r → ℝ) → ℝ) (u : Fin r → ℝ) : ℝ :=
  ∫ v in K, q v * η (v, u)

/-- **Continuity of the tangential average** (dominated continuity, locally in `u`). -/
theorem continuous_tangentialAvg (K : Set (Fin t → ℝ)) (hKc : IsCompact K) (hK : MeasurableSet K)
    (q : (Fin t → ℝ) → ℝ) (hq : IntegrableOn q K) (η : (Fin t → ℝ) × (Fin r → ℝ) → ℝ)
    (hη : Continuous η) : Continuous (tangentialAvg K q η) := by
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨C, hC⟩ := (hKc.prod (isCompact_closedBall u₀ 1)).exists_bound_of_continuousOn
    hη.continuousOn
  unfold tangentialAvg
  refine continuousAt_of_dominated (bound := fun v => C * ‖q v‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun u => ?_
    exact hq.aestronglyMeasurable.mul
      ((hη.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds u₀ one_pos] with u hu
    refine (ae_restrict_iff' hK).2 (Eventually.of_forall fun v hv => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC (v, u) ⟨hv, hu⟩) (norm_nonneg _)
  · exact hq.norm.const_mul C
  · exact Eventually.of_forall fun v =>
      (continuous_const.mul (hη.comp (continuous_const.prodMk continuous_id))).continuousAt

/-- Joint integrability of `q(v) w(u) η(v, φ u)` on `K × S` for a cube-valued map `φ`. -/
theorem integrable_tangential_prod (K : Set (Fin t → ℝ)) (hKc : IsCompact K)
    (q : (Fin t → ℝ) → ℝ) (hq : IntegrableOn q K) (S : Set (Fin r → ℝ))
    (φ : (Fin r → ℝ) → (Fin r → ℝ)) (hφ : MapsTo φ S (closedCube r)) (hφm : Measurable φ)
    (w : (Fin r → ℝ) → ℝ) (hw : IntegrableOn w S) (η : (Fin t → ℝ) × (Fin r → ℝ) → ℝ)
    (hη : Continuous η) (hS : MeasurableSet S) (hK : MeasurableSet K) :
    Integrable (fun z : (Fin t → ℝ) × (Fin r → ℝ) => (q z.1 * w z.2) * η (z.1, φ z.2))
      ((volume.restrict K).prod (volume.restrict S)) := by
  obtain ⟨C, hC⟩ := (hKc.prod (isCompact_closedCube r)).exists_bound_of_continuousOn hη.continuousOn
  have hqw : Integrable (fun z : (Fin t → ℝ) × (Fin r → ℝ) => q z.1 * w z.2)
      ((volume.restrict K).prod (volume.restrict S)) := hq.mul_prod hw
  refine Integrable.mono' (hqw.norm.const_mul C) (hqw.aestronglyMeasurable.mul
    ((hη.measurable.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).aestronglyMeasurable))
    ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (hK.prod hS)]
  refine Eventually.of_forall fun z hz => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC (z.1, φ z.2) ⟨hz.1, hφ hz.2⟩) (norm_nonneg _)

/-- **Fubini for the tangential average**:
`∫_K q(v) ∫_S η(v, φ u) w(u) du dv = ∫_S (∫_K q(v) η(v, φ u) dv) w(u) du`. -/
theorem integral_tangential_swap (K : Set (Fin t → ℝ)) (hKc : IsCompact K) (hK : MeasurableSet K)
    (q : (Fin t → ℝ) → ℝ) (hq : IntegrableOn q K) (S : Set (Fin r → ℝ)) (hS : MeasurableSet S)
    (φ : (Fin r → ℝ) → (Fin r → ℝ)) (hφ : MapsTo φ S (closedCube r)) (hφm : Measurable φ)
    (w : (Fin r → ℝ) → ℝ) (hw : IntegrableOn w S) (η : (Fin t → ℝ) × (Fin r → ℝ) → ℝ)
    (hη : Continuous η) :
    ∫ v in K, q v * ∫ u in S, η (v, φ u) * w u =
      ∫ u in S, (∫ v in K, q v * η (v, φ u)) * w u := by
  have hint := integrable_tangential_prod K hKc q hq S φ hφ hφm w hw η hη hS hK
  have h1 : ∀ v, q v * ∫ u in S, η (v, φ u) * w u = ∫ u in S, (q v * w u) * η (v, φ u) := by
    intro v
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have h2 : ∀ u, (∫ v in K, q v * η (v, φ u)) * w u = ∫ v in K, (q v * w u) * η (v, φ u) := by
    intro u
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  simp_rw [h1, h2]
  exact integral_integral_swap (f := fun v u => (q v * w u) * η (v, φ u)) hint

/-- **Tangentially integrated normal-block asymptotic**. -/
theorem tangential_amplitude_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (K : Set (Fin t → ℝ)) (hKc : IsCompact K)
    (hK : MeasurableSet K) (q : (Fin t → ℝ) → ℝ) (hq : IntegrableOn q K)
    (η : (Fin t → ℝ) × (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ v in K, q v * ∫ x in unitBox (d + 1),
        η (v, x) * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u)))) := by
  have hcont := continuous_tangentialAvg K hKc hK q hq η hη
  have hT := amplitude_tendsto d h k hk l β hl hβ hmin hatt (tangentialAvg K q η) hcont
  -- identify the numerator with the dressed integral of the average
  have hnum : ∀ N, ∫ v in K, q v * ∫ x in unitBox (d + 1),
      η (v, x) * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) =
      ∫ x in unitBox (d + 1), tangentialAvg K q η x *
        ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) := by
    intro N
    have := integral_tangential_swap K hKc hK q hq (unitBox (d + 1)) (measurableSet_unitBox _) id
      (fun x hx => unitBox_subset_closedCube _ hx) measurable_id _
      (monomialBox_integrableOn (d + 1) h k β N) η hη
    unfold tangentialAvg
    simpa only [id] using this
  -- identify the limit
  have hlim : amplitudeCoeff h k l β (tangentialAvg K q η) =
      ∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u)) := by
    have := integral_tangential_swap K hKc hK q hq (unitBox (d + 1)) (measurableSet_unitBox _)
      (faceProj h k l) (faceProj_mapsTo h k l) (measurable_faceProj h k l) _
      (residualWeight_integrableOn h k hk l hmin) η hη
    unfold amplitudeCoeff tangentialAvg
    beta_reduce
    rw [← this, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  rw [hlim] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  beta_reduce
  rw [hnum N]

end Laplace.Grammar
