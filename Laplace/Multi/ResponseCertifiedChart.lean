/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFisherNoiseBridge

/-!
# The certified chart: the good event of the probabilistic resolution theorem

The probabilistic resolution theorem of `ResponseFisherNoiseBridge` exports only the *sign*
event `ℓ(θ₀) < ℓ(θr(M̂_n))`. On the complement of the small-energy event the local inverse chart
`θr` may be evaluated outside its domain, where it is a junk value. Here the good event is
exported in full: the quadratic remainder is certified together with its **domain**
(`exists_responseTheta_quadratic_remainder_dom`: `‖z‖ ≤ δ ⇒ m(θ₀) + z ∈ Ω`), so that on the
small-energy event

* the empirical mean lies in the relative interior of the moment body,
* the chart is valid there, `m(θr(M̂_n)) = M̂_n` — the empirical response is the maximum-entropy
  law with the empirical moments — and
* the response has crossed the wall in the direction of the truth shift.

`measureReal_goodEvent_certified_ge` gives this event probability at least `1 − τ_{θ₀}(D)/(n r²)`;
`measureReal_chartValid_ge` is the certificate-free part (chart validity alone), and the
sign-only theorem of the bridge is its projection. The common engine is
`measureReal_ge_of_energy_lt_ae_le`: any event that almost surely contains the small-energy event
inherits the Chebyshev bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The quantitative quadratic remainder on a closed ball **inside the domain**. -/
theorem exists_quadratic_remainder_subset {F : E → G} {U : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) (hF : ContDiffOn ℝ 2 F U) :
    ∃ δ > 0, Metric.closedBall (0 : E) δ ⊆ U ∧ ∃ K, 0 ≤ K ∧ ∀ z : E, ‖z‖ ≤ δ →
      ‖F z - F 0 - fderiv ℝ F 0 z‖ ≤ K * ‖z‖ ^ 2 := by
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨δ₂, hδ₂, K, hK, h⟩ := exists_quadratic_remainder hU h0 hF
  refine ⟨min (δ₁ / 2) δ₂, lt_min (by positivity) hδ₂, fun z hz ↦ hball ?_, K, hK,
    fun z hz ↦ h z (hz.trans (min_le_right _ _))⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [Metric.mem_ball, dist_zero_right]
  exact hz.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ₁))

end Generic

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- **The quantitative second jet with a certified domain**: on the closed ball of mean
displacements of radius `δ`, the displaced mean is interior and the inverse chart has a quadratic
remainder. -/
theorem exists_responseTheta_quadratic_remainder_dom (θ₀ : 𝕍) :
    ∃ δ > 0, (∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) ∧
      ∃ K, 0 ≤ K ∧ ∀ z : 𝕍, ‖z‖ ≤ δ →
        ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2 := by
  obtain ⟨δ, hδ, hsub, K, hK, h⟩ := exists_quadratic_remainder_subset
    (isOpen_responseBallDomain hS ν θ₀) (zero_mem_responseBallDomain hS ν θ₀)
    ((contDiffOn_responseTheta_meanAdd hS ν θ₀).of_le (by exact_mod_cast natCast_le_infty 2))
  refine ⟨δ, hδ, fun z hz ↦ ?_, K, hK, fun z hz ↦ ?_⟩
  · have hz' : z ∈ Metric.closedBall (0 : 𝕍) δ := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact hsub hz'
  · have := h z hz
    rw [fderiv_responseTheta_meanAdd_zero hS ν] at this
    simp only [Submodule.coe_zero, add_zero, responseTheta_meanMap hS ν] at this
    exact this

/-- **Chart validity on the small-displacement ball**: the displaced mean is interior and the
inverse chart inverts the mean map there. -/
theorem chart_valid_of_norm_le (θ₀ : 𝕍) {δ : ℝ}
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) (z : 𝕍) (hz : ‖z‖ ≤ δ) :
    mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω ∧
      mean (θr (mean (θ₀ : J → ℝ) + (z : J → ℝ))) = mean (θ₀ : J → ℝ) + (z : J → ℝ) :=
  ⟨hdom z hz, meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (hdom z hz)⟩

/-- The total displacement `t e + ξ` stays in the certified ball when `q_{θ₀}(ξ) ≤ r²` and
`|t|‖e‖ + (‖A‖/√c) r ≤ δ`. -/
theorem norm_smul_add_le_of_meanNoiseEnergy (θ₀ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) (e ξ : 𝕍) {t r δ : ℝ} (hr0 : 0 ≤ r)
    (hr : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2)
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ) : ‖t • e + ξ‖ ≤ δ := by
  have hsqrt : Real.sqrt (meanNoiseEnergy hS ν θ₀ ξ) ≤ r := by
    rw [Real.sqrt_le_left hr0]; exact hr
  have hξ : ‖ξ‖ ≤ ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r :=
    calc ‖ξ‖ ≤ ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * Real.sqrt (meanNoiseEnergy hS ν θ₀ ξ) :=
          norm_le_of_meanNoiseEnergy hS ν θ₀ hc hcoer ξ
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
  calc ‖t • e + ξ‖ ≤ ‖t • e‖ + ‖ξ‖ := norm_add_le _ _
    _ ≤ |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r := by
        rw [norm_smul, Real.norm_eq_abs]; linarith
    _ ≤ δ := hδ

/-- **The certified good event, deterministically**: on `q_{θ₀}(ξ) ≤ r²` with a positive
Fisher-radius certificate, the displaced mean is interior, the chart inverts the mean map there,
and the response has crossed the wall `ℓ` in the direction of the truth shift. -/
theorem twoScale_goodEvent_fisher (θ₀ : 𝕍) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e ξ : 𝕍) (t r : ℝ) (hr0 : 0 ≤ r) (hr : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2)
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ)
    (hcert : 0 < t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ / Real.sqrt c * r -
      ‖ℓ‖ * K * (|t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r) ^ 2) :
    mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ) ∈ Ω ∧
      mean (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) =
        mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ) ∧
      ℓ θ₀ < ℓ (θr (mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ))) := by
  have hδ' : ‖t • e + ξ‖ ≤ δ :=
    norm_smul_add_le_of_meanNoiseEnergy hS ν θ₀ hc hcoer e ξ hr0 hr hδ
  obtain ⟨h1, h2⟩ := chart_valid_of_norm_le hS ν θ₀ hdom _ hδ'
  refine ⟨h1, h2, ?_⟩
  have := twoScale_sign_certificate_fisher hS ν θ₀ hc hcoer hK hrem ℓ e ξ t r hr0 hr hδ
  linarith

end Response

section Probabilistic

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  [DecidableEq J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hS hXm hid hlaw hDν hind

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The interior response domain (the sample space is `Ω`). -/
local notation "Ωm" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- **The resolution engine**: any event almost surely containing the small-energy event
`q_{θ₀}(M̂_n − m_D) < r²` has probability at least `1 − τ_{θ₀}(D)/(n r²)`. -/
theorem measureReal_ge_of_energy_lt_ae_le (θ₀ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) {E : Set Ω}
    (hsub : {ω | samplingEnergy hS ν θ₀ p
      (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) < r ^ 2} ≤ᵐ[P] E) :
    1 - -(∑ a, ∑ b, samplingOp hS ν θ₀ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 ≤
      P.real E := by
  have hcompl : Eᶜ ≤ᵐ[P] {ω | r ^ 2 ≤ samplingEnergy hS ν θ₀ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    filter_upwards [hsub] with ω hω hnot
    by_contra hlt
    exact hnot (hω (lt_of_not_ge hlt))
  have h1 : P.real Eᶜ ≤ P.real {ω | r ^ 2 ≤ samplingEnergy hS ν θ₀ p
        (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcompl)
  have h2 := measureReal_samplingEnergy_ge_le hS ν P D hDν Xs hXm hid hlaw hind θ₀ p hp hn hr
  have h3 : (1 : ℝ) ≤ P.real E + P.real Eᶜ := by
    have := measureReal_union_le (μ := P) E Eᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  linarith

omit [Nonempty X] [Nonempty J] [DecidableEq J] hS [IsProbabilityMeasure ν] [MeasurableSpace Ω]
  [IsProbabilityMeasure P] [IsProbabilityMeasure D] hDν hXm hid hlaw hind in
/-- The empirical mean as `m(θ₀) + t e + ξ` on the event where the sampling displacement lies in
the direction space. -/
theorem sampleResponse_eq_add_add (θ₀ e : 𝕍) (t : ℝ)
    (hmean : (fun j ↦ ∫ x, S j x ∂D) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ)) {n : ℕ} (ω : Ω)
    (hω : (fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D) ∈ 𝕍) :
    sampleResponse S Xs n ω = mean (θ₀ : J → ℝ) +
      ((t • e + ⟨fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D, hω⟩ : 𝕍) : J → ℝ) := by
  rw [Submodule.coe_add, Submodule.coe_smul]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := congrFun hmean j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- **The probabilistic resolution theorem with the good event**: with probability at least
`1 − τ_{θ₀}(D)/(n r²)` the empirical mean is interior, the chart inverts the mean map at it
(the empirical response is the maximum-entropy law with the empirical moments), and the response
has crossed the wall `ℓ` in the direction of the truth shift. -/
theorem measureReal_goodEvent_certified_ge (θ₀ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      ‖θr (mean (θ₀ : J → ℝ) + (z : J → ℝ)) - θ₀ - (CDE θ₀).symm z‖ ≤ K * ‖z‖ ^ 2)
    (ℓ : 𝕍 →L[ℝ] ℝ) (e : 𝕍) (t r : ℝ) (hr : 0 < r)
    (hmean : (fun j ↦ ∫ x, S j x ∂D) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ))
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ)
    (hcert : 0 < t * ℓ (((CDE θ₀).symm : 𝕍 →L[ℝ] 𝕍) e) - ‖ℓ‖ / Real.sqrt c * r -
      ‖ℓ‖ * K * (|t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r) ^ 2)
    {n : ℕ} (hn : 0 < n) :
    1 - -(∑ a, ∑ b, samplingOp hS ν θ₀ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 ≤
      P.real {ω | sampleResponse S Xs n ω ∈ Ωm ∧
        mean (θr (sampleResponse S Xs n ω)) = sampleResponse S Xs n ω ∧
        ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))} := by
  refine measureReal_ge_of_energy_lt_ae_le hS ν P D hDν Xs hXm hid hlaw hind θ₀ p hp hn hr ?_
  filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω hlt
  set ξ : 𝕍 := ⟨fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D, hω⟩ with hξ
  have hE : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2 := by
    rw [← meanNoiseEnergy_eq_samplingEnergy hS ν θ₀ p hp ξ]
    exact le_of_lt hlt
  have hpt : sampleResponse S Xs n ω = mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ) :=
    sampleResponse_eq_add_add ν D Xs θ₀ e t hmean ω hω
  have h := twoScale_goodEvent_fisher hS ν θ₀ hc hcoer hK hdom hrem ℓ e ξ t r hr.le hE hδ hcert
  change sampleResponse S Xs n ω ∈ Ωm ∧
    mean (θr (sampleResponse S Xs n ω)) = sampleResponse S Xs n ω ∧
    ℓ θ₀ < ℓ (θr (sampleResponse S Xs n ω))
  rw [hpt]
  exact h

/-- **Chart validity alone**: without any wall, the empirical mean is interior and the chart
inverts the mean map at it with probability at least `1 − τ_{θ₀}(D)/(n r²)`, as soon as
`|t|‖e‖ + (‖A‖/√c) r ≤ δ`. -/
theorem measureReal_chartValid_ge (θ₀ : 𝕍) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : 𝕍, c * ‖v‖ ^ 2 ≤ G θ₀ v v) {δ : ℝ}
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (e : 𝕍) (t r : ℝ) (hr : 0 < r)
    (hmean : (fun j ↦ ∫ x, S j x ∂D) = mean (θ₀ : J → ℝ) + t • (e : J → ℝ))
    (hδ : |t| * ‖e‖ + ‖(CD θ₀ : 𝕍 →L[ℝ] 𝕍)‖ / Real.sqrt c * r ≤ δ) {n : ℕ} (hn : 0 < n) :
    1 - -(∑ a, ∑ b, samplingOp hS ν θ₀ p (Pi.single b 1) a * lawCov D (S a) (S b)) / n / r ^ 2 ≤
      P.real {ω | sampleResponse S Xs n ω ∈ Ωm ∧
        mean (θr (sampleResponse S Xs n ω)) = sampleResponse S Xs n ω} := by
  refine measureReal_ge_of_energy_lt_ae_le hS ν P D hDν Xs hXm hid hlaw hind θ₀ p hp hn hr ?_
  filter_upwards [ae_sampleResponse_sub_mem_dirSpan hS ν P D hDν Xs hXm hid hlaw hn] with ω hω hlt
  set ξ : 𝕍 := ⟨fun j ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D, hω⟩ with hξ
  have hE : meanNoiseEnergy hS ν θ₀ ξ ≤ r ^ 2 := by
    rw [← meanNoiseEnergy_eq_samplingEnergy hS ν θ₀ p hp ξ]
    exact le_of_lt hlt
  have hpt : sampleResponse S Xs n ω = mean (θ₀ : J → ℝ) + ((t • e + ξ : 𝕍) : J → ℝ) :=
    sampleResponse_eq_add_add ν D Xs θ₀ e t hmean ω hω
  have hδ' : ‖t • e + ξ‖ ≤ δ :=
    norm_smul_add_le_of_meanNoiseEnergy hS ν θ₀ hc hcoer e ξ hr.le hE hδ
  have h := chart_valid_of_norm_le hS ν θ₀ hdom _ hδ'
  change sampleResponse S Xs n ω ∈ Ωm ∧
    mean (θr (sampleResponse S Xs n ω)) = sampleResponse S Xs n ω
  rw [hpt]
  exact h

end Probabilistic

end Laplace.Multi
