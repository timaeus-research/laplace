/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Normalised finite measures and the observables that determine them

The measure-theoretic core of the distinguishability question: what do ratios of integrals
`∫ψ dμ / ∫χ dμ` know about a finite measure `μ`? Exactly its normalisation
`normaliseMeasure μ = μ(1)⁻¹ • μ` (`normalise_eq_iff_forall_ratio`: two nonzero finite Borel measures
on a space with outer approximation of closed sets have the same normalised integrals of all
bounded continuous functions iff their normalisations agree, by Mathlib's
`ext_of_forall_integral_eq_of_IsFiniteMeasure`; conversely equal normalisations give equal ratios
`ratio_eq_of_normalise_eq`). When the test functions are constrained to be supported in an open
set `U`, they determine the restrictions to `U` (`restrict_ext_of_forall_integral_eq`: on a
pseudometric space, `1_U` is the increasing limit of the continuous functions
`min 1 (n · dist(x, Uᶜ))` supported in `U`), and ratios against a fixed reference observable
determine the normalised restrictions (`normalise_restrict_eq_of_forall_ratio`).
-/

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace Laplace.Multi

section Normalise

variable {X : Type*} [MeasurableSpace X]

/-- The normalisation `μ(1)⁻¹ • μ` of a measure. -/
noncomputable def normaliseMeasure (μ : Measure X) : Measure X := (μ univ)⁻¹ • μ

instance (μ : Measure X) [IsFiniteMeasure μ] : IsFiniteMeasure (normaliseMeasure μ) :=
  inferInstanceAs (IsFiniteMeasure ((μ univ)⁻¹ • μ))

theorem integral_normalise (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) :
    ∫ x, f x ∂(normaliseMeasure μ) = (∫ x, f x ∂μ) / μ.real univ := by
  unfold normaliseMeasure
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul, measureReal_def]

theorem measureReal_univ_ne_zero_of_ne_zero {μ : Measure X} [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    μ.real univ ≠ 0 := by
  intro h0
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hμ (Measure.measure_univ_eq_zero.mp h0)
  · exact (measure_ne_top μ univ) h0

theorem ne_zero_of_integral_ne_zero {μ : Measure X} {χ : X → ℝ} (hχ : ∫ x, χ x ∂μ ≠ 0) :
    μ ≠ 0 := fun h ↦ hχ (by rw [h, integral_zero_measure])

/-- Equal normalisations give equal ratios of integrals. -/
theorem ratio_eq_of_normalise_eq {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : normaliseMeasure μ = normaliseMeasure ν) (ψ χ : X → ℝ) (hχμ : ∫ x, χ x ∂μ ≠ 0)
    (hχν : ∫ x, χ x ∂ν ≠ 0) :
    (∫ x, ψ x ∂μ) / ∫ x, χ x ∂μ = (∫ x, ψ x ∂ν) / ∫ x, χ x ∂ν := by
  have hμ0 := measureReal_univ_ne_zero_of_ne_zero (ne_zero_of_integral_ne_zero hχμ)
  have hν0 := measureReal_univ_ne_zero_of_ne_zero (ne_zero_of_integral_ne_zero hχν)
  have e1 : (∫ x, ψ x ∂μ) / ∫ x, χ x ∂μ =
      (∫ x, ψ x ∂(normaliseMeasure μ)) / ∫ x, χ x ∂(normaliseMeasure μ) := by
    rw [integral_normalise, integral_normalise, div_div_div_cancel_right₀ hμ0]
  have e2 : (∫ x, ψ x ∂ν) / ∫ x, χ x ∂ν =
      (∫ x, ψ x ∂(normaliseMeasure ν)) / ∫ x, χ x ∂(normaliseMeasure ν) := by
    rw [integral_normalise, integral_normalise, div_div_div_cancel_right₀ hν0]
  rw [e1, e2, h]

variable [TopologicalSpace X] [HasOuterApproxClosed X] [BorelSpace X]

/-- **Normalised integrals of bounded continuous functions determine the normalisation.** -/
theorem normalise_eq_of_forall_integral_eq {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ f : X →ᵇ ℝ, (∫ x, f x ∂μ) / μ.real univ = (∫ x, f x ∂ν) / ν.real univ) :
    normaliseMeasure μ = normaliseMeasure ν :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ by
    rw [integral_normalise, integral_normalise]
    exact h f

/-- **What ratios of integrals know**: two nonzero finite Borel measures have the same
normalised integrals of all bounded continuous functions iff their normalisations agree. -/
theorem normalise_eq_iff_forall_ratio {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    normaliseMeasure μ = normaliseMeasure ν ↔
      ∀ f : X →ᵇ ℝ, (∫ x, f x ∂μ) / μ.real univ = (∫ x, f x ∂ν) / ν.real univ := by
  constructor
  · intro h f
    have hμ0 : ∫ x, (1 : ℝ) ∂μ ≠ 0 := by
      rw [integral_const, smul_eq_mul, mul_one]
      exact measureReal_univ_ne_zero_of_ne_zero hμ
    have hν0 : ∫ x, (1 : ℝ) ∂ν ≠ 0 := by
      rw [integral_const, smul_eq_mul, mul_one]
      exact measureReal_univ_ne_zero_of_ne_zero hν
    have := ratio_eq_of_normalise_eq h (fun x ↦ f x) (fun _ ↦ (1 : ℝ)) hμ0 hν0
    simpa only [integral_const, smul_eq_mul, mul_one] using this
  · exact normalise_eq_of_forall_integral_eq

end Normalise

section Restrict

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The continuous cutoffs `min 1 (n · dist(x, Uᶜ))` increase to `1_U` on an open set `U`. -/
theorem tendsto_min_infDist_indicator {U : Set X} (hU : IsOpen U) (hne : (Uᶜ).Nonempty) (x : X) :
    Tendsto (fun n : ℕ ↦ min 1 ((n : ℝ) * Metric.infDist x Uᶜ)) atTop
      (𝓝 (U.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    have hpos : 0 < Metric.infDist x Uᶜ := by
      rw [← Metric.infDist_pos_iff_notMem_closure hne, hU.isClosed_compl.closure_eq]
      exact fun h ↦ h hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈1 / Metric.infDist x Uᶜ⌉₊] with n hn
    symm
    apply min_eq_left
    have : 1 / Metric.infDist x Uᶜ ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    rwa [div_le_iff₀ hpos] at this
  · rw [Set.indicator_of_notMem hx]
    have h0 : ∀ n : ℕ, min 1 ((n : ℝ) * Metric.infDist x Uᶜ) = 0 := fun n ↦ by
      rw [Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx), mul_zero]
      exact min_eq_right zero_le_one
    simp only [h0]
    exact tendsto_const_nhds

/-- **Bounded continuous functions supported in an open set determine the restrictions**: two
finite Borel measures whose integrals agree on every bounded continuous function supported in
the open set `U` agree on `U`. -/
theorem restrict_ext_of_forall_integral_eq {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set X} (hU : IsOpen U)
    (h : ∀ f : X → ℝ, Continuous f → (∃ M, ∀ x, |f x| ≤ M) → (∀ x, f x ≠ 0 → x ∈ U) →
      ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ.restrict U = ν.restrict U := by
  by_cases hUc : Uᶜ = ∅
  · have hU' : U = univ := by rwa [compl_empty_iff] at hUc
    subst hU'
    rw [Measure.restrict_univ, Measure.restrict_univ]
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ h f f.continuous
      ⟨‖f‖, fun x ↦ by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x⟩ fun x _ ↦ mem_univ x
  have hne : (Uᶜ).Nonempty := nonempty_iff_ne_empty.mpr hUc
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
  have hgc : ∀ n : ℕ, Continuous fun x ↦ min 1 ((n : ℝ) * Metric.infDist x Uᶜ) := fun n ↦
    continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))
  have hg0 : ∀ (n : ℕ) x, 0 ≤ min 1 ((n : ℝ) * Metric.infDist x Uᶜ) := fun n x ↦
    le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg)
  have hg1 : ∀ (n : ℕ) x, min 1 ((n : ℝ) * Metric.infDist x Uᶜ) ≤ 1 := fun n x ↦ min_le_left _ _
  have hgU : ∀ (n : ℕ) x, x ∉ U → min 1 ((n : ℝ) * Metric.infDist x Uᶜ) = 0 := fun n x hx ↦ by
    rw [Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx), mul_zero]
    exact min_eq_right zero_le_one
  have hbound : ∀ (n : ℕ) x, ‖f x * min 1 ((n : ℝ) * Metric.infDist x Uᶜ)‖ ≤ ‖f‖ := fun n x ↦ by
    rw [norm_mul, Real.norm_of_nonneg (hg0 n x)]
    calc ‖f x‖ * min 1 ((n : ℝ) * Metric.infDist x Uᶜ) ≤ ‖f‖ * 1 :=
          mul_le_mul (f.norm_coe_le_norm x) (hg1 n x) (hg0 n x) (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  have hfg : ∀ n : ℕ, ∫ x, f x * min 1 ((n : ℝ) * Metric.infDist x Uᶜ) ∂μ =
      ∫ x, f x * min 1 ((n : ℝ) * Metric.infDist x Uᶜ) ∂ν := fun n ↦
    h _ (f.continuous.mul (hgc n)) ⟨‖f‖, fun x ↦ by rw [← Real.norm_eq_abs]; exact hbound n x⟩
      fun x hx ↦ by
        by_contra hxU
        exact hx (by rw [hgU n x hxU, mul_zero])
  have hlim : ∀ (κ : Measure X) [IsFiniteMeasure κ],
      Tendsto (fun n : ℕ ↦ ∫ x, f x * min 1 ((n : ℝ) * Metric.infDist x Uᶜ) ∂κ) atTop
        (𝓝 (∫ x, f x * U.indicator (fun _ ↦ (1 : ℝ)) x ∂κ)) := fun κ _ ↦
    tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖)
      (fun n ↦ (f.continuous.mul (hgc n)).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ ae_of_all _ fun x ↦ hbound n x)
      (ae_of_all _ fun x ↦ tendsto_const_nhds.mul (tendsto_min_infDist_indicator hU hne x))
  have hμν : ∫ x, f x * U.indicator (fun _ ↦ (1 : ℝ)) x ∂μ =
      ∫ x, f x * U.indicator (fun _ ↦ (1 : ℝ)) x ∂ν :=
    tendsto_nhds_unique (hlim μ) (by simpa only [hfg] using hlim ν)
  have e : ∀ x, f x * U.indicator (fun _ ↦ (1 : ℝ)) x = U.indicator (fun x ↦ f x) x := fun x ↦ by
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  simp only [e] at hμν
  rw [integral_indicator hU.measurableSet, integral_indicator hU.measurableSet] at hμν
  exact hμν

/-- **Ratios against a fixed reference observable determine the normalised restriction.** If for
every bounded continuous `ψ` supported in the open set `U` the ratios `∫ψ dμ / ∫χ dμ` and
`∫ψ dν / ∫χ dν` agree (`χ` with positive integrals), then the normalised restrictions of `μ`
and `ν` to `U` agree. -/
theorem normalise_restrict_eq_of_forall_ratio {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set X} (hU : IsOpen U) {χ : X → ℝ} (hχμ : 0 < ∫ x, χ x ∂μ)
    (hχν : 0 < ∫ x, χ x ∂ν)
    (h : ∀ ψ : X → ℝ, Continuous ψ → (∃ M, ∀ x, |ψ x| ≤ M) → (∀ x, ψ x ≠ 0 → x ∈ U) →
      (∫ x, ψ x ∂μ) / ∫ x, χ x ∂μ = (∫ x, ψ x ∂ν) / ∫ x, χ x ∂ν) :
    normaliseMeasure (μ.restrict U) = normaliseMeasure (ν.restrict U) := by
  set c : ℝ := (∫ x, χ x ∂μ) / ∫ x, χ x ∂ν with hc
  have hcpos : 0 < c := div_pos hχμ hχν
  have hc0 : ENNReal.ofReal c ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hcpos
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  -- `μ = c • ν` on `U`
  have hres : μ.restrict U = (ENNReal.ofReal c • ν).restrict U := by
    have : IsFiniteMeasure (ENNReal.ofReal c • ν) := ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)⟩
    refine restrict_ext_of_forall_integral_eq hU fun ψ hψc hψb hψU ↦ ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal hcpos.le, smul_eq_mul]
    have := h ψ hψc hψb hψU
    rw [div_eq_div_iff hχμ.ne' hχν.ne'] at this
    rw [hc]
    field_simp
    linarith
  rw [hres, Measure.restrict_smul]
  unfold normaliseMeasure
  rw [Measure.smul_apply, smul_eq_mul, smul_smul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcT)]
  congr 1
  rw [mul_right_comm, ENNReal.inv_mul_cancel hc0 hcT, one_mul]

end Restrict

end Laplace.Multi
