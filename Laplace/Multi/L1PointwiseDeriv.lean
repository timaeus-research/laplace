/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SmoothNormalForm

/-!
# `L¹` derivatives are pointwise derivatives

If a curve `t ↦ f(t) ∈ L¹(ν)` is differentiable at `t₀` with derivative `g`, and the curve has
pointwise representatives `φ(t, ·)` near `t₀` that are differentiable in `t` at `t₀` for every `x`
with derivative `h(x)`, then `g = [h]` (`coeFn_hasDerivAt_L1_ae`, `hasDerivAt_L1_eq_toL1`): `L¹`
convergence of the difference quotients gives an a.e. convergent subsequence, whose pointwise
limit is `h`. This is the bridge from the abstract `L¹` smoothness of the reconstruction curve to
the explicit pointwise formulas for its jets.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- **An `L¹` derivative is the pointwise derivative of any pointwise-differentiable
representative** (almost everywhere): if `f` is `L¹`-differentiable at `s₀` with derivative `g`,
has representatives `φ t` near `s₀`, and `t ↦ φ t x` is differentiable at `s₀` for every `x` with
derivative `h x`, then `g = h` a.e. -/
theorem coeFn_hasDerivAt_L1_ae {f : ℝ → X →₁[ν] ℝ} {g : X →₁[ν] ℝ} {s₀ : ℝ}
    (hL : HasDerivAt f g s₀) {φ : ℝ → X → ℝ}
    (hφ : ∀ᶠ t in 𝓝 s₀, (f t : X → ℝ) =ᵐ[ν] φ t) {h : X → ℝ}
    (hp : ∀ x, HasDerivAt (fun t ↦ φ t x) (h x) s₀) : (g : X → ℝ) =ᵐ[ν] h := by
  obtain ⟨ε, hε, hφε⟩ := Metric.eventually_nhds_iff.1 hφ
  -- a sequence approaching `s₀` from the right inside the neighbourhood
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun n : ℕ ↦ s₀ + ε / 2 * (1 / ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hpos : ∀ n : ℕ, (0 : ℝ) < ε / 2 * (1 / ((n : ℝ) + 1)) := fun n ↦ by positivity
  have hu_ne : ∀ n, u n ≠ s₀ := fun n ↦ by
    rw [hu]
    have := hpos n
    simp only
    linarith
  have hu_mem : ∀ n, dist (u n) s₀ < ε := fun n ↦ by
    rw [hu, Real.dist_eq]
    simp only
    rw [add_sub_cancel_left, abs_of_pos (hpos n)]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc ε / 2 * (1 / ((n : ℝ) + 1)) ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < ε := by linarith
  have hu_tend : Tendsto u atTop (𝓝[≠] s₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hu_ne⟩
    rw [hu]
    have := (tendsto_const_nhds (x := s₀)).add
      ((tendsto_const_nhds (x := ε / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [mul_zero, add_zero] at this
    exact this
  -- the `L¹` slopes converge, hence a subsequence converges almost everywhere
  have hL1 : Tendsto (fun n ↦ slope f s₀ (u n)) atTop (𝓝 g) :=
    (hasDerivAt_iff_tendsto_slope.1 hL).comp hu_tend
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (p := 1) hL1).exists_seq_tendsto_ae
  -- the slopes have pointwise representatives
  have hslope : ∀ n, ((slope f s₀ (u n) : X →₁[ν] ℝ) : X → ℝ) =ᵐ[ν]
      fun x ↦ (u n - s₀)⁻¹ * (φ (u n) x - φ s₀ x) := fun n ↦ by
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_smul ((u n - s₀)⁻¹) (f (u n) - f s₀), Lp.coeFn_sub (f (u n)) (f s₀),
      hφε (hu_mem n), hφε (by rw [dist_self]; exact hε)] with x h1 h2 h3 h4
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul]
  have hall : ∀ᵐ x ∂ν, ∀ n, ((slope f s₀ (u n) : X →₁[ν] ℝ) : X → ℝ) x =
      (u n - s₀)⁻¹ * (φ (u n) x - φ s₀ x) := ae_all_iff.2 hslope
  filter_upwards [hae, hall] with x hx hxall
  -- the pointwise slopes converge to `h x`
  have hpt : Tendsto (fun i ↦ (u (ns i) - s₀)⁻¹ * (φ (u (ns i)) x - φ s₀ x)) atTop (𝓝 (h x)) := by
    have := (hasDerivAt_iff_tendsto_slope.1 (hp x)).comp (hu_tend.comp hns.tendsto_atTop)
    refine this.congr fun i ↦ ?_
    simp only [Function.comp_def, slope_def_field]
    rw [div_eq_inv_mul]
  have hx' : Tendsto (fun i ↦ ((slope f s₀ (u (ns i)) : X →₁[ν] ℝ) : X → ℝ) x) atTop (𝓝 (h x)) :=
    hpt.congr fun i ↦ (hxall (ns i)).symm
  exact tendsto_nhds_unique hx hx'

/-- **An `L¹` derivative is the `L¹` class of the pointwise derivative.** -/
theorem hasDerivAt_L1_eq_toL1 {f : ℝ → X →₁[ν] ℝ} {g : X →₁[ν] ℝ} {s₀ : ℝ}
    (hL : HasDerivAt f g s₀) {φ : ℝ → X → ℝ}
    (hφ : ∀ᶠ t in 𝓝 s₀, (f t : X → ℝ) =ᵐ[ν] φ t) {h : X → ℝ}
    (hp : ∀ x, HasDerivAt (fun t ↦ φ t x) (h x) s₀) (hh : Integrable h ν) : g = hh.toL1 h :=
  Lp.ext ((coeFn_hasDerivAt_L1_ae ν hL hφ hp).trans (Integrable.coeFn_toL1 hh).symm)

/-- The pointwise derivative of a pointwise-differentiable representative of an `L¹`-differentiable
curve is integrable. -/
theorem integrable_of_hasDerivAt_L1 {f : ℝ → X →₁[ν] ℝ} {g : X →₁[ν] ℝ} {s₀ : ℝ}
    (hL : HasDerivAt f g s₀) {φ : ℝ → X → ℝ}
    (hφ : ∀ᶠ t in 𝓝 s₀, (f t : X → ℝ) =ᵐ[ν] φ t) {h : X → ℝ}
    (hp : ∀ x, HasDerivAt (fun t ↦ φ t x) (h x) s₀) : Integrable h ν :=
  (L1.integrable_coeFn g).congr (coeFn_hasDerivAt_L1_ae ν hL hφ hp)

end Laplace.Multi
