/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RescaledData

/-!
# Uniformity in the truth parameter on compact sets

Item G of the relative push-forward programme (germbij_slop S14). Convergence along every
sequence `(t_n, σ_n)` with `t_n → ∞` and `σ_n → σ∞ ∈ K` to a limit continuous on the compact `K`
gives uniform convergence on `K` (`tendstoUniformlyOn_of_seq`, sequential compactness). Applied to
the dominated rescaling lemma along sequences (`RescaledData atTop` on `ℕ`), this turns the pointwise
crossover profiles into uniform ones: the energy statistic of a `σ`-parametrised family converges
uniformly on compact `σ`-sets to its Boltzmann profile (`RescaledData.tendstoUniformlyOn_energy`).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- **Sequential compactness gives uniformity.** If `f t σ → g σ` along every sequence
`(t_n, σ_n)` with `t_n → ∞`, `σ_n ∈ K`, `σ_n → σ∞ ∈ K`, and `g` is continuous on the compact `K`,
then `f t → g` uniformly on `K`. -/
theorem tendstoUniformlyOn_of_seq {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hg : ContinuousOn g K)
    (hseq : ∀ (tn σn : ℕ → ℝ), Tendsto tn atTop atTop → (∀ n, σn n ∈ K) →
      ∀ σl ∈ K, Tendsto σn atTop (𝓝 σl) →
        Tendsto (fun n ↦ f (tn n) (σn n)) atTop (𝓝 (g σl))) :
    TendstoUniformlyOn (fun t σ ↦ f t σ) g atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∀ a : ℝ, ∃ b ≥ a, ∃ σ ∈ K, ε ≤ dist (g σ) (f b σ) := by
    intro a
    obtain ⟨b, hb, hσ⟩ := Filter.frequently_atTop.mp hcon a
    push Not at hσ
    obtain ⟨σ, hσK, hd⟩ := hσ
    exact ⟨b, hb, σ, hσK, hd⟩
  choose tn htn σn hσK hdist using fun n : ℕ ↦ hfreq n
  have htn_lim : Tendsto tn atTop atTop :=
    tendsto_atTop_mono htn tendsto_natCast_atTop_atTop
  obtain ⟨σl, hσl, φ, hφ, hconv⟩ := hK.tendsto_subseq hσK
  have h1 : Tendsto (fun k ↦ f (tn (φ k)) (σn (φ k))) atTop (𝓝 (g σl)) :=
    hseq (tn ∘ φ) (σn ∘ φ) (htn_lim.comp hφ.tendsto_atTop) (fun k ↦ hσK (φ k)) σl hσl hconv
  have h2 : Tendsto (fun k ↦ g (σn (φ k))) atTop (𝓝 (g σl)) := by
    refine ((hg σl hσl).tendsto).comp ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨hconv, Filter.Eventually.of_forall fun k ↦ hσK (φ k)⟩
  have h3 : Tendsto (fun k ↦ dist (g (σn (φ k))) (f (tn (φ k)) (σn (φ k)))) atTop (𝓝 0) := by
    have := (h2.dist h1)
    rwa [dist_self] at this
  have h4 := h3.eventually (eventually_lt_nhds hε)
  obtain ⟨k, hk⟩ := h4.exists
  exact absurd (hdist (φ k)) (not_le.mpr hk)

variable {X : Type*} [MeasurableSpace X]

/-- **Uniform crossover profiles.** A `σ`-parametrised family whose rescaled data converge along
every sequence `(t_n, σ_n) → (∞, σ∞ ∈ K)` has energy statistic converging uniformly on the compact
`K` to its Boltzmann profile, provided the profile is continuous on `K`. -/
theorem RescaledData.tendstoUniformlyOn_energy {μ : Measure X} {G w : ℝ → ℝ → X → ℝ}
    {Φ₀ w₀ : ℝ → X → ℝ} {W : X → ℝ} {c : ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn (fun σ ↦ (∫ u, w₀ σ u * (Φ₀ σ u * Real.exp (-Φ₀ σ u)) ∂μ) /
      ∫ u, w₀ σ u * Real.exp (-Φ₀ σ u) ∂μ) K)
    (hpos : ∀ σ ∈ K, ∫ u, w₀ σ u * Real.exp (-Φ₀ σ u) ∂μ ≠ 0)
    (hseq : ∀ (tn σn : ℕ → ℝ), Tendsto tn atTop atTop → (∀ n, σn n ∈ K) →
      ∀ σl ∈ K, Tendsto σn atTop (𝓝 σl) →
        RescaledData atTop μ (fun n u ↦ G (tn n) (σn n) u) (fun n u ↦ w (tn n) (σn n) u)
          (Φ₀ σl) (w₀ σl) W c) :
    TendstoUniformlyOn
      (fun t σ ↦ (∫ u, w t σ u * (G t σ u * Real.exp (-(G t σ u))) ∂μ) /
        ∫ u, w t σ u * Real.exp (-(G t σ u)) ∂μ)
      (fun σ ↦ (∫ u, w₀ σ u * (Φ₀ σ u * Real.exp (-Φ₀ σ u)) ∂μ) /
        ∫ u, w₀ σ u * Real.exp (-Φ₀ σ u) ∂μ) atTop K := by
  refine tendstoUniformlyOn_of_seq hK hcont fun tn σn htn hσK σl hσl hconv ↦ ?_
  exact (hseq tn σn htn hσK σl hσl hconv).tendsto_energy (hpos σl hσl)

end Laplace.Multi
