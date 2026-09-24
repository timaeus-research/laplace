/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallLogTerm
import Laplace.Multi.WallFibreExpectationDominant
import Laplace.Multi.PowerLogAssembly

/-!
# The fibre expectation with logarithmic terms

The lexicographic assembly of `PowerLogAssembly` applied to the wall terms: if every term
`p = (i, ε, b)` has a certified power–log asymptotic `t^{λ_p}/(log t)^{k_p} K_p(t) → C_p(φ)` for
both observables, the ratio of the total kernels converges to the ratio of the summed constants
over the lexicographically dominant terms (minimal `λ`, then maximal `k`)
(`tendsto_fibre_expectation_lex`). The three ways a term is certified are collected as
`termKernel` limits: a non-admissible branch vanishes identically
(`tendsto_termKernel_of_not_admissible`), an admissible branch at a certified isolated scale has
the power law `(λ_p, 0)` of `tendsto_term` (`tendsto_termKernel_vertex`), and an admissible branch
of a chart with a pure truth monomial and a fully tied transverse face has the power–log law
`(γp + δλ, k)` of `tendsto_modelKernelOf_tied` (`tendsto_termKernel_tied`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {σ γ : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

open scoped Classical in
theorem termKernel_of_not_admissible {p : TermIdx D} (h : ¬ D.admissible p.1 p.2.1 p.2.2 σ)
    (t : ℝ) : P.termKernel φ σ γ p t = 0 := by
  unfold termKernel
  rw [if_neg h]

/-- A non-admissible branch is negligible at every normalisation. -/
theorem tendsto_termKernel_of_not_admissible {p : TermIdx D}
    (h : ¬ D.admissible p.1 p.2.1 p.2.2 σ) (lam : ℝ) (k : ℕ) :
    Tendsto (fun t ↦ t ^ lam / log t ^ k * P.termKernel φ σ γ p t) atTop (𝓝 0) := by
  simp only [P.termKernel_of_not_admissible h, mul_zero]
  exact tendsto_const_nhds

/-- An admissible branch at a certified isolated scale: the power law `(λ_p, 0)`. -/
theorem tendsto_termKernel_vertex (hS : ∀ i, |D.S i| = 1) (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ} {p : TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hfeas : ConstrainedFeasible (D.Qexp p.1) (P.kappa p.1) γ (P.phaseExp p.1 γ)
      (α p.1 p.2.1 p.2.2))
    (hprof : P.ProfileIntegrableOf p.1 p.2.1 p.2.2 σ γ (α p.1 p.2.1 p.2.2)) :
    Tendsto (fun t ↦ t ^ P.termLam γ α p / log t ^ 0 * P.termKernel φ σ γ p t) atTop
      (𝓝 (P.termConst' φ σ γ α p)) := by
  classical
  have h := P.tendsto_term (hS p.1) hσ hadm (htruth p.1) hφc hφ hMφ hφL hfeas hprof
  unfold termKernel termConst' termLam
  simp only [if_pos hadm, pow_zero, div_one]
  exact h

/-- **The fibre expectation by lexicographic power–log dominance.** -/
theorem tendsto_fibre_expectation_lex (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ)
    (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ} (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z)
    {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) {lam : TermIdx D → ℝ} {kk : TermIdx D → ℕ}
    {Cψ Cχ : TermIdx D → ℝ} {lam₀ : ℝ} {k₀ : ℕ}
    (hmin : ∀ p, lam₀ ≤ lam p ∧ (lam p = lam₀ → kk p ≤ k₀))
    (hKψ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel ψ σ γ p t) atTop
      (𝓝 (Cψ p)))
    (hKχ : ∀ p, Tendsto (fun t ↦ t ^ lam p / log t ^ kk p * P.termKernel χ σ γ p t) atTop
      (𝓝 (Cχ p)))
    (hpos : (∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cχ p) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cψ p) /
        ∑ p ∈ Finset.univ.filter (fun p ↦ lam p = lam₀ ∧ kk p = k₀), Cχ p)) := by
  classical
  refine (tendsto_sum_ratio_lex hmin hKχ hKψ hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [P.totalKernel_toReal_eq_sum_terms hS hF hFm hψc.measurable hψ hMψ ht hσ,
    P.totalKernel_toReal_eq_sum_terms hS hF hFm hχc.measurable hχ hMχ ht hσ]

end WallChartsData.Phase

section Tied

variable {k : ℕ} {ℓ : Fin (k + 1 + 1)} {L' : Set (Fin (k + 1 + 1) → ℝ)}
  {D : WallChartsData (k + 1) ℓ L'} {F : (Fin (k + 1 + 1) → ℝ) → ℝ} (P : D.Phase F)
  {σ γ : ℝ} {φ : (Fin (k + 1 + 1) → ℝ) → ℝ}

open scoped Classical in
/-- An admissible branch of a chart with a pure truth monomial and a fully tied transverse face:
the power–log law `(γp + δλ, k)` with the constant at the wall point. -/
theorem WallChartsData.Phase.tendsto_termKernel_tied (hσ : σ ≠ 0) (hγ : 0 < γ)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') {p : WallChartsData.Phase.TermIdx D}
    (hadm : D.admissible p.1 p.2.1 p.2.2 σ) (hQ : D.Qexp p.1 = 0) (hκ : ∀ j, 0 < P.kappa p.1 j)
    {lam : ℝ} (hlam : 0 < lam) (htied : ∀ j, (P.rExp p.1 j + 1) / P.kappa p.1 j = lam)
    (hδ : 0 < P.phaseExp p.1 γ) :
    Tendsto (fun t ↦ t ^ (γ * P.pExp p.1 + P.phaseExp p.1 γ * lam) / log t ^ k *
        P.termKernel φ σ γ p t) atTop
      (𝓝 (tiedConst (P.constA p.1 σ) (P.constB p.1 σ) (P.phaseExp p.1 γ) (P.kappa p.1)
        (P.rExp p.1) lam (D.ρ p.1) |P.a p.1 0|
        (φ (D.rep p.1 0) * (P.wt p.1 0 * |P.b p.1 0|)))) := by
  have h := P.tendsto_modelKernelOf_tied (ε := p.2.1) (b := p.2.2) hσ hγ hQ hκ hlam htied hδ hφc hφ
    hMφ hφL
  unfold WallChartsData.Phase.termKernel
  simp only [if_pos hadm]
  exact h

end Tied

end Laplace.Multi
