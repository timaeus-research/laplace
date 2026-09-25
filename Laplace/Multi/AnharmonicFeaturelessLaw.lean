/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthFromBase
import Laplace.Multi.LocalisedEnergyInvariant
import Laplace.Multi.LocalisedEnergyCumulant3

/-!
# The featureless law for a regular model with a proper prior: `ℓ(t)/log t → √(d/2)`

For the separable anharmonic loss `L = ∑ᵢ ℓᵢ(uᵢ)` on `ℝ^d` (a regular model, `λ = d/2`) with the
Gaussian prior `π(u) = e^{-(g/2)|u − m|²}`, the temperature-`u` posterior is the seabed's localised
measure `e^{-u(L + (g/(2u))|u − m|²)}` (`exp_gaussPrior_eq_localised`), whose energy variance obeys
`u² Var_u(L) → d/2` with an explicit rate (`localisedVar_energy_leading`). The temperature
variance is continuous on `[s₀, ∞)` (dominated convergence, `ThermoLengthFromBase`), so the
thermodynamic length from any base temperature `s₀ > 0` satisfies

  `(∫_{s₀}^t √Var_u(L) du) / log t → √(d/2)`   (`anharmonic_thermoLength_div_log_tendsto`):

the RLCT of a regular model, `d/2`, is the growth rate of the thermodynamic length from the
(near-)featureless point to the data — the first concrete instance of the featureless law of
`ThermoLengthAsymptotic`, with a proper prior and an unbounded loss.
-/

open MeasureTheory Filter Topology Set Laplace.OneD
open scoped Matrix

namespace Laplace.Multi

/-- A rate `|f t − c| ≤ K/t` for `t ≥ T` gives `f → c`. -/
theorem tendsto_of_rate_div {f : ℝ → ℝ} {c K T : ℝ} (h : ∀ {t : ℝ}, T ≤ t → |f t - c| ≤ K / t) :
    Tendsto f atTop (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK : Tendsto (fun t : ℝ ↦ K / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Filter.Eventually.of_forall fun t ↦ norm_nonneg _) ?_ hK
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [Real.norm_eq_abs]
  exact h ht

variable {d : ℕ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

/-- The Gaussian prior `e^{-(g/2)|u − m|²}`. -/
noncomputable def gaussPrior (g : ℝ) (m : Fin d → ℝ) : (Fin d → ℝ) → ℝ :=
  fun u ↦ Real.exp (-(g / 2 * ∑ j, (u j - m j) ^ 2))

/-- The trivially rotated anharmonic loss is the separable one. -/
theorem rotatedAnharmonic_one_zero :
    rotatedAnharmonic (1 : Matrix (Fin d) (Fin d) ℝ) 0 lam alpha gamma =
      separableAnharmonic lam alpha gamma := by
  funext w
  simp [rotatedAnharmonic, rotated, affineFrame]

/-- The Gaussian-prior temperature weight is the localised weight. -/
theorem exp_gaussPrior_eq_localised (m : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) (u : Fin d → ℝ) :
    Real.exp (-(t * separableAnharmonic lam alpha gamma u)) * gaussPrior g m u =
      Real.exp (-(t * localisedRotatedAnharmonic 1 0 lam alpha gamma g m t u)) := by
  unfold localisedRotatedAnharmonic
  rw [exp_neg_localisedPotential _ g m ht, rotatedAnharmonic_one_zero, gaussPrior,
    ← Real.exp_add]
  congr 1

/-- Posterior expectations under the Gaussian prior are localised Gibbs expectations. -/
theorem priorExp_gaussPrior (m : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) (φ : (Fin d → ℝ) → ℝ) :
    priorExp volume (gaussPrior g m) (separableAnharmonic lam alpha gamma) φ t =
      gibbsExpectation (localisedRotatedAnharmonic 1 0 lam alpha gamma g m t) t φ := by
  unfold priorExp priorZ gibbsExpectation partitionFunction
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    beta_reduce
    rw [mul_assoc, exp_gaussPrior_eq_localised m ht]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun u ↦
      exp_gaussPrior_eq_localised m ht u)

theorem priorCov_gaussPrior (m : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) (φ ψ : (Fin d → ℝ) → ℝ) :
    priorCov volume (gaussPrior g m) (separableAnharmonic lam alpha gamma) φ ψ t =
      gibbsCov (localisedRotatedAnharmonic 1 0 lam alpha gamma g m t) t φ ψ := by
  simp only [priorCov, gibbsCov, priorExp_gaussPrior m ht]

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The fluctuation law of a regular model**: `u² Var_u(L) → d/2` under the Gaussian prior. -/
theorem tendsto_sq_mul_priorCov_gaussPrior (hg : 0 ≤ g) (m : Fin d → ℝ) :
    Tendsto (fun u ↦ u ^ 2 * priorCov volume (gaussPrior g m) (separableAnharmonic lam alpha gamma)
      (separableAnharmonic lam alpha gamma) (separableAnharmonic lam alpha gamma) u) atTop
      (𝓝 ((d : ℝ) / 2)) := by
  have hQ : (1 : Matrix (Fin d) (Fin d) ℝ)ᵀ * 1 = 1 := by simp
  obtain ⟨K, T, _, _, h⟩ := localisedVar_energy_leading hlam hgamma hdisc hQ 0 m hg
  have h' : Tendsto (fun t ↦ t ^ 2 * gibbsCov (localisedRotatedAnharmonic 1 0 lam alpha gamma g m t)
      t (separableAnharmonic lam alpha gamma) (separableAnharmonic lam alpha gamma)) atTop
      (𝓝 ((d : ℝ) / 2)) := by
    refine tendsto_of_rate_div (T := T) (K := K) fun {t} ht ↦ ?_
    have := h ht
    rwa [rotatedAnharmonic_one_zero] at this
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [priorCov_gaussPrior m ht.ne']

/-- Integrability of `L^k e^{-sL} π` for `k ≤ 2` at a positive temperature. -/
theorem integrable_energy_pow_gaussPrior (hg : 0 ≤ g) (m : Fin d → ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u ↦ Real.exp (-(s * separableAnharmonic lam alpha gamma u)) *
        gaussPrior g m u) ∧
      Integrable (fun u ↦ separableAnharmonic lam alpha gamma u *
        (Real.exp (-(s * separableAnharmonic lam alpha gamma u)) * gaussPrior g m u)) ∧
      Integrable (fun u ↦ separableAnharmonic lam alpha gamma u *
        separableAnharmonic lam alpha gamma u *
        (Real.exp (-(s * separableAnharmonic lam alpha gamma u)) * gaussPrior g m u)) := by
  have hcont : Continuous (separableAnharmonic lam alpha gamma) :=
    continuous_separableAnharmonic lam alpha gamma
  have hLc : Continuous (localisedPotential (rotatedAnharmonic 1 0 lam alpha gamma) g m s) :=
    continuous_localisedRotatedAnharmonic 1 0 lam alpha gamma g m s
  have key : ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ →
      Integrable (fun u ↦ φ u * Real.exp (-(s * separableAnharmonic lam alpha gamma u))) →
      Integrable (fun u ↦ φ u * (Real.exp (-(s * separableAnharmonic lam alpha gamma u)) *
        gaussPrior g m u)) := fun φ hφ hint ↦ by
    have := integrable_localised_of_integrable (L := rotatedAnharmonic 1 0 lam alpha gamma)
      (φ := φ) hg m hs (Continuous.aestronglyMeasurable (by fun_prop)) (by
        rw [rotatedAnharmonic_one_zero]; exact hint)
    refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    change φ u * Real.exp (-(s * localisedRotatedAnharmonic 1 0 lam alpha gamma g m s u)) =
      φ u * (Real.exp (-(s * separableAnharmonic lam alpha gamma u)) * gaussPrior g m u)
    rw [exp_gaussPrior_eq_localised m hs.ne']
  refine ⟨?_, ?_, ?_⟩
  · have := key (fun _ ↦ 1) continuous_const
      (by simpa using integrable_exp_separableAnharmonic hlam hgamma hdisc hs)
    simpa using this
  · refine key _ hcont ?_
    rw [separableAnharmonic_eq_sum (lam := lam) (alpha := alpha) (gamma := gamma)]
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ fun k _ ↦
      integrable_coord_energy_separableAnharmonic hlam hgamma hdisc hs k
  · refine key _ (hcont.mul hcont) ?_
    have e : (fun u ↦ separableAnharmonic lam alpha gamma u *
        separableAnharmonic lam alpha gamma u *
        Real.exp (-(s * separableAnharmonic lam alpha gamma u))) =
        fun u ↦ ∑ k, ∑ i, anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (u i) *
          Real.exp (-(s * separableAnharmonic lam alpha gamma u)) := by
      funext u
      have hL : separableAnharmonic lam alpha gamma u =
          ∑ k, anharmonicPotential (lam k) (alpha k) (gamma k) (u k) := by
        rw [separableAnharmonic_eq_sum]
      conv_lhs => rw [show separableAnharmonic lam alpha gamma u *
        separableAnharmonic lam alpha gamma u = ∑ k, ∑ i,
          anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
          anharmonicPotential (lam i) (alpha i) (gamma i) (u i) by rw [hL, Finset.sum_mul_sum]]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_mul _ _ _
    rw [e]
    exact integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun i _ ↦
      integrable_energy_energy_coord hlam hgamma hdisc k i hs

/-- **The featureless law for a regular model with a Gaussian prior**:
`(∫_{s₀}^t √Var_u(L) du)/log t → √(d/2)` for every base temperature `s₀ > 0`. -/
theorem anharmonic_thermoLength_div_log_tendsto (hg : 0 ≤ g) (m : Fin d → ℝ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) :
    Tendsto (fun t ↦ (∫ u in s₀..t, Real.sqrt (priorCov volume (gaussPrior g m)
      (separableAnharmonic lam alpha gamma) (separableAnharmonic lam alpha gamma)
      (separableAnharmonic lam alpha gamma) u)) / Real.log t) atTop
      (𝓝 (Real.sqrt ((d : ℝ) / 2))) := by
  have hQ : (1 : Matrix (Fin d) (Fin d) ℝ)ᵀ * 1 = 1 := by simp
  obtain ⟨h0, h1, h2⟩ := integrable_energy_pow_gaussPrior hlam hgamma hdisc hg m hs₀
  have hcont := continuousOn_priorCov_self_Ici (μ := volume) (π := gaussPrior g m)
    (L := separableAnharmonic lam alpha gamma) (u₀ := s₀)
    (continuous_separableAnharmonic lam alpha gamma).measurable
    (separableAnharmonic_nonneg hgamma hdisc) (by unfold gaussPrior; fun_prop)
    (fun u ↦ (Real.exp_pos _).le) (fun u hu ↦ ?_) h0 h1 h2
  · exact thermoLength_from_div_log_tendsto hcont
      (tendsto_sq_mul_priorCov_gaussPrior hlam hgamma hdisc hg m)
  · have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu
    have hpos := partitionFunction_localisedRotatedAnharmonic_pos hQ 0 m hlam hgamma hdisc hg hu0
    unfold priorZ
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      exp_gaussPrior_eq_localised (g := g) (lam := lam) (alpha := alpha) (gamma := gamma) m
        hu0.ne' x)]
    exact hpos.ne'

end Laplace.Multi
