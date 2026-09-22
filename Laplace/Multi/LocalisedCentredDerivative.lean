/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LocalisedCovKOrder2Multi
import Laplace.Multi.LocalisedOrder2Multi

/-!
# The centred covariance's derivative on the localised measure

The note's eq:cov is the *centred* covariance. On E2's exact localised measure, exactly,

`−d/dt Var_loc(uᵢ) = Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ]`,

the off-diagonal centred covariances vanish identically (and, consistently, the raw pair covariance
`Cov_loc[L∘A, uᵢuⱼ]` equals its mean-product term exactly), and to second order

`t²(−∂ₜ Cov_loc(wⱼ, wₖ)) = (H⁻¹)ⱼₖ + 2(∑ᵢ QⱼᵢQₖᵢ vᵢ)/t + O(t⁻²)`, `vᵢ = c₂',ᵢ − cᵢ²`:

the derivative reading holds for the centred eq:cov coefficientwise through second order, the raw
off-diagonal terms `2cᵢcⱼ` of `LocalisedCovKOrder2Multi` cancelling on centring.
-/

open Matrix MeasureTheory Filter Topology Laplace.OneD

namespace Laplace.Multi

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-! ### The exact identities -/

/-- `d/ds ⟨uᵢ^m⟩_loc(s) = −Cov_loc,t[L∘A, uᵢ^m]` on the localised rotated measure. -/
theorem hasDerivAt_localised_frame_pow (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) (m : ℕ) :
    HasDerivAt (fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => affineFrame Q c w i ^ m))
      (-gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ m)) t := by
  have ht2 := half_pos ht
  have e : (fun w => affineFrame Q c w i ^ m) = rotated Q c (fun u : Fin d → ℝ => u i ^ m) := rfl
  have hexp : ∀ s, gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => affineFrame Q c w i ^ m) =
      gibbsExpectation (localisedPotential (separableAnharmonic lam alpha gamma) g
        (affineFrame Q c w₀) s) s (fun u => u i ^ m) := fun s => by
    rw [e, localisedRotated_gibbsExpectation_eq hQ c w₀ s (by fun_prop),
      separablePotential_locFamily]
  have hcov : gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ m) =
      gibbsCov (localisedPotential (separableAnharmonic lam alpha gamma) g (affineFrame Q c w₀) t) t
        (separableAnharmonic lam alpha gamma) (fun u => u i ^ m) := by
    rw [e, localisedRotated_gibbsCov_eq hQ c w₀ t (by fun_prop), separablePotential_locFamily]
  simp only [hexp, hcov]
  refine hasDerivAt_localised_separable hlam hgamma hdisc hg (affineFrame Q c w₀) ht (by fun_prop)
    ?_ ?_
  · exact integrable_energy_mul_separableAnharmonic (fun u => u i ^ m) fun k =>
      integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht2 k i m
  · have := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht2 i i 0 m
    simpa using this

/-- **The exact derivative identity for the centred frame variance**:
`d/ds Var_loc(uᵢ)(s) = −(Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ])`. -/
theorem hasDerivAt_localised_frame_var (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) :
    HasDerivAt (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i))
      (-(gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i))) t := by
  have h2 := hasDerivAt_localised_frame_pow hlam hgamma hdisc hQ c w₀ hg ht i 2
  have h1 := hasDerivAt_localised_frame_pow hlam hgamma hdisc hQ c w₀ hg ht i 1
  simp only [pow_one] at h1
  have e : (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i)) =
      fun s => gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => affineFrame Q c w i ^ 2) -
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => affineFrame Q c w i) *
        gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => affineFrame Q c w i) := by
    funext s
    unfold gibbsCov
    have e' : (fun w => affineFrame Q c w i * affineFrame Q c w i) =
        fun w => affineFrame Q c w i ^ 2 := by funext w; ring
    rw [e']
  rw [e]
  exact (h2.sub (h1.mul h1)).congr_deriv (by ring)

/-- `Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ] = −d/dt Var_loc(uᵢ)`. -/
theorem localisedVar_frame_eq_neg_deriv (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (i : Fin d) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
      2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) =
      -deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i)) t := by
  rw [(hasDerivAt_localised_frame_var hlam hgamma hdisc hQ c w₀ hg ht i).deriv, neg_neg]

/-- **Off the diagonal the centred derivative expression vanishes identically**: for `i ≠ j`,
`Cov_loc[L∘A, uᵢuⱼ] − ⟨uⱼ⟩_loc Cov_loc[L∘A, uᵢ] − ⟨uᵢ⟩_loc Cov_loc[L∘A, uⱼ] = 0` — the raw pair
covariance is exactly its mean-product term. -/
theorem centred_pair_offdiag_zero (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) {i j : Fin d} (hij : i ≠ j) :
    gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => affineFrame Q c w i * affineFrame Q c w j) -
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w j) *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) -
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w j) = 0 := by
  rw [localisedCovK_frame_pair hlam hgamma hdisc hQ c w₀ hg ht hij]
  have ei := localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht i 1
  have ej := localisedCovK_frame_coord hlam hgamma hdisc hQ c w₀ hg ht j 1
  have mi := localised_frame_coord_expectation hlam hgamma hdisc hQ c w₀ hg ht i 1
  have mj := localised_frame_coord_expectation hlam hgamma hdisc hQ c w₀ hg ht j 1
  simp only [pow_one] at ei ej mi mj
  rw [ei, ej, mi, mj]
  ring

/-- The physical-coordinate centred covariance's derivative:
`d/ds Cov_loc(wⱼ, wₖ)(s) = −∑ᵢ QⱼᵢQₖᵢ (Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ])`. -/
theorem hasDerivAt_localised_cov_coord (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) {t : ℝ}
    (ht : 0 < t) (j k : Fin d) :
    HasDerivAt (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
        (fun w => w j) (fun w => w k))
      (-∑ i, Q j i * Q k i *
        (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i))) t := by
  have heq : (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
      (fun w => w j) (fun w => w k)) =ᶠ[𝓝 t]
      fun s => ∑ i, Q j i * Q k i * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s)
        s (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [localisedRotatedAnharmonic_cov_coord hQ c w₀ hlam hgamma hdisc hg hs j k]
      exact Finset.sum_congr rfl fun i _ => by
        rw [localisedRotatedAnharmonic_cov_frame hQ c w₀ hlam hgamma hdisc hg hs i i, if_pos rfl]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_localised_frame_var hlam hgamma hdisc hQ c w₀ hg ht i).const_mul (Q j i * Q k i)
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Second order -/

/-- **The centred frame variance's derivative to second order**:
`|t²(Cov_loc[L∘A, uᵢ²] − 2⟨uᵢ⟩_loc Cov_loc[L∘A, uᵢ]) − 1/λᵢ − 2vᵢ/t| ≤ K/t²`,
`vᵢ = varLocCoeff2 = c₂',ᵢ − cᵢ²`. -/
theorem localisedVar_neg_deriv_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (i : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) - 1 / lam i -
        2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₂, T₂, hK₂, hT₂, h₂⟩ := localisedCovK_frame_sq_order2_rate hlam hgamma hdisc hQ c w₀ hg i
  obtain ⟨Km, Tm, hKm, hTm, hm⟩ := locMean_loc_leading (hlam i) (hgamma i) (hdisc i) hg
    (x₀ := affineFrame Q c w₀ i)
  obtain ⟨Kc, Tc, hKc, hTc, hc⟩ := localisedCovK_frame_lin_rate hlam hgamma hdisc hQ c w₀ hg i
  set ci := locLeadMean lam alpha g (affineFrame Q c w₀) i with hci
  have hci' : ci = -alpha i / (2 * lam i ^ 2) + g * affineFrame Q c w₀ i / lam i := rfl
  refine ⟨K₂ + 2 * (Km * (|ci| + Kc) + |ci| * Kc), T₂ + Tm + Tc, by positivity, by linarith,
    fun {t} ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set C₂ := gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
    (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) with hC₂
  set C₁ := gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
    (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i) with hC₁
  set M₁ := gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
    (fun w => affineFrame Q c w i) with hM₁
  have e₂ := h₂ (t := t) (by linarith)
  have em : |t * M₁ - ci| ≤ Km / t := by
    have mi := localised_frame_coord_expectation hlam hgamma hdisc hQ c w₀ hg ht0 i 1
    simp only [pow_one] at mi
    rw [hM₁, mi, hci']
    exact hm (t := t) (by linarith)
  have ec : |t ^ 2 * C₁ - ci| ≤ Kc / t := hc (t := t) (by linarith)
  have p := prod_rate t (t * M₁) (t ^ 2 * C₁) ci ci Km Kc ht1 hKm hKc em ec
  have hv : 2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) =
      2 * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) - 2 * (ci * ci) := by
    unfold varLocCoeff2
    rw [hci']
    ring
  have key : t ^ 2 * (C₂ - 2 * M₁ * C₁) - 1 / lam i -
      2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t =
      (t ^ 2 * C₂ - 1 / lam i -
        2 * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) -
      2 * (((t * M₁) * (t ^ 2 * C₁) - ci * ci) / t) := by
    rw [hv]
    field_simp
    ring
  rw [key]
  calc _ ≤ |t ^ 2 * C₂ - 1 / lam i -
        2 * locSecondCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t| +
        |2 * (((t * M₁) * (t ^ 2 * C₁) - ci * ci) / t)| := abs_sub _ _
    _ ≤ K₂ / t ^ 2 + 2 * ((Km * (|ci| + Kc) + |ci| * Kc) / t / t) := by
        gcongr
        rw [abs_mul, abs_two, abs_div, abs_of_pos ht0]
        gcongr
    _ = _ := by ring

/-- **The centred covariance tensor's derivative to second order, in physical coordinates**:
`|t²(−∂ₜ Cov_loc(wⱼ, wₖ)) − (H⁻¹)ⱼₖ − 2(∑ᵢ QⱼᵢQₖᵢ vᵢ)/t| ≤ K/t²` — the derivative reading for the
note's centred eq:cov coefficientwise through second order; the raw off-diagonal terms have
cancelled. -/
theorem localisedCov_neg_deriv_order2_rate (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (j k : Fin d) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * (-deriv (fun s => gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ s) s
          (fun w => w j) (fun w => w k)) t) -
        (Q * diagonal (fun i => 1 / lam i) * Qᵀ) j k -
        2 * (∑ i, Q j i * Q k i *
          varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t| ≤ K / t ^ 2 := by
  obtain ⟨K, T, hK, hT, h⟩ := sum_rate_div_sq (fun i => Q j i * Q k i)
    (fun i t => t ^ 2 * (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
      2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (fun w => affineFrame Q c w i) *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) - 1 / lam i -
      2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t)
    (fun i => localisedVar_neg_deriv_order2_rate hlam hgamma hdisc hQ c w₀ hg i)
  refine ⟨K, T, hK, hT, fun {t} ht => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [(hasDerivAt_localised_cov_coord hlam hgamma hdisc hQ c w₀ hg ht0 j k).deriv, neg_neg,
    conj_diagonal_inv_apply]
  have key : t ^ 2 * (∑ i, Q j i * Q k i *
        (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i))) -
      (∑ i, Q j i * Q k i * (1 / lam i)) -
      2 * (∑ i, Q j i * Q k i *
        varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t =
      ∑ i, Q j i * Q k i *
        (t ^ 2 * (gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i ^ 2) -
        2 * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (fun w => affineFrame Q c w i) *
        gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
          (rotatedAnharmonic Q c lam alpha gamma) (fun w => affineFrame Q c w i)) - 1 / lam i -
        2 * varLocCoeff2 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) / t) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  exact h ht

end Multi

end Laplace.Multi
