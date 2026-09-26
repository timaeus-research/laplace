/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.VisibleBudget
import Laplace.Multi.InverseStability
import Laplace.Multi.FixedNormalLimit

/-!
# The exact endpoint tail of the atlas

Along the straight path `M_s = (1 − s) m₀ + s M` to a finite-rate response `M` (interior or
boundary), with `θ_s` the natural coordinates and `κ` the curvature of the rate,

* `KL(Π(M) ‖ Π(M_s)) = 𝓘(M) − 𝓘(M_s) − (1 − s) 𝓘'(s)` exactly
  (`toReal_klDiv_responseProjection_atlas`): the endpoint certificate
  `KL ≤ 𝓘(M) − 𝓘(M_s)` of `EndpointConvergence` is this identity with the first-order term
  `(1 − s)(−⟨θ_s, Δ⟩) ≥ 0` dropped;
* hence the **exact tail formula** `KL(Π(M) ‖ Π(M_s)) = ∫_s^1 (1 − u) κ(u) du`
  (`toReal_klDiv_responseProjection_atlas_eq_integral`), the endpoint remainder of the
  information budget `𝓘(M) = ∫₀¹ (1 − u) κ(u) du`;
* wherever the natural coordinates stay in a ball of radius `r` on `[s, 1)`, the curvature is
  bounded by `‖Δ‖² / κ_r` with `κ_r = e^{−2Br} λ₀` (`atlasCurv_le_of_dotJ_le`), and the endpoint
  divergence is **second order**: `KL(Π(M) ‖ Π(M_s)) ≤ ‖Δ‖² (1 − s)² / (2 κ_r)`
  (`toReal_klDiv_responseProjection_atlas_le`).

The information gap `𝓘(M) − 𝓘(M_s)` itself is first order in `1 − s`, with slope `𝓘'(1)`; it is
the divergence, not the gap, that is quadratic.
-/

open MeasureTheory Filter Topology Set InformationTheory intervalIntegral
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hS hfin in
theorem atlasPath_eq_sub (s : ℝ) :
    atlasPath S ν M s =
      M - (1 - s) • (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  unfold atlasPath
  module

/-- **The exact endpoint identity**: `KL(Π(M) ‖ Π(M_s)) = 𝓘(M) − 𝓘(M_s) − (1 − s)(−⟨θ_s, Δ⟩)`. -/
theorem toReal_klDiv_responseProjection_atlas {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν (atlasPath S ν M s))).toReal =
      (genRate ν S M).toReal - (genRate ν S (atlasPath S ν M s)).toReal -
        (1 - s) * (-dotJ (atlasTheta hS ν M s : J → ℝ)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) := by
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
  have hrel := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel]
  change (klDiv Q (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (atlasTheta hS ν M s))).toReal = _
  rw [familyMeasure_one_zero_eq_tilted hS ν]
  have hbdd : Bdd (fun x ↦ -1 * dirLoss S (atlasTheta hS ν M s : J → ℝ) x) :=
    Bdd.const_mul (-1) (bdd_dirLoss hS _)
  rw [klDiv_tilted_right_eq ν Q hQν hQkl' hbdd, hQkl]
  have hmean : ∫ x, -1 * dirLoss S (atlasTheta hS ν M s : J → ℝ) x ∂Q =
      -dotJ (atlasTheta hS ν M s : J → ℝ) M := by
    rw [MeasureTheory.integral_const_mul, ← dotJ_integral_eq Q hS _, hQM]
    ring
  have hlog : Real.log (∫ x, Real.exp (-1 * dirLoss S (atlasTheta hS ν M s : J → ℝ) x) ∂ν) =
      featCgf ν S (-(atlasTheta hS ν M s : J → ℝ)) := by
    unfold featCgf
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [dirLoss_neg (S := S)]
    ring_nf
  have hrate := genRate_atlasPath_toReal_eq hS ν hfin hs0 hs1
  have hgap := gap_ge_atlasVelocity hS ν hfin hs0 hs1
  rw [dotJ_neg_left] at hrate
  have hlin : dotJ (atlasTheta hS ν M s : J → ℝ) (atlasPath S ν M s) =
      dotJ (atlasTheta hS ν M s : J → ℝ) M - (1 - s) * dotJ (atlasTheta hS ν M s : J → ℝ)
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
    rw [atlasPath_eq_sub, (isLinearMap_dotJ _).map_sub, (isLinearMap_dotJ _).map_smul,
      smul_eq_mul]
  have hnn : 0 ≤ (genRate ν S M).toReal - -dotJ (atlasTheta hS ν M s : J → ℝ) M +
      featCgf ν S (-(atlasTheta hS ν M s : J → ℝ)) := by
    linarith
  rw [hmean, hlog, ENNReal.toReal_ofReal hnn]
  linarith

theorem intervalIntegrable_atlasCurv_weighted_tail {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IntervalIntegrable (fun u ↦ (1 - u) * atlasCurv hS ν hfin u) volume s 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs1.le, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact (integrableOn_atlasCurv_weighted hS ν hfin).mono_set (Ioo_subset_Ioo hs0 le_rfl)

/-- **The exact endpoint tail**: `KL(Π(M) ‖ Π(M_s)) = ∫_s^1 (1 − u) κ(u) du`. -/
theorem toReal_klDiv_responseProjection_atlas_eq_integral {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν (atlasPath S ν M s))).toReal =
      ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u := by
  rw [toReal_klDiv_responseProjection_atlas hS ν hfin hs0 hs1,
    genRate_toReal_eq_integral_atlasCurv hS ν hfin, genRate_atlasPath_eq_integral hS ν hfin hs0 hs1,
    neg_dotJ_atlasTheta_eq_integral hS ν hfin hs0 hs1]
  have hcont : ContinuousOn (atlasCurv hS ν hfin) (Icc 0 s) := fun u hu ↦
    (continuousAt_atlasCurv hS ν hfin hu.1 (lt_of_le_of_lt hu.2 hs1)).continuousWithinAt
  have h01 : ∫ u in Ioo (0 : ℝ) 1, (1 - u) * atlasCurv hS ν hfin u =
      ∫ u in (0 : ℝ)..1, (1 - u) * atlasCurv hS ν hfin u := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hii1 : IntervalIntegrable (fun u ↦ (1 - u) * atlasCurv hS ν hfin u) volume 0 s := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hs0]
    exact (continuousOn_const.sub continuousOn_id).mul hcont
  have hii2 := intervalIntegrable_atlasCurv_weighted_tail hS ν hfin hs0 hs1
  have hsu : IntervalIntegrable (fun u ↦ (s - u) * atlasCurv hS ν hfin u) volume 0 s := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hs0]
    exact (continuousOn_const.sub continuousOn_id).mul hcont
  have hκ : IntervalIntegrable (atlasCurv hS ν hfin) volume 0 s := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le hs0]
  rw [h01, ← intervalIntegral.integral_add_adjacent_intervals hii1 hii2]
  have hsplit : ∫ u in (0 : ℝ)..s, (1 - u) * atlasCurv hS ν hfin u =
      (∫ u in (0 : ℝ)..s, (s - u) * atlasCurv hS ν hfin u) +
        (1 - s) * ∫ u in (0 : ℝ)..s, atlasCurv hS ν hfin u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hsu (hκ.const_mul _)]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    change (1 - u) * atlasCurv hS ν hfin u =
      (s - u) * atlasCurv hS ν hfin u + (1 - s) * atlasCurv hS ν hfin u
    ring
  rw [hsplit]
  ring

section Coercive

variable {B r : ℝ} (hB0 : 0 ≤ B) (hr0 : 0 ≤ r)
  (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
    (statPoint S x - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) ≤ B ^ 2)
  {lam₀ : ℝ} (hlam0 : 0 < lam₀) (hlam : ∀ u : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    lam₀ * dotJ (u : J → ℝ) (u : J → ℝ) ≤ lawCov ν (dirLoss S u) (dirLoss S u))
include hB0 hr0 hB hlam0 hlam

/-- **The curvature is bounded by `‖Δ‖² / κ_r`** wherever the natural coordinates lie in the
ball of radius `r`. -/
theorem atlasCurv_le_of_dotJ_le {u : ℝ}
    (hθ : dotJ (atlasTheta hS ν M u : J → ℝ) (atlasTheta hS ν M u : J → ℝ) ≤ r ^ 2) :
    atlasCurv hS ν hfin u ≤
      dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) /
        (Real.exp (-(2 * (r * B))) * lam₀) := by
  have hK : 0 < Real.exp (-(2 * (r * B))) * lam₀ := mul_pos (Real.exp_pos _) hlam0
  have hvar := variance_familyMeasure_ge_coercive hS ν hB0 hr0 hB hlam hθ
    (atlasVel hS ν hfin u)
  have hκ : atlasCurv hS ν hfin u =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M u))
        (dirLoss S (atlasVel hS ν hfin u)) (dirLoss S (atlasVel hS ν hfin u)) := by
    rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν]
  have hκ' : atlasCurv hS ν hfin u = -dotJ (atlasVel hS ν hfin u : J → ℝ)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := rfl
  have h1 : Real.exp (-(2 * (r * B))) * lam₀ *
      dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasVel hS ν hfin u : J → ℝ) ≤
        atlasCurv hS ν hfin u := by
    rw [hκ]
    exact hvar
  have hcs := sq_dotJ_le (atlasVel hS ν hfin u : J → ℝ)
    (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
  have hΔ0 : 0 ≤ dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hv0 : 0 ≤ dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasVel hS ν hfin u : J → ℝ) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rcases (atlasCurv_nonneg hS ν hfin u).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · rw [le_div_iff₀ hK]
    have h2 : atlasCurv hS ν hfin u ^ 2 ≤
        dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasVel hS ν hfin u : J → ℝ) *
          dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
            (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
      rw [hκ', neg_sq]
      exact hcs
    have h3 : atlasCurv hS ν hfin u * (atlasCurv hS ν hfin u * (Real.exp (-(2 * (r * B))) * lam₀)) ≤
        atlasCurv hS ν hfin u * dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hK.le, mul_le_mul_of_nonneg_right h1 hΔ0]
    exact le_of_mul_le_mul_left h3 hpos

/-- **The endpoint divergence is second order** wherever the natural coordinates stay in a ball
of radius `r` on `[s, 1)`: `KL(Π(M) ‖ Π(M_s)) ≤ ‖Δ‖² (1 − s)² / (2 κ_r)`, `κ_r = e^{−2Br} λ₀`. -/
theorem toReal_klDiv_responseProjection_atlas_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hθ : ∀ u ∈ Ico s 1,
      dotJ (atlasTheta hS ν M u : J → ℝ) (atlasTheta hS ν M u : J → ℝ) ≤ r ^ 2) :
    (klDiv (responseProjection hS ν M) (responseProjection hS ν (atlasPath S ν M s))).toReal ≤
      dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) /
        (Real.exp (-(2 * (r * B))) * lam₀) * ((1 - s) ^ 2 / 2) := by
  rw [toReal_klDiv_responseProjection_atlas_eq_integral hS ν hfin hs0 hs1]
  have hii2 := intervalIntegrable_atlasCurv_weighted_tail hS ν hfin hs0 hs1
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
      (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) /
        (Real.exp (-(2 * (r * B))) * lam₀) := ⟨_, rfl⟩
  rw [← hC]
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
      (mul_pos (Real.exp_pos _) hlam0).le
  have hc : IntervalIntegrable (fun u ↦ (1 - u) * C) volume s 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable _ _
  calc ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u
      ≤ ∫ u in s..1, (1 - u) * C := by
        refine intervalIntegral.integral_mono_on hs1.le hii2 hc fun u hu ↦ ?_
        rcases eq_or_lt_of_le hu.2 with h1 | h1
        · rw [h1]
          simp
        · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          rw [hC]
          exact atlasCurv_le_of_dotJ_le hS ν hfin hB0 hr0 hB hlam0 hlam (hθ u ⟨hu.1, h1⟩)
    _ = C * ((1 - s) ^ 2 / 2) := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
          intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
          intervalIntegral.integral_const, integral_id, smul_eq_mul]
        ring

end Coercive

end Laplace.Multi
