/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedJetPackage
import Laplace.Multi.AnalyticGermRecovery
import Laplace.Multi.MultilinearDiagonal

/-!
# From equal weighted jets to equal analytic germs

The closing step of the semi-quasi-homogeneous recovery (germbij §7.4(b)): once the weighted
jets agree, the difference of the two losses is `O(‖x‖^N)` at the origin for every `N`, and a
function analytic at `0` that is flat to every order vanishes on a neighbourhood
(`eventually_eq_zero_of_flat_analytic`: every power-series coefficient vanishes on the
diagonal by Taylor's theorem `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`, hence every
derivative tensor vanishes by symmetry, hence the germ is constant, and the constant is zero).

Headline: `weightedJet_germ_eq_of_superPoly` — two losses analytic at the minimum, with
weighted Taylor packages relative to a common quasi-homogeneous leading part, whose localized
normalized monomial moments agree beyond all orders in the temperature, coincide near the
minimum.
-/

open Real MeasureTheory Filter Topology Asymptotics
open scoped ContDiff

namespace Laplace.Multi

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every power-series coefficient of a function flat to all orders at `0` vanishes on the
diagonal. -/
theorem flat_coeff_diag_eq_zero {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hf : HasFPowerSeriesAt f p 0)
    (hflat : ∀ N : ℕ, (fun y ↦ f y) =O[𝓝 (0 : E)] fun y ↦ ‖y‖ ^ N) :
    ∀ n (y : E), (p n fun _ ↦ y) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ k hk =>
    intro y
    have psum_eq : p.partialSum (k + 1) = fun z ↦ p k fun _ ↦ z := by
      funext z
      refine Finset.sum_eq_single _ (fun b hb hnb ↦ ?_) fun hn ↦ ?_
      · exact hk b ((Finset.mem_range_succ_iff.mp hb).lt_of_ne hnb) z
      · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one k)))
    have h := hf.isBigO_sub_partialSum_pow (k + 1)
    simp only [zero_add, psum_eq] at h
    have h2 : (fun z ↦ p k fun _ ↦ z) =O[𝓝 (0 : E)] fun z ↦ ‖z‖ ^ (k + 1) := by
      have := (hflat (k + 1)).sub h
      refine this.congr_left fun z ↦ ?_
      ring
    exact h2.continuousMultilinearMap_apply_eq_zero y

/-- A function analytic at `0` and flat to all orders there vanishes near `0`. -/
theorem eventually_eq_zero_of_flat_analytic {f : E → ℝ} (hf : AnalyticAt ℝ f 0)
    (hflat : ∀ N : ℕ, (fun y ↦ f y) =O[𝓝 (0 : E)] fun y ↦ ‖y‖ ^ N) :
    ∀ᶠ y in 𝓝 (0 : E), f y = 0 := by
  obtain ⟨p, r, hp⟩ := hf
  have hpa : HasFPowerSeriesAt f p 0 := ⟨r, hp⟩
  have hdiag := flat_coeff_diag_eq_zero hpa hflat
  -- the value at the origin
  have hf0 : f 0 = 0 := by
    have := hdiag 0 0
    rwa [hpa.coeff_zero] at this
  -- every derivative tensor of positive order vanishes
  have hjet : ∀ n : ℕ, 0 < n →
      iteratedFDeriv ℝ n f 0 = iteratedFDeriv ℝ n (fun _ : E ↦ (0 : ℝ)) 0 := by
    intro n hn
    rw [iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply]
    refine ContinuousMultilinearMap.eq_of_diag_eq _ 0 ?_ (fun _ _ ↦ by simp) fun y ↦ ?_
    · intro σ v
      exact (hpa.analyticAt.contDiffAt (n := ω)).iteratedFDeriv_comp_perm v σ
    · have h := hasFPowerSeries_diag_eq hp n y
      rw [hdiag n y] at h
      have hfac : ((n.factorial : ℝ))⁻¹ ≠ 0 :=
        inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)
      rw [zero_apply]
      exact ((mul_eq_zero.mp h.symm).resolve_left hfac)
  have hgerm := analytic_germ_eq_of_jet_eq hpa.analyticAt analyticAt_const hjet
  filter_upwards [hgerm] with y hy
  simpa [hf0] using hy

end Flat

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)
variable {P L₁ L₂ : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}

/-- **Semi-quasi-homogeneous germ recovery beyond all orders** (germbij §7.4(b), analytic
case): two losses analytic at the origin, carrying weighted Taylor packages relative to the
same quasi-homogeneous coercive leading part `P` on a localization region `U ∈ 𝓝 0`, with
corrections dominated by `P` on `U`, whose localized normalized monomial moments agree beyond
all orders in the temperature for every exponent of weighted degree `> D`, coincide on a
neighbourhood of the origin. -/
theorem weightedJet_germ_eq_of_superPoly (hPm : Measurable P) (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : ∀ c : ℝ, 0 < c → Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (hU : MeasurableSet U) (hU0 : U ∈ 𝓝 (0 : ι → ℝ))
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    (hL₁a : AnalyticAt ℝ L₁ 0) (hL₂a : AnalyticAt ℝ L₂ 0)
    (J₁ : W.WeightedJet P L₁ U) (J₂ : W.WeightedJet P L₂ U)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdom₁ : ∀ x ∈ U, |L₁ x - P x| ≤ (1 - c₀) * P x)
    (hdom₂ : ∀ x ∈ U, |L₂ x - P x| ≤ (1 - c₀) * P x)
    (hdata : ∀ α : ι → ℕ, W.D < W.wdeg α → Laplace.SuperPoly fun t : ℝ ↦
      tempMoment U L₂ (mvMonomial α) t - tempMoment U L₁ (mvMonomial α) t) :
    ∀ᶠ y in 𝓝 (0 : ι → ℝ), L₁ y = L₂ y := by
  have hcoeff := W.weightedJet_coeff_eq_of_superPoly hPm hP0 hPqh hint hκ hcoer hU hU0 hL₁ hL₂
    J₁ J₂ hc₀ hdom₁ hdom₂ hdata
  have hflat : ∀ N : ℕ, (fun y ↦ (L₁ - L₂) y) =O[𝓝 (0 : ι → ℝ)] fun y ↦ ‖y‖ ^ N := by
    intro N
    obtain ⟨C, hC0, hC⟩ := W.weightedJet_sub_isBigO_of_coeff_eq J₁ J₂ hcoeff
      (N := N + W.D + 1) (by omega)
    refine IsBigO.of_bound C ?_
    filter_upwards [hU0, Metric.closedBall_mem_nhds (0 : ι → ℝ) zero_lt_one] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) N),
      Pi.sub_apply]
    have hx1' : ‖x‖ ≤ 1 := by simpa using hx1
    calc |L₁ x - L₂ x| ≤ C * ‖x‖ ^ (N + W.D + 1) := hC x hx
      _ ≤ C * ‖x‖ ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg x) hx1' (by omega)) hC0
  have := eventually_eq_zero_of_flat_analytic (hL₁a.sub hL₂a) hflat
  filter_upwards [this] with y hy
  simpa [sub_eq_zero] using hy

end IntWeights

end Laplace.Multi
