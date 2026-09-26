/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NaturalParameterMajorant
import Laplace.Multi.CubicRemainder

/-!
# Taylor expansion along natural-parameter lines with explicit geometric error

With `p(t) = [q_{θ + t v}] ∈ L¹(ν)`, `|⟨v, S⟩| ≤ L` and `ρ = log(3/2)/L`, the factorial bounds of
`NaturalParameterMajorant` give the **explicit Taylor remainder**

`‖p(s + t) − Σ_{k≤N} p^{(k)}(s) t^k / k!‖₁ ≤ 3 (|t|/ρ)^{N+1}`   (`norm_natCurve_sub_taylor_le`)

for every `s, t ∈ ℝ` and `N`, hence the `L¹` Taylor series of the tilt map converges to it on the
whole disc `|t| < ρ` (`tendsto_taylor_natCurve`): an explicit radius of analyticity in natural
coordinates, uniform along the line, and the same for every bounded observable
(`abs_obsL1_natCurve_sub_taylor_le`). The proof pairs with bounded test functions
(`norm_L1_le_of_forall_integral_mul_le`), applies the scalar Lagrange remainder, and reflects
`v ↦ −v` for negative `t`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ContDiff

namespace Laplace.Multi

section CLM

/-- A continuous linear map commutes with the iterated derivatives of a `C^∞` curve. -/
theorem clm_iteratedDeriv_of_contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (t : ℝ) : iteratedDeriv k (fun s ↦ L (f s)) t = L (iteratedDeriv k f t) := by
  have h := L.iteratedFDeriv_comp_left hf.contDiffAt (x := t) (i := k)
    (by exact_mod_cast natCast_le_infty k)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (L ∘ f) t (fun _ ↦ 1) = _
  rw [h]
  rfl

end CLM

section Line

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] (θ v : J → ℝ)
include hS

omit [Nonempty X] [Nonempty J] in
/-- Reflection of the line: `p_{−v}(t) = p_v(−t)`. -/
theorem natCurve_neg (t : ℝ) : natCurve hS ν θ (-v) t = natCurve hS ν θ v (-t) := by
  unfold natCurve
  rw [smul_neg, neg_smul]

omit [Nonempty X] [Nonempty J] in
/-- Jets of the reflected line. -/
theorem iteratedDeriv_natCurve_neg (k : ℕ) (t : ℝ) :
    iteratedDeriv k (natCurve hS ν θ (-v)) t =
      (-1 : ℝ) ^ k • iteratedDeriv k (natCurve hS ν θ v) (-t) := by
  have e : natCurve hS ν θ (-v) = fun t ↦ natCurve hS ν θ v (-t) := funext (natCurve_neg hS ν θ v)
  rw [e, iteratedDeriv_comp_neg]

variable {L : ℝ} (hY : ∀ x, |dirLoss S v x| ≤ L)
include hY

omit [Nonempty J] in
/-- The explicit Taylor remainder along the line, forward direction. -/
theorem norm_natCurve_sub_taylor_le_of_nonneg (hL : 0 < L) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    ‖natCurve hS ν θ v (s + t) - ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s‖ ≤
      3 * (t / (Real.log (3 / 2) / L)) ^ (N + 1) := by
  have hρ : 0 < Real.log (3 / 2) / L := div_pos (Real.log_pos (by norm_num)) hL
  rcases eq_or_lt_of_le ht with h0 | ht0
  · subst h0
    simp [Finset.sum_range_succ', iteratedDeriv_zero]
  refine norm_L1_le_of_forall_integral_mul_le ν _ fun F hF hF1 ↦ ?_
  have hp := contDiff_natCurve hS ν θ v
  have hg : ContDiff ℝ ∞ (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u)) :=
    (obsL1 ν hF).contDiff.comp hp
  have hlt : s < s + t := by linarith
  have hg2 : ContDiffOn ℝ N (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u)) (uIcc s (s + t)) :=
    (hg.of_le (by exact_mod_cast natCast_le_infty N)).contDiffOn
  have hg' : DifferentiableOn ℝ (iteratedDerivWithin N
      (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u)) (uIcc s (s + t))) (uIoo s (s + t)) := by
    rw [uIcc_of_le hlt.le, uIoo_of_le hlt.le]
    refine (hg.differentiable_iteratedDeriv N
      (by exact_mod_cast natCast_lt_infty N)).differentiableOn.congr fun y hy ↦ ?_
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      (hg.of_le (by exact_mod_cast natCast_le_infty N)).contDiffAt (Ioo_subset_Icc_self hy)
  obtain ⟨x', hx', hx⟩ := taylor_mean_remainder_lagrange (n := N) hlt.ne hg2 hg'
  rw [uIoo_of_le hlt.le] at hx'
  rw [uIcc_of_le hlt.le, taylor_within_apply, add_sub_cancel_left] at hx
  have hT : ∀ k ∈ range (N + 1), ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDerivWithin k
      (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u)) (Icc s (s + t)) s =
      ((k.factorial : ℝ)⁻¹ * t ^ k) * obsL1 ν hF (iteratedDeriv k (natCurve hS ν θ v) s) :=
    fun k _ ↦ by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
        (hg.of_le (by exact_mod_cast natCast_le_infty k)).contDiffAt (left_mem_Icc.2 hlt.le),
        clm_iteratedDeriv_of_contDiff _ hp, smul_eq_mul]
  rw [Finset.sum_congr rfl hT] at hx
  have hN1 : |iteratedDerivWithin (N + 1) (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u))
      (Icc s (s + t)) x'| ≤ 3 * (N + 1).factorial / (Real.log (3 / 2) / L) ^ (N + 1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      (hg.of_le (by exact_mod_cast natCast_le_infty (N + 1))).contDiffAt
      (Ioo_subset_Icc_self hx'), clm_iteratedDeriv_of_contDiff _ hp]
    refine (abs_obsL1_le ν hF hF1 _).trans ?_
    rw [one_mul]
    exact norm_iteratedDeriv_natCurve_le hS ν θ v hY hL (N + 1) x'
  have e : ∫ x, F x * (natCurve hS ν θ v (s + t) - ∑ k ∈ range (N + 1),
      ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s) x ∂ν =
      obsL1 ν hF (natCurve hS ν θ v (s + t)) - ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) * obsL1 ν hF (iteratedDeriv k (natCurve hS ν θ v) s) := by
    rw [← obsL1_apply ν hF, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul]
  rw [e, hx]
  have hfac : (0 : ℝ) < (N + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have htN : (0 : ℝ) ≤ t ^ (N + 1) := by positivity
  calc iteratedDerivWithin (N + 1) (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u))
        (Icc s (s + t)) x' * t ^ (N + 1) / (N + 1).factorial ≤
      |iteratedDerivWithin (N + 1) (fun u ↦ obsL1 ν hF (natCurve hS ν θ v u))
        (Icc s (s + t)) x'| * t ^ (N + 1) / (N + 1).factorial := by
        gcongr
        exact le_abs_self _
    _ ≤ 3 * (N + 1).factorial / (Real.log (3 / 2) / L) ^ (N + 1) * t ^ (N + 1) /
        (N + 1).factorial := by gcongr
    _ = 3 * (t / (Real.log (3 / 2) / L)) ^ (N + 1) := by
        have hlog : Real.log (3 / 2) ≠ 0 := (Real.log_pos (by norm_num)).ne'
        rw [div_pow]
        field_simp
        rw [div_pow, mul_pow]
        field_simp

omit [Nonempty J] in
/-- **The explicit Taylor remainder along natural-parameter lines**:
`‖p(s+t) − Σ_{k≤N} p^{(k)}(s) t^k/k!‖₁ ≤ 3 (|t|/ρ)^{N+1}`, `ρ = log(3/2)/L`, for all `s, t`. -/
theorem norm_natCurve_sub_taylor_le (hL : 0 < L) (s t : ℝ) (N : ℕ) :
    ‖natCurve hS ν θ v (s + t) - ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s‖ ≤
      3 * (|t| / (Real.log (3 / 2) / L)) ^ (N + 1) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_natCurve_sub_taylor_le_of_nonneg hS ν θ v hY hL s ht N
  · have hY' : ∀ x, |dirLoss S (-v) x| ≤ L := fun x ↦ by rw [dirLoss_neg, abs_neg]; exact hY x
    have h := norm_natCurve_sub_taylor_le_of_nonneg hS ν θ (-v) hY' hL (-s) (t := -t)
      (by linarith) N
    rw [abs_of_neg ht]
    have e1 : natCurve hS ν θ (-v) (-s + -t) = natCurve hS ν θ v (s + t) := by
      rw [natCurve_neg]
      congr 1
      ring
    have e2 : ∀ k ∈ range (N + 1), ((k.factorial : ℝ)⁻¹ * (-t) ^ k) •
        iteratedDeriv k (natCurve hS ν θ (-v)) (-s) =
        ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s := fun k _ ↦ by
      rw [iteratedDeriv_natCurve_neg, neg_neg, smul_smul]
      congr 1
      have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_pow]; norm_num
      rw [neg_pow]
      linear_combination ((k.factorial : ℝ)⁻¹ * t ^ k) * h1
    rw [e1, Finset.sum_congr rfl e2] at h
    exact h

omit [Nonempty J] in
/-- **Explicit radius of analyticity in natural coordinates**: for `|t| < ρ = log(3/2)/L` the
`L¹` Taylor series of the tilt map at `s` converges to `p(s + t)`. -/
theorem tendsto_taylor_natCurve (hL : 0 < L) (s : ℝ) {t : ℝ}
    (ht : |t| < Real.log (3 / 2) / L) :
    Tendsto (fun N ↦ ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s) atTop
      (𝓝 (natCurve hS ν θ v (s + t))) := by
  have hρ : 0 < Real.log (3 / 2) / L := div_pos (Real.log_pos (by norm_num)) hL
  have hr : |t| / (Real.log (3 / 2) / L) < 1 := (div_lt_one hρ).2 ht
  have hr0 : 0 ≤ |t| / (Real.log (3 / 2) / L) := by positivity
  have hlim : Tendsto (fun N : ℕ ↦ 3 * (|t| / (Real.log (3 / 2) / L)) ^ (N + 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).comp
      (tendsto_add_atTop_nat 1)).const_mul 3
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N ↦ norm_nonneg _) (fun N ↦ ?_) hlim
  rw [norm_sub_rev]
  exact norm_natCurve_sub_taylor_le hS ν θ v hY hL s t N

omit [Nonempty J] in
/-- The same expansion for the response of a bounded observable. -/
theorem abs_obsL1_natCurve_sub_taylor_le {F : X → ℝ} (hF : Bdd F) {B : ℝ} (hB : ∀ x, |F x| ≤ B)
    (hL : 0 < L) (s t : ℝ) (N : ℕ) :
    |obsL1 ν hF (natCurve hS ν θ v (s + t)) - ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) * obsL1 ν hF (iteratedDeriv k (natCurve hS ν θ v) s)| ≤
      B * (3 * (|t| / (Real.log (3 / 2) / L)) ^ (N + 1)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have e : obsL1 ν hF (natCurve hS ν θ v (s + t)) - ∑ k ∈ range (N + 1),
      ((k.factorial : ℝ)⁻¹ * t ^ k) * obsL1 ν hF (iteratedDeriv k (natCurve hS ν θ v) s) =
      obsL1 ν hF (natCurve hS ν θ v (s + t) - ∑ k ∈ range (N + 1),
        ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k (natCurve hS ν θ v) s) := by
    rw [map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul]
  rw [e]
  exact (abs_obsL1_le ν hF hB _).trans
    (mul_le_mul_of_nonneg_left (norm_natCurve_sub_taylor_le hS ν θ v hY hL s t N) hB0)

end Line

end Laplace.Multi
