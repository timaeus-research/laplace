/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.Turnkey

/-!
# Analytic bridge, multivariate

Derives the leading-part hypotheses of the multivariate turnkey theorem
from a power series. If `g` has a power series `p` at `0` whose diagonal
evaluations vanish below degree `m`, then `g` differs from the diagonal
`m`-th term `P x = p m (x, …, x)` by `O(‖x‖^(m+1))` near `0`
(`analytic_remainder_bound`, via the uniform geometric approximation of a
power series by its partial sums). Since `P` is automatically continuous
and homogeneous of degree `m`, this feeds the turnkey theorem directly:
`analytic_pencil_difference_lower_bound_multi` is the germbij Theorem 7.3
lower bound in `ℝ^d` with the Taylor-structure hypotheses replaced by
analytic ones, mirroring the 1D `analytic_pencil_difference_lower_bound'`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Laplace

/-- If the diagonal coefficients of a power series for `g` at `0` vanish
below degree `m`, then `g` agrees with the diagonal `m`-th term up to a
remainder of order `m + 1`. -/
theorem analytic_remainder_bound
    {ι : Type*} [Fintype ι]
    {g : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {r : ℝ≥0∞} (hg : HasFPowerSeriesOnBall g p 0 r) (m : ℕ)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0) :
    ∃ C u₁ : ℝ, 0 ≤ C ∧ 0 < u₁ ∧
      ∀ x : ι → ℝ, ‖x‖ ≤ 2 * u₁ →
        |g x - (p m) (fun _ ↦ x)| ≤ C * ‖x‖ ^ (m + 1) := by
  obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hg.r_pos
  have hr'pos : (0 : ℝ) < r' := ENNReal.coe_pos.mp hr'0
  obtain ⟨a, ha, C, hC, hb⟩ := hg.uniform_geometric_approx' hr'r
  have ha0 : (0 : ℝ) < a := ha.1
  refine ⟨C * (a / r') ^ (m + 1), r' / 4, by positivity, by positivity,
    fun x hx ↦ ?_⟩
  have hxr : ‖x‖ < (r' : ℝ) := by
    have : ‖x‖ ≤ (r' : ℝ) / 2 := by linarith
    linarith
  have hb' := hb x (mem_ball_zero_iff.mpr hxr) (m + 1)
  have hps : p.partialSum (m + 1) x = (p m) (fun _ ↦ x) := by
    rw [FormalMultilinearSeries.partialSum]
    exact Finset.sum_eq_single_of_mem m (Finset.self_mem_range_succ m)
      (fun k hk hne ↦ hlow k
        (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hne) x)
  rw [zero_add, hps, Real.norm_eq_abs] at hb'
  calc |g x - (p m) (fun _ ↦ x)|
      ≤ C * (a * (‖x‖ / r')) ^ (m + 1) := hb'
    _ = C * (a / r') ^ (m + 1) * ‖x‖ ^ (m + 1) := by ring

/-- **Analytic identifiability lower bound, multivariate** (germbij
Theorem 7.3, `ℝ^d`, analytic hypotheses). If `L₂ - L₁` has a power series
at `0` whose diagonal terms vanish below degree `m` and whose diagonal
`m`-th term is nonzero somewhere on the sphere of radius `3/2`, then the
pencil difference obeys the `t^{1 - m - d/2}` lower bound. -/
theorem analytic_pencil_difference_lower_bound_multi
    {ι : Type*} [Fintype ι] (L₁ L₂ ψ : (ι → ℝ) → ℝ)
    {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r : ℝ≥0∞} (m : ℕ)
    (hg : HasFPowerSeriesOnBall (fun w ↦ L₂ w - L₁ w) p 0 r)
    (hlow : ∀ k, k < m → ∀ x : ι → ℝ, (p k) (fun _ ↦ x) = 0)
    {x₀ : ι → ℝ} (hx₀ : (p m) (fun _ ↦ x₀) ≠ 0) (hx₀n : ‖x₀‖ = 3 / 2)
    (hL1c : Continuous L₁) (hL2c : Continuous L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {C0 R : ℝ} (hC0 : 0 ≤ C0) (hR : 0 < R)
    (hsum : ∀ w : ι → ℝ, ‖w‖ ≤ R → L₁ w + L₂ w ≤ C0 * ‖w‖ ^ 2)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ w, 0 ≤ ψ w) (hψ1 : ∀ w : ι → ℝ, ‖w‖ ≤ R → ψ w = 1) :
    ∃ (κ T₀ : ℝ), 0 < κ ∧ 0 < T₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        κ * (t * t ^ (-(m : ℝ) - (Fintype.card ι : ℝ) / 2))
          ≤ ∫ w, ((L₂ w - L₁ w) * ψ w) *
              (Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))) := by
  obtain ⟨C, u₁, hCnn, hu₁, hrem⟩ := analytic_remainder_bound hg m hlow
  have hPc : Continuous fun x : ι → ℝ ↦ (p m) (fun _ ↦ x) :=
    (p m).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id)
  have hPh : ∀ (c : ℝ) (x : ι → ℝ), 0 ≤ c →
      (p m) (fun _ ↦ c • x) = c ^ m * (p m) (fun _ ↦ x) := by
    intro c x _
    simpa [Finset.prod_const, smul_eq_mul] using
      (p m).map_smul_univ (fun _ : Fin m ↦ c) (fun _ ↦ x)
  exact leading_part_pencil_difference_lower_bound' L₁ L₂ ψ
    (fun x ↦ (p m) (fun _ ↦ x)) m hPc hPh hx₀ hx₀n hCnn hu₁ hrem
    hL1c hL2c hL1 hL2 hC0 hR hsum hψc hψs hψ0 hψ1

end Laplace
