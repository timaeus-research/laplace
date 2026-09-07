/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Laplace.Grammar.AmpCoeffLipschitz

/-!
# Taylor-data identification of double-series coefficients (grammar §4.2, Astra #10 R7)

The Taylor-tree theorems take the coefficient arrays `x, y : ℕ × ℕ → ℝ` of the phase and amplitude
as input. Here we identify them with the Taylor data of the functions they represent:

* `iteratedDeriv_zero_of_hasSum`: if `f(y) = ∑ c_n y^n` on `|y| < r` with `∑ |c_n| r^n < ∞`, then
  `∂^n f(0) = n! c_n` (via Mathlib's `HasFPowerSeriesOnBall.factorial_smul` for the scalar series
  `FormalMultilinearSeries.ofScalars ℝ c`);
* `taylorData_of_eq_dblSum`: if `ξ(u,v) = ∑ x_{ij} u^i v^j` on `|u|, |v| < ρ` with `‖x‖_ρ < ∞`,
  then `∂_v^j ∂_u^i ξ(0,0) = i! j! x_{ij}`; in particular `dblSum_taylorData` for
  `ξ = dblSum x`, and the coefficients are determined by the function on any ball
  (`dblSum_injective`).

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- **One-variable Taylor-data identification.** If `f(y) = ∑ c_n y^n` for `|y| < r` and
`∑ |c_n| r^n < ∞`, then `∂^n f(0) = n! c_n`. -/
theorem iteratedDeriv_zero_of_hasSum (c : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hs : Summable fun n => |c n| * r ^ n) (f : ℝ → ℝ)
    (hf : ∀ y : ℝ, |y| < r → HasSum (fun n => c n * y ^ n) (f y)) (n : ℕ) :
    iteratedDeriv n f 0 = (n.factorial : ℝ) * c n := by
  set r' : NNReal := ⟨r, hr.le⟩ with hr'
  have hp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ c) 0 r' := by
    refine ⟨?_, by exact_mod_cast hr, fun {y} hy => ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      refine hs.congr fun n => ?_
      rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
      rfl
    · rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
      rw [zero_add]
      refine (hf y hy).congr_fun fun n => ?_
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have h := hp.factorial_smul (1 : ℝ) n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h, FormalMultilinearSeries.ofScalars_apply_eq, one_pow,
    smul_eq_mul, mul_one, nsmul_eq_mul]

/-- The weighted row norm `∑_j |x_{ij}| ρ^j`. -/
noncomputable def rowNorm (ρ : ℝ) (x : ℕ × ℕ → ℝ) (i : ℕ) : ℝ := ∑' j, |x (i, j)| * ρ ^ j

theorem row_summable (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (i : ℕ) :
    Summable fun j => |x (i, j)| * ρ ^ j := by
  unfold WSummable at hx
  have h := ((summable_prod_of_nonneg fun k => mul_nonneg (abs_nonneg (x k))
    (pow_nonneg hρ.le _)).1 hx).1 i
  refine (h.mul_left (ρ ^ i)⁻¹).congr fun j => ?_
  change (ρ ^ i)⁻¹ * (|x (i, j)| * ρ ^ (i + j)) = _
  rw [pow_add]
  field_simp

theorem rowNorm_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℕ × ℕ → ℝ) (i : ℕ) : 0 ≤ rowNorm ρ x i :=
  tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (pow_nonneg hρ _)

theorem rowNorm_mul_summable (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) :
    Summable fun i => rowNorm ρ x i * ρ ^ i := by
  unfold WSummable at hx
  have h := ((summable_prod_of_nonneg fun k => mul_nonneg (abs_nonneg (x k))
    (pow_nonneg hρ.le _)).1 hx).2
  refine h.congr fun i => ?_
  unfold rowNorm
  change ∑' j, |x (i, j)| * ρ ^ (i + j) = (∑' j, |x (i, j)| * ρ ^ j) * ρ ^ i
  rw [← tsum_mul_right]
  refine tsum_congr fun j => ?_
  rw [pow_add]; ring

theorem faceU_hasSum (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (i : ℕ) (v : ℝ)
    (hv : |v| ≤ ρ) : HasSum (fun j => x (i, j) * v ^ j) (faceU x i v) := by
  have hs : Summable fun j => x (i, j) * v ^ j := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (row_summable ρ hρ x hx i))
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg v) hv j) (abs_nonneg _)
  exact hs.hasSum

theorem abs_faceU_le_rowNorm (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (i : ℕ)
    (v : ℝ) (hv : |v| ≤ ρ) : |faceU x i v| ≤ rowNorm ρ x i := by
  have hs := (faceU_hasSum ρ hρ x hx i v hv).summable
  unfold faceU rowNorm
  have hn : Summable fun j => ‖x (i, j) * v ^ j‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (row_summable ρ hρ x hx i)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg v) hv j) (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun j => ?_) (row_summable ρ hρ x hx i))
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg v) hv j) (abs_nonneg _)

/-- Row-wise resummation of the double series:
`∑_k x_k u^{k₁} v^{k₂} = ∑_i (∑_j x_{ij} v^j) u^i`. -/
theorem dblSum_hasSum_faceU (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (u v : ℝ)
    (hu : |u| ≤ ρ) (hv : |v| ≤ ρ) : HasSum (fun i => faceU x i v * u ^ i) (dblSum x u v) := by
  have hs := dblSum_summable ρ u v x hx hu hv
  have hrow : ∀ i, HasSum (fun j => x (i, j) * u ^ i * v ^ j) (faceU x i v * u ^ i) := by
    intro i
    refine ((faceU_hasSum ρ hρ x hx i v hv).mul_right (u ^ i)).congr_fun fun j => ?_
    ring
  have := hs.hasSum.prod_fiberwise hrow
  simpa [dblSum] using this

/-- **Taylor-data identification for double series.** If `ξ(u,v) = ∑ x_{ij} u^i v^j` on the open
ball `|u|, |v| < ρ`, then `∂_v^j ∂_u^i ξ(0,0) = i! j! x_{ij}`. -/
theorem taylorData_of_eq_dblSum (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (ξ : ℝ → ℝ → ℝ) (hξ : ∀ u v, |u| < ρ → |v| < ρ → ξ u v = dblSum x u v) (i j : ℕ) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => ξ u v) 0) 0
      = (i.factorial : ℝ) * (j.factorial : ℝ) * x (i, j) := by
  -- the inner derivative: `∂_u^i ξ(0, v) = i! a_i(v)` for `|v| < ρ`
  have hinner : ∀ v, |v| < ρ →
      iteratedDeriv i (fun u => ξ u v) 0 = (i.factorial : ℝ) * faceU x i v := by
    intro v hv
    refine iteratedDeriv_zero_of_hasSum (fun i => faceU x i v) ρ hρ ?_ _ (fun y hy => ?_) i
    · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
        (rowNorm_mul_summable ρ hρ x hx)
      exact mul_le_mul_of_nonneg_right (abs_faceU_le_rowNorm ρ hρ x hx i v hv.le) (by positivity)
    · rw [hξ y v hy hv]
      exact dblSum_hasSum_faceU ρ hρ x hx y v hy.le hv.le
  -- the outer derivative: the function `v ↦ i! a_i(v)` has coefficients `i! x_{ij}`
  rw [show (i.factorial : ℝ) * (j.factorial : ℝ) * x (i, j)
      = (j.factorial : ℝ) * ((i.factorial : ℝ) * x (i, j)) by ring]
  refine iteratedDeriv_zero_of_hasSum (fun j => (i.factorial : ℝ) * x (i, j)) ρ hρ ?_ _
    (fun y hy => ?_) j
  · refine ((row_summable ρ hρ x hx i).mul_left (i.factorial : ℝ)).congr fun j => ?_
    rw [abs_mul, Nat.abs_cast]; ring
  · rw [hinner y hy]
    refine ((faceU_hasSum ρ hρ x hx i y hy.le).mul_left (i.factorial : ℝ)).congr_fun fun j => ?_
    ring

/-- The coefficients of `dblSum x` are its normalised mixed derivatives at the origin. -/
theorem dblSum_taylorData (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (i j : ℕ) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => dblSum x u v) 0) 0
      = (i.factorial : ℝ) * (j.factorial : ℝ) * x (i, j) :=
  taylorData_of_eq_dblSum ρ hρ x hx (fun u v => dblSum x u v) (fun _ _ _ _ => rfl) i j

/-- **Uniqueness of coefficients**: two weighted-summable arrays whose double series agree on the
open ball `|u|, |v| < ρ` coincide. -/
theorem dblSum_injective (ρ : ℝ) (hρ : 0 < ρ) (x x' : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hx' : WSummable ρ x') (h : ∀ u v, |u| < ρ → |v| < ρ → dblSum x u v = dblSum x' u v) :
    x = x' := by
  funext k
  obtain ⟨i, j⟩ := k
  have h1 := dblSum_taylorData ρ hρ x hx i j
  have h2 := taylorData_of_eq_dblSum ρ hρ x' hx' (fun u v => dblSum x u v) h i j
  rw [h1] at h2
  have hpos : (0 : ℝ) < (i.factorial : ℝ) * (j.factorial : ℝ) := by positivity
  exact mul_left_cancel₀ hpos.ne' h2

end Laplace.Grammar
