/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AnalyticTaylorTree1D

/-!
# The normalised circle operator (Stage 7a)

Unit 260 (Astra #31 route R2, unit 2 of the several-variable bridge tranche). The **normalised
circle operator**
```
A_r(g) = (2πi)⁻¹ ∮_{|w| = r} w⁻¹ g(w) dw
```
(`circleOp`) is the building block of the iterated Cauchy formula. Exported here:

* `‖A_r g‖ ≤ C` whenever `‖g‖ ≤ C` on the circle (`norm_circleOp_le`): the normalisation removes
  every `2πr` factor from the later bookkeeping;
* the one-variable Cauchy formula `A_r((1 − z/w)⁻¹ g) = g z` for `|z| < r` and `g` holomorphic
  on the disc, continuous on its closure (`circleOp_cauchy`);
* coefficient extraction: for `|z| < r`, `∑_n z^n A_r(w^{-n} g) = A_r((1 − z/w)⁻¹ g)` as a `HasSum`
  (`hasSum_circleOp_coeff`), hence `= g z` under the Cauchy hypothesis (`hasSum_circleOp_coeff_eq`),
  with the coefficient bound `‖A_r(w^{-n} g)‖ ≤ C r^{-n}` (`norm_circleOp_coeff_le`);
* continuity of `A_r(G x)` in a parameter `x` when `G` is jointly continuous
  (`continuous_circleOp_param`) — the reusable lemma for the dimension induction.

No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Complex

namespace Laplace.Grammar

/-- The normalised circle operator `A_r(g) = (2πi)⁻¹ ∮_{|w|=r} w⁻¹ g(w) dw`. -/
noncomputable def circleOp (r : ℝ) (g : ℂ → ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ w in C(0, r), w⁻¹ * g w

theorem norm_two_pi_I_inv : ‖((2 * Real.pi * I)⁻¹ : ℂ)‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- **Norm bound**: `‖A_r g‖ ≤ C` if `‖g w‖ ≤ C` on `|w| = r`. -/
theorem norm_circleOp_le {r C : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖g w‖ ≤ C) : ‖circleOp r g‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg (r : ℂ) (by simp [abs_of_pos hr]))
  have h1 : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖w⁻¹ * g w‖ ≤ C / r := by
    intro w hw
    have hw' : ‖w‖ = r := by simpa using hw
    rw [norm_mul, norm_inv, hw', div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hg w hw) (inv_nonneg.2 hr.le)
  have h2 := circleIntegral.norm_integral_le_of_norm_le_const hr.le h1
  unfold circleOp
  rw [norm_mul, norm_two_pi_I_inv]
  calc (2 * Real.pi)⁻¹ * ‖∮ w in C(0, r), w⁻¹ * g w‖ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * (C /
      r)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C := by field_simp

/-- **The Cauchy formula in operator form**: `A_r((1 − z/w)⁻¹ g) = g z` for `|z| < r`. -/
theorem circleOp_cauchy {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g (Metric.ball 0 r))
    {z : ℂ} (hz : ‖z‖ < r) :
    circleOp r (fun w => (1 - z / w)⁻¹ * g w) = g z := by
  have hmem : z ∈ Metric.ball (0 : ℂ) r := by simpa using hz
  have hc := hg.circleIntegral_sub_inv_smul hmem
  have hcongr : (∮ w in C(0, r), w⁻¹ * (1 - z / w)⁻¹ * g w) = ∮ w in C(0, r), (w - z)⁻¹ • g w := by
    refine circleIntegral.integral_congr hr.le fun w hw => ?_
    have hw0 : w ≠ 0 := by
      intro h; rw [Metric.mem_sphere, dist_zero_right] at hw; rw [h, norm_zero] at hw; linarith
    rw [smul_eq_mul]
    congr 1
    field_simp
  unfold circleOp
  have : (fun w : ℂ => w⁻¹ * ((1 - z / w)⁻¹ * g w)) = fun w => w⁻¹ * (1 - z / w)⁻¹ * g w := by
    funext w; ring
  rw [this, hcongr, hc, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]

/-- Coefficient bound `‖A_r(w^{-n} g)‖ ≤ C r^{-n}`. -/
theorem norm_circleOp_coeff_le {r C : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖g w‖ ≤ C) (n : ℕ) :
    ‖circleOp r (fun w => w⁻¹ ^ n * g w)‖ ≤ C * r⁻¹ ^ n := by
  refine norm_circleOp_le hr fun w hw => ?_
  have hw' : ‖w‖ = r := by simpa using hw
  rw [norm_mul, norm_pow, norm_inv, hw', mul_comm]
  exact mul_le_mul_of_nonneg_right (hg w hw) (by positivity)

/-- **Coefficient extraction as a `HasSum`**: `∑_n z^n A_r(w^{-n} g) = A_r((1 − z/w)⁻¹ g)` for
`|z| < r` and `g` circle-integrable. -/
theorem hasSum_circleOp_coeff {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : CircleIntegrable g 0 r) {z : ℂ}
    (hz : ‖z‖ < r) :
    HasSum (fun n => z ^ n * circleOp r (fun w => w⁻¹ ^ n * g w))
      (circleOp r (fun w => (1 - z / w)⁻¹ * g w)) := by
  have h := hasSum_two_pi_I_cauchyPowerSeries_integral (c := 0) hg hz
  simp only [sub_zero, zero_add] at h
  have h2 := h.mul_left ((2 * Real.pi * I)⁻¹ : ℂ)
  -- identify both sides with the operator form
  have hterm : ∀ n : ℕ, (2 * Real.pi * I)⁻¹ * ∮ w in C(0, r), (z / w) ^ n • w⁻¹ • g w =
      z ^ n * circleOp r (fun w => w⁻¹ ^ n * g w) := by
    intro n
    have hfun : (fun w : ℂ => (z / w) ^ n • w⁻¹ • g w) =
        fun w => z ^ n • (w⁻¹ * (w⁻¹ ^ n * g w)) := by
      funext w; simp only [smul_eq_mul, div_eq_mul_inv, mul_pow]; ring
    rw [hfun, circleIntegral.integral_smul, smul_eq_mul]
    show _ = z ^ n * ((2 * Real.pi * I)⁻¹ * ∮ w in C(0, r), w⁻¹ * (w⁻¹ ^ n * g w))
    ring
  have hsum : (2 * Real.pi * I)⁻¹ * ∮ w in C(0, r), (w - z)⁻¹ • g w =
      circleOp r (fun w => (1 - z / w)⁻¹ * g w) := by
    unfold circleOp
    congr 1
    refine circleIntegral.integral_congr hr.le fun w hw => ?_
    have hw0 : w ≠ 0 := by
      intro h; rw [Metric.mem_sphere, dist_zero_right] at hw; rw [h, norm_zero] at hw; linarith
    rw [smul_eq_mul, ← mul_assoc]
    congr 1
    field_simp
  simp_rw [hterm] at h2
  rw [hsum] at h2
  exact h2

/-- **Extraction and reconstruction**: `∑_n z^n A_r(w^{-n} g) = g z` for `|z| < r`, `g` holomorphic
on the disc and continuous on its closure. -/
theorem hasSum_circleOp_coeff_eq {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 r)) {z : ℂ} (hz : ‖z‖ < r) :
    HasSum (fun n => z ^ n * circleOp r (fun w => w⁻¹ ^ n * g w)) (g z) := by
  have hint : CircleIntegrable g 0 r :=
    ContinuousOn.circleIntegrable hr.le (hg.continuousOn.mono (by
      rw [closure_ball _ hr.ne']; exact Metric.sphere_subset_closedBall))
  rw [← circleOp_cauchy hr hg hz]
  exact hasSum_circleOp_coeff hr hint hz

/-- **Parametric continuity**: `x ↦ A_r(G x)` is continuous when `G` is jointly continuous. -/
theorem continuous_circleOp_param {X : Type*} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    {G : X → ℂ → ℂ} (hG : Continuous fun p : X × ℂ => G p.1 p.2) :
    Continuous fun x => circleOp r (G x) := by
  unfold circleOp
  refine continuous_const.mul ?_
  simp only [circleIntegral]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hmap : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun _ => circleMap_ne_center hr.ne'
  have hinv : Continuous fun θ : ℝ => (circleMap 0 r θ)⁻¹ := hmap.inv₀ hne
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
    simp only [deriv_circleMap]; exact hmap.mul continuous_const
  have hGc : Continuous fun p : X × ℝ => G p.1 (circleMap 0 r p.2) :=
    hG.comp (continuous_fst.prodMk (hmap.comp continuous_snd))
  exact (hderiv.comp continuous_snd).smul ((hinv.comp continuous_snd).mul hGc)

end Laplace.Grammar
