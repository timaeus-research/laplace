/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TwoAxisResponse

/-!
# Lengths along the annealing ray

The Fisher length of the annealing ray `u ↦ P_u ∝ e^{−uL₀} π` on `[0, T]` is
`Length(T) = ∫₀ᵀ √Var_u(L₀) du` (`rayLength`): the response form in the temperature direction is
the variance of the loss. Three facts:

* **Length is at most the geometric mean of temperature and energy released**:
  `Length(T)² ≤ T (E(0) − E(T))` (`sq_rayLength_le`, `rayLength_le_sqrt`), by Cauchy–Schwarz.
* **Observables move no faster than the ray**:
  `|⟨φ⟩_T − ⟨φ⟩_0| ≤ ∫₀ᵀ √(Var_u φ · Var_u L₀) du` (`abs_priorExp_sub_le_ray`).
* **Popoviciu**: an observable with values in `[lo, hi]` has variance at most `((hi − lo)/2)²`
  (`priorCov_self_le_sq_of_bounds`), hence `|⟨φ⟩_T − ⟨φ⟩_0| ≤ ((hi − lo)/2) Length(T)`
  (`abs_priorExp_sub_le_rayLength`): **the Fisher length of the annealing ray is at least
  `2|Δ⟨φ⟩|/(hi − lo)` for every observable with values in `[lo, hi]`** (`rayLength_ge`). To move
  a bounded observable by a definite amount the posterior must travel a definite Fisher distance.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The Fisher length of the annealing ray on `[0, T]`: `∫₀ᵀ √Var_u(L₀) du`. -/
noncomputable def rayLength (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (T : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..T, Real.sqrt (priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- Posterior expectations of bounded observables are monotone. -/
theorem priorExp_mono_bdd {t : ℝ} (a : ι → ℝ) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g)
    (h : ∀ x, f x ≤ g x) :
    priorExp μ π (affLoss L₀ R a) f t ≤ priorExp μ π (affLoss L₀ R a) g t := by
  unfold priorExp
  refine div_le_div_of_nonneg_right ?_ (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).le
  refine integral_mono (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hf)
    (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a hg) fun x ↦ ?_
  simp only [mul_assoc]
  exact mul_le_mul_of_nonneg_right (h x) (mul_nonneg (Real.exp_pos _).le (hπ x).le)

/-- **Popoviciu's inequality**: an observable with values in `[lo, hi]` has posterior variance at
most `((hi − lo)/2)²`. -/
theorem priorCov_self_le_sq_of_bounds {t : ℝ} (a : ι → ℝ) {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ}
    (hlo : ∀ x, lo ≤ φ x) (hhi : ∀ x, φ x ≤ hi) :
    priorCov μ π (affLoss L₀ R a) φ φ t ≤ ((hi - lo) / 2) ^ 2 := by
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  -- the centred second moment
  have hsq : priorExp μ π (affLoss L₀ R a)
      (fun x ↦ (φ x - (lo + hi) / 2) * (φ x - (lo + hi) / 2)) t =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * φ x) t -
        2 * ((lo + hi) / 2) * priorExp μ π (affLoss L₀ R a) φ t + ((lo + hi) / 2) ^ 2 := by
    have e : (fun x ↦ (φ x - (lo + hi) / 2) * (φ x - (lo + hi) / 2)) =
        fun x ↦ φ x * φ x + ((-2 * ((lo + hi) / 2)) * φ x + ((lo + hi) / 2) ^ 2) :=
      funext fun x ↦ by ring
    rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hφ.mul hφ)
      ((hφ.const_mul _).add (Bdd.const _)),
      priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hφ.const_mul _) (Bdd.const _),
      priorExp_const_mul_bdd, priorExp_const_fun hZ]
    ring
  -- Popoviciu's pointwise bound
  have hle : priorExp μ π (affLoss L₀ R a)
      (fun x ↦ (φ x - (lo + hi) / 2) * (φ x - (lo + hi) / 2)) t ≤
      priorExp μ π (affLoss L₀ R a) (fun _ ↦ ((hi - lo) / 2) ^ 2) t := by
    refine priorExp_mono_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a ((hφ.sub (Bdd.const _)).mul
      (hφ.sub (Bdd.const _))) (Bdd.const _) fun x ↦ ?_
    nlinarith [mul_nonneg (sub_nonneg.2 (hlo x)) (sub_nonneg.2 (hhi x))]
  rw [priorExp_const_fun hZ] at hle
  unfold priorCov
  nlinarith [sq_nonneg (priorExp μ π (affLoss L₀ R a) φ t - (lo + hi) / 2)]

/-- **The change of an observable along the ray is bounded by the joint variance budget**:
`|⟨φ⟩_T − ⟨φ⟩_0| ≤ ∫₀ᵀ √(Var_u φ · Var_u L₀) du`. -/
theorem abs_priorExp_sub_le_ray {φ : X → ℝ} (hφ : Bdd φ) {T : ℝ} (hT : 0 < T) :
    |priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0| ≤
      ∫ u in (0 : ℝ)..T, Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
        priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hf : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) φ φ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hφ
  have hg : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hL hL
  have hf0 : ∀ u, 0 ≤ priorCov μ π (affLoss L₀ R 0) φ φ u := fun u ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 hφ
  have hD : ∀ u, HasDerivAt (fun u ↦ priorExp μ π (affLoss L₀ R 0) φ u)
      (-priorCov μ π (affLoss L₀ R 0) φ L₀ u) u := fun u ↦
    (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 u hφ).congr_deriv
      (by rw [affLoss_zero_eq_fun L₀ R])
  have hcovc : Continuous (fun u ↦ -priorCov μ π (affLoss L₀ R 0) φ L₀ u) :=
    (continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hL).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hD u)
    (hcovc.intervalIntegrable 0 T)
  have hcs : ∀ u, |priorCov μ π (affLoss L₀ R 0) φ L₀ u| ≤
      Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u * priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) := by
    intro u
    obtain ⟨_, h⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR (0 : ι → ℝ) 0 u
    have := h.abs_tiltCov_le (f := φ) (g := L₀) hφ hL u 0
    rw [← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero,
      ← Real.sqrt_mul (hf0 u)] at this
    exact this
  have hsqrtc : Continuous (fun u ↦ Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
      priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)) := (hf.mul hg).sqrt
  rw [← hftc]
  calc |∫ u in (0 : ℝ)..T, -priorCov μ π (affLoss L₀ R 0) φ L₀ u|
      ≤ ∫ u in (0 : ℝ)..T, |-priorCov μ π (affLoss L₀ R 0) φ L₀ u| :=
        intervalIntegral.abs_integral_le_integral_abs hT.le
    _ ≤ _ := intervalIntegral.integral_mono_on hT.le (hcovc.abs.intervalIntegrable 0 T)
        (hsqrtc.intervalIntegrable 0 T) fun u _ ↦ by rw [abs_neg]; exact hcs u

/-- **Length is at most the geometric mean of temperature and energy released**:
`Length(T)² ≤ T (E(0) − E(T))`. -/
theorem sq_rayLength_le {T : ℝ} (hT : 0 < T) :
    rayLength μ π L₀ R T ^ 2 ≤
      T * (priorExp μ π (affLoss L₀ R 0) L₀ 0 - priorExp μ π (affLoss L₀ R 0) L₀ T) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hg : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hL hL
  have hg0 : ∀ u, 0 ≤ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u := fun u ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 hL
  have hres : ∀ k : ℝ → ℝ, (∫ u in (0 : ℝ)..T, k u) = T * ∫ s in (0 : ℝ)..1, k (T * s) := by
    intro k
    rw [intervalIntegral.integral_comp_mul_left k hT.ne', mul_zero, mul_one, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  have hCS := sq_integral_sqrt_mul_le
    (f := fun s ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s)) (g := fun _ ↦ (1 : ℝ))
    (hg.comp (continuous_const.mul continuous_id)).continuousOn continuousOn_const
    (fun s _ ↦ hg0 _) (fun _ _ ↦ zero_le_one)
  simp only [mul_one, intervalIntegral.integral_const, sub_zero, one_smul] at hCS
  have h1 := hres (fun u ↦ Real.sqrt (priorCov μ π (affLoss L₀ R 0) L₀ L₀ u))
  have h2 := hres (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)
  rw [← integral_var_eq_energy_drop hπm hπi hπ hπpos hL₀m hL₀ hR T, rayLength, h1, h2, mul_pow]
  calc T ^ 2 * (∫ s in (0 : ℝ)..1, Real.sqrt (priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s))) ^ 2
      ≤ T ^ 2 * ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg T)
    _ = _ := by ring

/-- `Length(T) ≤ √(T (E(0) − E(T)))`. -/
theorem rayLength_le_sqrt {T : ℝ} (hT : 0 < T) :
    rayLength μ π L₀ R T ≤
      Real.sqrt (T * (priorExp μ π (affLoss L₀ R 0) L₀ 0 - priorExp μ π (affLoss L₀ R 0) L₀ T)) :=
  Real.le_sqrt_of_sq_le (sq_rayLength_le hπm hπi hπ hπpos hL₀m hL₀ hR hT)

/-- **A bounded observable moves at most `(hi − lo)/2` times the Fisher length of the ray.** -/
theorem abs_priorExp_sub_le_rayLength {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ} (hlo : ∀ x, lo ≤ φ x)
    (hhi : ∀ x, φ x ≤ hi) {T : ℝ} (hT : 0 < T) :
    |priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0| ≤
      (hi - lo) / 2 * rayLength μ π L₀ R T := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hlh : lo ≤ hi := (hlo (Classical.arbitrary X)).trans (hhi _)
  have hr0 : 0 ≤ (hi - lo) / 2 := by linarith
  have hf : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) φ φ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hφ
  have hg : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hL hL
  have hf0 : ∀ u, 0 ≤ priorCov μ π (affLoss L₀ R 0) φ φ u := fun u ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 hφ
  refine (abs_priorExp_sub_le_ray hπm hπi hπ hπpos hL₀m hL₀ hR hφ hT).trans ?_
  unfold rayLength
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT.le ((hf.mul hg).sqrt.intervalIntegrable 0 T)
    ((continuous_const.mul hg.sqrt).intervalIntegrable 0 T) fun u _ ↦ ?_
  rw [Real.sqrt_mul (hf0 u)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u) ≤ Real.sqrt (((hi - lo) / 2) ^ 2) :=
        Real.sqrt_le_sqrt
          (priorCov_self_le_sq_of_bounds hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hlo hhi)
    _ = (hi - lo) / 2 := Real.sqrt_sq hr0

/-- **The Fisher length of the annealing ray is at least `2|Δ⟨φ⟩|/(hi − lo)`** for every
observable with values in `[lo, hi]`. -/
theorem rayLength_ge {φ : X → ℝ} (hφ : Bdd φ) {lo hi : ℝ} (hlo : ∀ x, lo ≤ φ x)
    (hhi : ∀ x, φ x ≤ hi) (hlt : lo < hi) {T : ℝ} (hT : 0 < T) :
    2 * |priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0| / (hi - lo) ≤
      rayLength μ π L₀ R T := by
  have h := abs_priorExp_sub_le_rayLength hπm hπi hπ hπpos hL₀m hL₀ hR hφ hlo hhi hT
  rw [div_le_iff₀ (sub_pos.2 hlt)]
  linarith

end

end Laplace.Multi
