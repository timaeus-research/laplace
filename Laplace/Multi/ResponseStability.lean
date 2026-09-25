/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MeanJourney
import Laplace.Multi.RayLength

/-!
# Quantitative stability: how far the response moves under a change of the data

Under a **uniform ellipticity** bound `α ‖v‖² ≤ Var_a(R_v) ≤ β ‖v‖²` on the covariance form
`v ⬝ C_a v = Cov_a(R_v, R_v)` (`dotProduct_featCov_mulVec`), the two journeys of `MeanJourney`
bound the information distance from both sides:

* along the mean journey, `‖Δ‖²/β ≤ Δ ⬝ C⁻¹ Δ ≤ ‖Δ‖²/α` (`mul_meanSpeed_le`, `le_mul_meanSpeed`,
  by the Cauchy–Schwarz inequality of the covariance form `sq_dotProduct_featCov_le`), hence
  `‖Δm‖² ≤ 2 β KL(P_{a₁} ‖ P_{a₀})` and `2 α KL(P_{a₁} ‖ P_{a₀}) ≤ ‖Δm‖²` with `Δm = m(a₁) − m(a₀)`
  (`sq_dist_meanMap_le_famKL`, `famKL_le_sq_dist_meanMap`);
* along the natural journey, `t² α ‖Δa‖² ≤ 2 KL(P_{a₁} ‖ P_{a₀}) ≤ t² β ‖Δa‖²` with `Δa = a₁ − a₀`
  (`famKL_ge_sq_dist_coeff`, `famKL_le_sq_dist_coeff`).

Together: **the mean map is bi-Lipschitz**, `α t ‖Δa‖ ≤ ‖Δm‖ ≤ β t ‖Δa‖`
(`sq_dist_meanMap_le`, `le_sq_dist_meanMap`) — a small change of the data moves the response by at
most `β t` times as much, and a response cannot be reproduced by a data change smaller than
`1/(α t)` times its displacement (quantitative identifiability). The upper constant is always
available: bounded features `|Rᵢ| ≤ Mᵢ` give `Var_a(R_v) ≤ (∑ Mᵢ²) ‖v‖²` at every `a`
(`dotProduct_featCov_mulVec_le_of_bounds`), so
`‖m(a₁) − m(a₀)‖ ≤ t (∑ Mᵢ²) ‖a₁ − a₀‖` unconditionally (`sq_dist_meanMap_le_of_bounds`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- `∫₀¹ (1 − s) c ds = c / 2`. -/
theorem integral_one_sub_mul_const (c : ℝ) :
    ∫ s in (0 : ℝ)..1, (1 - s) * c = c / 2 := by
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const]
  norm_num
  ring

/-- `∫₀¹ s c ds = c / 2`. -/
theorem integral_id_mul_const (c : ℝ) : ∫ s in (0 : ℝ)..1, s * c = c / 2 := by
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] in
/-- The covariance form: `u ⬝ C_a v = Cov_a(R_u, R_v)`. -/
theorem dotProduct_featCov_mulVec (a u v : ι → ℝ) :
    dotProduct u ((featCov μ π L₀ R t a).mulVec v) =
      priorCov μ π (affLoss L₀ R a) (dirLoss R u) (dirLoss R v) t := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR v) u]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a v i]

/-- **Cauchy–Schwarz for the covariance form**: `(u ⬝ C v)² ≤ (u ⬝ C u)(v ⬝ C v)`. -/
theorem sq_dotProduct_featCov_le (a u v : ι → ℝ) :
    dotProduct u ((featCov μ π L₀ R t a).mulVec v) ^ 2 ≤
      dotProduct u ((featCov μ π L₀ R t a).mulVec u) *
        dotProduct v ((featCov μ π L₀ R t a).mulVec v) := by
  rw [dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR,
    dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR,
    dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR]
  obtain ⟨M, hT⟩ := tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t
  have h := hT.abs_tiltCov_le (bdd_dirLoss hR u) (bdd_dirLoss hR v) t 0
  rw [← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero, ← priorCov_eq_tiltCov_zero] at h
  have hu := priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (bdd_dirLoss hR u)
  have hv := priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (bdd_dirLoss hR v)
  calc priorCov μ π (affLoss L₀ R a) (dirLoss R u) (dirLoss R v) t ^ 2
      = |priorCov μ π (affLoss L₀ R a) (dirLoss R u) (dirLoss R v) t| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (priorCov μ π (affLoss L₀ R a) (dirLoss R u) (dirLoss R u) t) *
          Real.sqrt (priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hv]

/-- Bounded features bound the covariance form uniformly: `Var_a(R_v) ≤ (∑ Mᵢ²) ‖v‖²`. -/
theorem dotProduct_featCov_mulVec_le_of_bounds {M : ι → ℝ} (hM : ∀ i x, |R i x| ≤ M i)
    (a v : ι → ℝ) :
    dotProduct v ((featCov μ π L₀ R t a).mulVec v) ≤ (∑ i, M i ^ 2) * dotProduct v v := by
  rw [dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR]
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have hv := bdd_dirLoss hR v
  have hpt : ∀ x, dirLoss R v x * dirLoss R v x ≤ (∑ i, M i ^ 2) * dotProduct v v := by
    intro x
    have h1 : (∑ i, v i * R i x) ^ 2 ≤ (∑ i, v i ^ 2) * ∑ i, R i x ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h2 : ∑ i, R i x ^ 2 ≤ ∑ i, M i ^ 2 := Finset.sum_le_sum fun i _ ↦ by
      rw [← sq_abs (R i x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM i x) 2
    have h3 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have e : dotProduct v v = ∑ i, v i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq (v i)).symm
    rw [e]
    calc dirLoss R v x * dirLoss R v x = (∑ i, v i * R i x) ^ 2 := by rw [sq]; rfl
      _ ≤ (∑ i, v i ^ 2) * ∑ i, R i x ^ 2 := h1
      _ ≤ (∑ i, v i ^ 2) * ∑ i, M i ^ 2 := mul_le_mul_of_nonneg_left h2 h3
      _ = (∑ i, M i ^ 2) * ∑ i, v i ^ 2 := mul_comm _ _
  calc priorCov μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t
      ≤ priorExp μ π (affLoss L₀ R a) (fun x ↦ dirLoss R v x * dirLoss R v x) t := by
        unfold priorCov
        linarith [mul_self_nonneg (priorExp μ π (affLoss L₀ R a) (dirLoss R v) t)]
    _ ≤ priorExp μ π (affLoss L₀ R a) (fun _ ↦ (∑ i, M i ^ 2) * dotProduct v v) t :=
        priorExp_mono_bdd hπm hπi hπ hπpos hL₀m hL₀ hR a (hv.mul hv) (Bdd.const _) hpt
    _ = (∑ i, M i ^ 2) * dotProduct v v := priorExp_const_fun hZ _

variable (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include ht hnd

/-- Under `α ‖w‖² ≤ w ⬝ C w` at the point `a(s)`, the inverse-covariance speed is at most
`‖Δ‖²/α`: `α q ≤ ‖Δ‖²`. -/
theorem mul_meanSpeed_le [DecidableEq ι] {α : ℝ} (hα : 0 < α) (y₀ d : ι → ℝ) (s : ℝ)
    (h : ∀ w, α * dotProduct w w ≤
      dotProduct w ((featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ d s)).mulVec w)) :
    α * meanSpeed μ π L₀ R t y₀ d s ≤ dotProduct d d := by
  obtain ⟨a, ha⟩ : ∃ a, meanLine μ π L₀ R t y₀ d s = a := ⟨_, rfl⟩
  rw [ha] at h
  obtain ⟨w, hw⟩ : ∃ w, (featCov μ π L₀ R t a)⁻¹.mulVec d = w := ⟨_, rfl⟩
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)
  have hd : (featCov μ π L₀ R t a).mulVec w = d := by
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hq : meanSpeed μ π L₀ R t y₀ d s = dotProduct d w := by
    unfold meanSpeed; rw [ha, hw]
  -- `q = w ⬝ C w ≥ α ‖w‖²` and `q² = (d ⬝ w)² ≤ ‖d‖² ‖w‖²`
  have hqw : dotProduct d w = dotProduct w ((featCov μ π L₀ R t a).mulVec w) := by
    rw [hd, dotProduct_comm]
  have hcs : dotProduct d w ^ 2 ≤ dotProduct d d * dotProduct w w := by
    have e1 : dotProduct d d = ∑ i, d i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
    have e2 : dotProduct w w = ∑ i, w i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
    rw [e1, e2]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hαw := h w
  have hdd : 0 ≤ dotProduct d d := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hww : 0 ≤ dotProduct w w := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rw [hq]
  rw [← hqw] at hαw
  nlinarith [mul_le_mul_of_nonneg_left hcs hα.le, mul_le_mul_of_nonneg_left hαw hdd]

/-- Under `w ⬝ C w ≤ β ‖w‖²` at the point `a(s)`, the inverse-covariance speed is at least
`‖Δ‖²/β`: `‖Δ‖² ≤ β q`. -/
theorem le_mul_meanSpeed [DecidableEq ι] {β : ℝ} (hβ : 0 ≤ β) (y₀ d : ι → ℝ) (s : ℝ)
    (h : ∀ w, dotProduct w ((featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ d s)).mulVec w) ≤
      β * dotProduct w w) :
    dotProduct d d ≤ β * meanSpeed μ π L₀ R t y₀ d s := by
  obtain ⟨a, ha⟩ : ∃ a, meanLine μ π L₀ R t y₀ d s = a := ⟨_, rfl⟩
  rw [ha] at h
  obtain ⟨w, hw⟩ : ∃ w, (featCov μ π L₀ R t a)⁻¹.mulVec d = w := ⟨_, rfl⟩
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)
  have hd : (featCov μ π L₀ R t a).mulVec w = d := by
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hq : meanSpeed μ π L₀ R t y₀ d s = dotProduct d w := by
    unfold meanSpeed; rw [ha, hw]
  have hqw : dotProduct d w = dotProduct w ((featCov μ π L₀ R t a).mulVec w) := by
    rw [hd, dotProduct_comm]
  -- Cauchy–Schwarz for the covariance form with `u = d`, `v = w`: `(d ⬝ C w)² ≤ (d ⬝ C d)(w ⬝ C w)`
  have hcs := sq_dotProduct_featCov_le hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a d w
  rw [hd, dotProduct_comm w d, hqw] at hcs
  have hβd := h d
  have hq0 : 0 ≤ dotProduct w ((featCov μ π L₀ R t a).mulVec w) := by
    rw [← hqw, ← hq]; exact meanSpeed_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd y₀ d s
  have hdd : 0 ≤ dotProduct d d := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rw [hq, hqw]
  rcases hdd.eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hβ hq0
  · have h1 : dotProduct d d * dotProduct d d ≤
        dotProduct d d * (β * dotProduct w ((featCov μ π L₀ R t a).mulVec w)) := by
      calc dotProduct d d * dotProduct d d = dotProduct d d ^ 2 := by ring
        _ ≤ dotProduct d ((featCov μ π L₀ R t a).mulVec d) *
            dotProduct w ((featCov μ π L₀ R t a).mulVec w) := hcs
        _ ≤ β * dotProduct d d * dotProduct w ((featCov μ π L₀ R t a).mulVec w) :=
            mul_le_mul_of_nonneg_right hβd hq0
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1 h0

/-- **Response displacement is at most the information, mean side**: under the global upper
ellipticity `w ⬝ C_a w ≤ β ‖w‖²`, `‖m(a₁) − m(a₀)‖² ≤ 2 β KL(P_{a₁} ‖ P_{a₀})`. -/
theorem sq_dist_meanMap_le_famKL [Nonempty ι] {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ a w, dotProduct w ((featCov μ π L₀ R t a).mulVec w) ≤ β * dotProduct w w)
    (a₀ a₁ : ι → ℝ) :
    dotProduct (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) ≤ 2 * β * famKL μ π L₀ R t a₁ a₀ := by
  classical
  rw [famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  have hcont : ContinuousOn (fun s ↦ (1 - s) * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s)
      (uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
        (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)
        (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁))
  have hmono : ∫ s in (0 : ℝ)..1, (1 - s) * dotProduct d d ≤
      ∫ s in (0 : ℝ)..1, (1 - s) * (β * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s) := by
    have hc1 : Continuous fun s : ℝ ↦ (1 - s) * dotProduct d d :=
      (continuous_const.sub continuous_id).mul continuous_const
    refine intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable 0 1)
      (hcont.const_mul β |>.congr fun s _ ↦ by ring).intervalIntegrable ?_
    intro s hs
    exact mul_le_mul_of_nonneg_left
      (le_mul_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hβ _ d s fun w ↦ h _ w)
      (by linarith [hs.2])
  rw [integral_one_sub_mul_const] at hmono
  have e : ∫ s in (0 : ℝ)..1, (1 - s) * (β * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s) =
      β * ∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ ↦ by ring
  rw [e] at hmono
  linarith

/-- **Information is at most the response displacement, mean side**: under the global lower
ellipticity `α ‖w‖² ≤ w ⬝ C_a w`, `2 α KL(P_{a₁} ‖ P_{a₀}) ≤ ‖m(a₁) − m(a₀)‖²`. -/
theorem famKL_le_sq_dist_meanMap [Nonempty ι] {α : ℝ} (hα : 0 < α)
    (h : ∀ a w, α * dotProduct w w ≤ dotProduct w ((featCov μ π L₀ R t a).mulVec w))
    (a₀ a₁ : ι → ℝ) :
    2 * α * famKL μ π L₀ R t a₁ a₀ ≤ dotProduct (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) := by
  classical
  rw [famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  set d := meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀ with hd
  have hcont : ContinuousOn (fun s ↦ (1 - s) * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s)
      (uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
        (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)
        (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁))
  have hmono : ∫ s in (0 : ℝ)..1, (1 - s) * (α * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s)
      ≤ ∫ s in (0 : ℝ)..1, (1 - s) * dotProduct d d := by
    have hc1 : Continuous fun s : ℝ ↦ (1 - s) * dotProduct d d :=
      (continuous_const.sub continuous_id).mul continuous_const
    refine intervalIntegral.integral_mono_on zero_le_one
      (hcont.const_mul α |>.congr fun s _ ↦ by ring).intervalIntegrable
      (hc1.intervalIntegrable 0 1) ?_
    intro s hs
    exact mul_le_mul_of_nonneg_left
      (mul_meanSpeed_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hα _ d s fun w ↦ h _ w)
      (by linarith [hs.2])
  rw [integral_one_sub_mul_const] at hmono
  have e : ∫ s in (0 : ℝ)..1, (1 - s) * (α * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s) =
      α * ∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀) d s := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ ↦ by ring
  rw [e] at hmono
  linarith

omit [Nonempty X] ht hnd in
/-- The segment variance is the covariance form along the natural segment. -/
theorem segVar_eq_dotProduct (a v : ι → ℝ) (s : ℝ) :
    segVar μ π L₀ R t a v s = dotProduct v ((featCov μ π L₀ R t (a + s • v)).mulVec v) := by
  rw [dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR]; rfl

omit hnd in
/-- **Information is at most the data displacement, natural side**:
`2 KL(P_{a₁} ‖ P_{a₀}) ≤ t² β ‖a₁ − a₀‖²`. -/
theorem famKL_le_sq_dist_coeff {β : ℝ}
    (h : ∀ a w, dotProduct w ((featCov μ π L₀ R t a).mulVec w) ≤ β * dotProduct w w)
    (a₀ a₁ : ι → ℝ) :
    2 * famKL μ π L₀ R t a₁ a₀ ≤ t ^ 2 * β * dotProduct (a₁ - a₀) (a₁ - a₀) := by
  rw [famKL, mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ a₁]
  have hc1 : Continuous fun s : ℝ ↦ s * segVar μ π L₀ R t a₀ (a₁ - a₀) s :=
    continuous_id.mul (continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ _)
  have hc2 : Continuous fun s : ℝ ↦ s * (β * dotProduct (a₁ - a₀) (a₁ - a₀)) :=
    continuous_id.mul continuous_const
  have hmono : ∫ s in (0 : ℝ)..1, s * segVar μ π L₀ R t a₀ (a₁ - a₀) s ≤
      ∫ s in (0 : ℝ)..1, s * (β * dotProduct (a₁ - a₀) (a₁ - a₀)) := by
    refine intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable 0 1)
      (hc2.intervalIntegrable 0 1) fun s hs ↦ ?_
    rw [segVar_eq_dotProduct hπm hπi hπ hπpos hL₀m hL₀ hR]
    exact mul_le_mul_of_nonneg_left (h _ _) hs.1
  rw [integral_id_mul_const] at hmono
  nlinarith [sq_nonneg t]

omit hnd in
/-- **Data displacement is at most the information, natural side**:
`t² α ‖a₁ − a₀‖² ≤ 2 KL(P_{a₁} ‖ P_{a₀})`. -/
theorem famKL_ge_sq_dist_coeff {α : ℝ}
    (h : ∀ a w, α * dotProduct w w ≤ dotProduct w ((featCov μ π L₀ R t a).mulVec w))
    (a₀ a₁ : ι → ℝ) :
    t ^ 2 * α * dotProduct (a₁ - a₀) (a₁ - a₀) ≤ 2 * famKL μ π L₀ R t a₁ a₀ := by
  rw [famKL, mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ a₁]
  have hc1 : Continuous fun s : ℝ ↦ s * segVar μ π L₀ R t a₀ (a₁ - a₀) s :=
    continuous_id.mul (continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ _)
  have hc2 : Continuous fun s : ℝ ↦ s * (α * dotProduct (a₁ - a₀) (a₁ - a₀)) :=
    continuous_id.mul continuous_const
  have hmono : ∫ s in (0 : ℝ)..1, s * (α * dotProduct (a₁ - a₀) (a₁ - a₀)) ≤
      ∫ s in (0 : ℝ)..1, s * segVar μ π L₀ R t a₀ (a₁ - a₀) s := by
    refine intervalIntegral.integral_mono_on zero_le_one (hc2.intervalIntegrable 0 1)
      (hc1.intervalIntegrable 0 1) fun s hs ↦ ?_
    rw [segVar_eq_dotProduct hπm hπi hπ hπpos hL₀m hL₀ hR]
    exact mul_le_mul_of_nonneg_left (h _ _) hs.1
  rw [integral_id_mul_const] at hmono
  nlinarith [sq_nonneg t]

/-- **The mean map is Lipschitz**: `‖m(a₁) − m(a₀)‖ ≤ β t ‖a₁ − a₀‖` under the upper ellipticity. -/
theorem sq_dist_meanMap_le [Nonempty ι] {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ a w, dotProduct w ((featCov μ π L₀ R t a).mulVec w) ≤ β * dotProduct w w)
    (a₀ a₁ : ι → ℝ) :
    dotProduct (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) ≤
      (β * t) ^ 2 * dotProduct (a₁ - a₀) (a₁ - a₀) := by
  have h1 := sq_dist_meanMap_le_famKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hβ h a₀ a₁
  have h2 := famKL_le_sq_dist_coeff hπm hπi hπ hπpos hL₀m hL₀ hR ht h a₀ a₁
  nlinarith [mul_le_mul_of_nonneg_left h2 hβ]

/-- **The mean map is co-Lipschitz (quantitative identifiability)**:
`α t ‖a₁ − a₀‖ ≤ ‖m(a₁) − m(a₀)‖` under the lower ellipticity. -/
theorem le_sq_dist_meanMap [Nonempty ι] {α : ℝ} (hα : 0 < α)
    (h : ∀ a w, α * dotProduct w w ≤ dotProduct w ((featCov μ π L₀ R t a).mulVec w))
    (a₀ a₁ : ι → ℝ) :
    (α * t) ^ 2 * dotProduct (a₁ - a₀) (a₁ - a₀) ≤
      dotProduct (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
        (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) := by
  have h1 := famKL_le_sq_dist_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hα h a₀ a₁
  have h2 := famKL_ge_sq_dist_coeff hπm hπi hπ hπpos hL₀m hL₀ hR ht h a₀ a₁
  nlinarith [mul_le_mul_of_nonneg_left h2 hα.le]

/-- **The unconditional Lipschitz bound**: for bounded features `|Rᵢ| ≤ Mᵢ`,
`‖m(a₁) − m(a₀)‖ ≤ t (∑ Mᵢ²) ‖a₁ − a₀‖`. -/
theorem sq_dist_meanMap_le_of_bounds [Nonempty ι] {M : ι → ℝ} (hM : ∀ i x, |R i x| ≤ M i)
    (a₀ a₁ : ι → ℝ) :
    dotProduct (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) ≤
      ((∑ i, M i ^ 2) * t) ^ 2 * dotProduct (a₁ - a₀) (a₁ - a₀) :=
  sq_dist_meanMap_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (fun a w ↦ dotProduct_featCov_mulVec_le_of_bounds hπm hπi hπ hπpos hL₀m hL₀ hR hM a w) a₀ a₁

end

end Laplace.Multi
