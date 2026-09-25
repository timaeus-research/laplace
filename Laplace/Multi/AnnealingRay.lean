/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ReducedPotential
import Laplace.Multi.MeanSegment

/-!
# The annealing ray from the prior to the data

Fix the data (`a`) and let the temperature run: `P_t ∝ e^{−t L_a} π`, `t ∈ ℝ`, through the prior at
`t = 0`. For every bounded observable `d/dt ⟨φ⟩_t = −Cov_t(φ, L_a)` (`hasDerivAt_priorExp_temp`);
in particular the energy `E(t) = ⟨L₀⟩_{t,0}` satisfies `E' = −Var_t(L₀)` and is nonincreasing
(`hasDerivAt_energy_temp`, `energy_antitone`). The total variance budget is the energy released,
`∫₀ᵀ Var_u(L₀) du = E(0) − E(T)` (`integral_var_eq_energy_drop`); the information acquired from
the prior is `KL(P_T ‖ P_0) = ∫₀ᵀ u Var_u(L₀) du` (`rayKL_eq`), hence at most `T (E(0) − E(T))`
(`rayKL_le`); and the change of any observable along the ray is controlled by its own variance
budget and the energy released, `(⟨φ⟩_T − ⟨φ⟩_0)² ≤ (∫₀ᵀ Var_u φ du)(E(0) − E(T))`
(`sq_priorExp_sub_le_ray`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] in
theorem affLoss_zero_eq_fun (L₀ : X → ℝ) (R : ι → X → ℝ) : affLoss L₀ R 0 = L₀ :=
  funext fun x ↦ by simp [affLoss]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

/-- **The temperature response of any observable**: `d/dt ⟨φ⟩_{t,a} = −Cov_{t,a}(φ, L_a)`. -/
theorem hasDerivAt_priorExp_temp (a : ι → ℝ) (t₀ : ℝ) {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun t ↦ priorExp μ π (affLoss L₀ R a) φ t)
      (-priorCov μ π (affLoss L₀ R a) φ (affLoss L₀ R a) t₀) t₀ := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hline : HasDerivAt (fun t : ℝ ↦ natCoord t a) (natCoord 1 a) t₀ := by
    have e : (fun t : ℝ ↦ natCoord t a) = fun t : ℝ ↦ t • natCoord 1 a :=
      funext fun t ↦ natCoord_eq_smul t a
    rw [e]
    simpa using (hasDerivAt_id t₀).smul_const (natCoord 1 a)
  have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos
    (natCoord t₀ a)).comp_hasDerivAt t₀ hline
  have e2 : (fun t ↦ priorExp μ π (affLoss L₀ R a) φ t) =
      (fun θ ↦ priorExp μ π (affLoss (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) θ) φ 1) ∘
        (fun t ↦ natCoord t a) := by
    funext t
    simp only [Function.comp, priorExp_natCoord]
  rw [e2]
  refine h.congr_deriv ?_
  rw [obsMapDeriv_apply hπm hπi hπ hπpos measurable_const h0 hS' hφm hφb one_pos, priorCov_natCoord]
  have e3 : dirLoss (jointStat L₀ R) (natCoord 1 a) = affLoss L₀ R a :=
    funext fun x ↦ by rw [dirLoss_jointStat_natCoord, one_mul]
  rw [e3]
  ring

/-- The energy `E(t) = ⟨L₀⟩_{t,0}` decreases at the rate of its variance: `E' = −Var_t(L₀)`. -/
theorem hasDerivAt_energy_temp (t₀ : ℝ) :
    HasDerivAt (fun t ↦ priorExp μ π (affLoss L₀ R 0) L₀ t)
      (-priorCov μ π (affLoss L₀ R 0) L₀ L₀ t₀) t₀ :=
  (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 t₀ ⟨hL₀m, M₀, hL₀⟩).congr_deriv
    (by rw [affLoss_zero_eq_fun L₀ R])

/-- **The energy is nonincreasing along the annealing ray** (on all of `ℝ`). -/
theorem energy_antitone : Antitone (fun t ↦ priorExp μ π (affLoss L₀ R 0) L₀ t) := by
  refine antitone_of_deriv_nonpos
    (fun t ↦ (hasDerivAt_energy_temp hπm hπi hπ hπpos hL₀m hL₀ hR t).differentiableAt) fun t ↦ ?_
  rw [(hasDerivAt_energy_temp hπm hπi hπ hπpos hL₀m hL₀ hR t).deriv, neg_nonpos]
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0 ⟨hL₀m, M₀, hL₀⟩

/-- Posterior covariances are continuous in the temperature. -/
theorem continuous_priorCov_temp (a : ι → ℝ) {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    Continuous (fun t ↦ priorCov μ π (affLoss L₀ R a) φ ψ t) := by
  have h1 : Continuous (fun t ↦ priorExp μ π (affLoss L₀ R a) (fun x ↦ φ x * ψ x) t) :=
    continuous_iff_continuousAt.2 fun t ↦
      (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR a t (hφ.mul hψ)).continuousAt
  have h2 : Continuous (fun t ↦ priorExp μ π (affLoss L₀ R a) φ t) :=
    continuous_iff_continuousAt.2 fun t ↦
      (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR a t hφ).continuousAt
  have h3 : Continuous (fun t ↦ priorExp μ π (affLoss L₀ R a) ψ t) :=
    continuous_iff_continuousAt.2 fun t ↦
      (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR a t hψ).continuousAt
  exact h1.sub (h2.mul h3)

/-- **The variance budget is the energy released**: `∫₀ᵀ Var_u(L₀) du = E(0) − E(T)`. -/
theorem integral_var_eq_energy_drop (T : ℝ) :
    ∫ u in (0 : ℝ)..T, priorCov μ π (affLoss L₀ R 0) L₀ L₀ u =
      priorExp μ π (affLoss L₀ R 0) L₀ 0 - priorExp μ π (affLoss L₀ R 0) L₀ T := by
  have hcont := continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 ⟨hL₀m, M₀, hL₀⟩
    ⟨hL₀m, M₀, hL₀⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u ↦ -priorExp μ π (affLoss L₀ R 0) L₀ u)
    (f' := fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)
    (fun u _ ↦ ((hasDerivAt_energy_temp hπm hπi hπ hπpos hL₀m hL₀ hR u).neg).congr_deriv
      (neg_neg _)) (hcont.intervalIntegrable 0 T)
  rw [h]
  ring

/-- **The information acquired along the ray**: `KL(P_T ‖ P_0) = ∫₀ᵀ u Var_u(L₀) du`, where
`P_0 = π̄` is the prior. -/
theorem rayKL_eq (T : ℝ) :
    mixKL μ π L₀ (fun x ↦ -L₀ x) T 0 1 =
      ∫ u in (0 : ℝ)..T, u * priorCov μ π (affLoss L₀ R 0) L₀ L₀ u := by
  have hΔm : Measurable (fun x ↦ -L₀ x) := hL₀m.neg
  have hT := tiltData_baseWeight_of_bounded (μ := μ) (Δ := fun x ↦ -L₀ x) hπm hπi
    (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hΔm (M := M₀)
    (fun x ↦ by rw [abs_neg]; exact hL₀ x) T
  have hkl := hT.mixKL_eq (fun x ↦ (hπ x).le) 0 1
  -- the primitive of `u Var_u`
  have hg : ∀ u, HasDerivAt (fun u ↦ Real.log (∫ x, π x ∂μ) - affLogZ μ π L₀ R u 0 -
      u * priorExp μ π (affLoss L₀ R 0) L₀ u) (u * priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) u := by
    intro u
    have h := ((hasDerivAt_const u (Real.log (∫ x, π x ∂μ))).sub
      (hasDerivAt_affLogZ_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 u)).sub
      ((hasDerivAt_id u).mul (hasDerivAt_energy_temp hπm hπi hπ hπpos hL₀m hL₀ hR u))
    refine h.congr_deriv ?_
    simp only [dotJ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, id_eq]
    ring
  have hcont : Continuous (fun u ↦ u * priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) :=
    continuous_id.mul (continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 ⟨hL₀m, M₀, hL₀⟩
      ⟨hL₀m, M₀, hL₀⟩)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hg u)
    (hcont.intervalIntegrable 0 T)
  rw [hftc, hkl]
  unfold mixLogZ mixExp
  have e0 : pathLoss L₀ (fun x ↦ -L₀ x) 0 = affLoss L₀ R 0 := by
    funext x
    simp [pathLoss, affLoss]
  have e1 : pathLoss L₀ (fun x ↦ -L₀ x) 1 = fun _ ↦ (0 : ℝ) := by
    funext x
    simp [pathLoss]
  rw [e0, e1]
  have hZ0 : priorZ μ π (fun _ ↦ (0 : ℝ)) T = ∫ x, π x ∂μ := by
    unfold priorZ
    simp
  have hA0 : affLogZ μ π L₀ R 0 0 = Real.log (∫ x, π x ∂μ) := by
    unfold affLogZ priorZ
    simp
  have hneg : priorExp μ π (affLoss L₀ R 0) (fun x ↦ -L₀ x) T =
      -priorExp μ π (affLoss L₀ R 0) L₀ T := by
    unfold priorExp
    simp only [neg_mul, integral_neg, neg_div]
  rw [hZ0, hA0, hneg]
  unfold affLogZ
  ring

/-- **Information is at most temperature times energy released**:
`KL(P_T ‖ P_0) ≤ T (E(0) − E(T))` for `T ≥ 0`. -/
theorem rayKL_le {T : ℝ} (hT : 0 ≤ T) :
    mixKL μ π L₀ (fun x ↦ -L₀ x) T 0 1 ≤
      T * (priorExp μ π (affLoss L₀ R 0) L₀ 0 - priorExp μ π (affLoss L₀ R 0) L₀ T) := by
  rw [rayKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR T,
    ← integral_var_eq_energy_drop hπm hπi hπ hπpos hL₀m hL₀ hR T,
    ← intervalIntegral.integral_const_mul]
  have hcont := continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 ⟨hL₀m, M₀, hL₀⟩
    ⟨hL₀m, M₀, hL₀⟩
  refine intervalIntegral.integral_mono_on hT ((continuous_id.mul hcont).intervalIntegrable 0 T)
    ((continuous_const.mul hcont).intervalIntegrable 0 T) fun u hu ↦ ?_
  exact mul_le_mul_of_nonneg_right hu.2
    (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 ⟨hL₀m, M₀, hL₀⟩)

/-- **The change of an observable along the ray is bounded by its variance budget and the energy
released**: `(⟨φ⟩_T − ⟨φ⟩_0)² ≤ (∫₀ᵀ Var_u(φ) du) (E(0) − E(T))`. -/
theorem sq_priorExp_sub_le_ray {φ : X → ℝ} (hφ : Bdd φ) {T : ℝ} (hT : 0 < T) :
    (priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0) ^ 2 ≤
      (∫ u in (0 : ℝ)..T, priorCov μ π (affLoss L₀ R 0) φ φ u) *
        (priorExp μ π (affLoss L₀ R 0) L₀ 0 - priorExp μ π (affLoss L₀ R 0) L₀ T) := by
  have hL : Bdd L₀ := ⟨hL₀m, M₀, hL₀⟩
  have hf : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) φ φ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hφ
  have hg : Continuous (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) :=
    continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hL hL
  have hf0 : ∀ u, 0 ≤ priorCov μ π (affLoss L₀ R 0) φ φ u := fun u ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 hφ
  have hg0 : ∀ u, 0 ≤ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u := fun u ↦
    priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := u) 0 hL
  -- the change as the integral of the covariance with the loss
  have hD : ∀ u, HasDerivAt (fun u ↦ priorExp μ π (affLoss L₀ R 0) φ u)
      (-priorCov μ π (affLoss L₀ R 0) φ L₀ u) u := fun u ↦
    (hasDerivAt_priorExp_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 u hφ).congr_deriv
      (by rw [affLoss_zero_eq_fun L₀ R])
  have hcovc : Continuous (fun u ↦ -priorCov μ π (affLoss L₀ R 0) φ L₀ u) :=
    (continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 hφ hL).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hD u)
    (hcovc.intervalIntegrable 0 T)
  -- pointwise Cauchy–Schwarz
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
  have hΔ : |priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0| ≤
      ∫ u in (0 : ℝ)..T, Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
        priorCov μ π (affLoss L₀ R 0) L₀ L₀ u) := by
    rw [← hftc]
    calc |∫ u in (0 : ℝ)..T, -priorCov μ π (affLoss L₀ R 0) φ L₀ u|
        ≤ ∫ u in (0 : ℝ)..T, |-priorCov μ π (affLoss L₀ R 0) φ L₀ u| :=
          intervalIntegral.abs_integral_le_integral_abs hT.le
      _ ≤ _ := intervalIntegral.integral_mono_on hT.le (hcovc.abs.intervalIntegrable 0 T)
          (hsqrtc.intervalIntegrable 0 T) fun u _ ↦ by rw [abs_neg]; exact hcs u
  -- rescale to `[0, 1]` and apply Cauchy–Schwarz for integrals
  have hres : ∀ k : ℝ → ℝ, (∫ u in (0 : ℝ)..T, k u) = T * ∫ s in (0 : ℝ)..1, k (T * s) := by
    intro k
    rw [intervalIntegral.integral_comp_mul_left k hT.ne', mul_zero, mul_one, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  have hCS := sq_integral_sqrt_mul_le
    (f := fun s ↦ priorCov μ π (affLoss L₀ R 0) φ φ (T * s))
    (g := fun s ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s))
    (hf.comp (continuous_const.mul continuous_id)).continuousOn
    (hg.comp (continuous_const.mul continuous_id)).continuousOn
    (fun s _ ↦ hf0 _) (fun s _ ↦ hg0 _)
  have h1 := hres (fun u ↦ Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
    priorCov μ π (affLoss L₀ R 0) L₀ L₀ u))
  have h2 := hres (fun u ↦ priorCov μ π (affLoss L₀ R 0) φ φ u)
  have h3 := hres (fun u ↦ priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)
  have hsq : (∫ u in (0 : ℝ)..T, Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
      priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)) ^ 2 ≤
      (∫ u in (0 : ℝ)..T, priorCov μ π (affLoss L₀ R 0) φ φ u) *
        ∫ u in (0 : ℝ)..T, priorCov μ π (affLoss L₀ R 0) L₀ L₀ u := by
    rw [h1, h2, h3, mul_pow]
    calc T ^ 2 * (∫ s in (0 : ℝ)..1, Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ (T * s) *
          priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s))) ^ 2
        ≤ T ^ 2 * ((∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R 0) φ φ (T * s)) *
          ∫ s in (0 : ℝ)..1, priorCov μ π (affLoss L₀ R 0) L₀ L₀ (T * s)) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg T)
      _ = _ := by ring
  calc (priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0) ^ 2
      = |priorExp μ π (affLoss L₀ R 0) φ T - priorExp μ π (affLoss L₀ R 0) φ 0| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (∫ u in (0 : ℝ)..T, Real.sqrt (priorCov μ π (affLoss L₀ R 0) φ φ u *
          priorCov μ π (affLoss L₀ R 0) L₀ L₀ u)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hΔ 2
    _ ≤ _ := hsq
    _ = _ := by rw [integral_var_eq_energy_drop hπm hπi hπ hπpos hL₀m hL₀ hR T]

end

end Laplace.Multi
