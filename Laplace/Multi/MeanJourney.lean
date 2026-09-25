/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ReducedPotential
import Laplace.Multi.LossCurvature
import Laplace.Multi.MeanSegment
import Laplace.Multi.HalfspaceProjection

/-!
# The mean journey: the same information through the inverse covariance

The natural (e-)journey from `P_{t,a₀}` to `P_{t,a₁}` is the straight segment `a₀ + s(a₁ − a₀)` of
data coefficients; its information cost is
`KL(P_{a₁} ‖ P_{a₀}) = t² ∫₀¹ s Var_{a(s)}(R_{a₁−a₀}) ds` (`mixKL_eq_integral_mul_var`): the
covariance along a straight natural journey, weighted by `s`. The **mean (m-)journey** is the
straight segment `M(s) = m(a₀) + s (m(a₁) − m(a₀))` of responses, which stays in the open convex
response space `int K` (`segment_mem_interior_momentBody`); its coefficient `a(s) = θ(M(s))`
(`meanLine`) moves with velocity `−(1/t) Cov_{a(s)}(R,R)⁻¹ Δ` (`hasDerivAt_meanLine`,
`invJac_apply_eq`), and the dual potential `I` of `DualPotential` has along it the derivative
`−t ⟨Δ, a(s)⟩` and the second derivative

  `q(s) = Δ ⬝ Cov_{a(s)}(R,R)⁻¹ Δ ≥ 0`

(`meanSpeed`, `hasDerivAt_meanLine_pairing`, `meanSpeed_nonneg`), the inverse-covariance form.
Integrating twice (`famKL_eq_integral_meanSpeed`):

  `KL(P_{a₁} ‖ P_{a₀}) = ∫₀¹ (1 − s) q(s) ds`,

so the **same information cost** is spent by the two journeys with opposite weights
(`famKL_e_journey_eq_m_journey`):

  `t² ∫₀¹ s Var_{a₀+s(a₁−a₀)}(R_{a₁−a₀}) ds = KL(P_{a₁} ‖ P_{a₀})
    = ∫₀¹ (1 − s) Δ ⬝ C_{θ(M(s))}⁻¹ Δ ds`.

Integrating once gives Jeffreys' symmetrised divergence
`∫₀¹ q = KL(P_{a₁}‖P_{a₀}) + KL(P_{a₀}‖P_{a₁})` (`famKL_add_famKL_eq_integral_meanSpeed`), hence
the inverse-covariance length of the mean segment is at most the square root of the Jeffreys
divergence (`sq_integral_sqrt_meanSpeed_le`).

In mean coordinates the relative entropy to the featureless member `P_{t,0}`,
`𝒮_t(M) = −KL(P_{θ(M)} ‖ P_{t,0})` (`meanEntropy`), is `I(m(0)) − I(M)`, concave on the response
space (`meanEntropy_concaveOn`), with derivative `t ⟨Δ, a(s)⟩` and second derivative `−q(s)` along
mean segments (`hasDerivAt_meanEntropy_line`, `hasDerivAt_meanEntropy_line_deriv`); along the mean
journey from the featureless response `m(0)` the entropy decreases (`meanEntropy_line_antitoneOn`)
and `−𝒮_t(M₁) = ∫₀¹ (1 − s) q(s) ds` (`meanEntropy_eq_neg_integral`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The coefficient of the mean segment `M₀ + s Δ`: `a(s) = θ(M₀ + s Δ)`. -/
noncomputable def meanLine (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (y₀ d : ι → ℝ) (s : ℝ) : ι → ℝ :=
  Function.invFun (meanMap μ π L₀ R t) (y₀ + s • d)

/-- The inverse-covariance speed of the mean segment, `q(s) = Δ ⬝ Cov_{a(s)}(R,R)⁻¹ Δ`. -/
noncomputable def meanSpeed [DecidableEq ι] (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ)
    (t : ℝ) (y₀ d : ι → ℝ) (s : ℝ) : ℝ :=
  dotProduct d ((featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ d s))⁻¹.mulVec d)

/-- The relative entropy of the response `M` to the featureless member `P_{t,0}`,
`𝒮_t(M) = −KL(P_{θ(M)} ‖ P_{t,0})`. -/
noncomputable def meanEntropy (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (M : ι → ℝ) : ℝ :=
  -famKL μ π L₀ R t (Function.invFun (meanMap μ π L₀ R t) M) 0

theorem dotJ_zero_left (v : ι → ℝ) : dotJ 0 v = 0 := by simp [dotJ]

theorem dotJ_zero_right (v : ι → ℝ) : dotJ v 0 = 0 := by simp [dotJ]

omit [Fintype ι] in
/-- The response space is convex: mean segments with endpoints in `int K` stay in `int K`. -/
theorem segment_mem_interior_momentBody {π : X → ℝ} {R : ι → X → ℝ} {y₀ y₁ : ι → ℝ}
    (h₀ : y₀ ∈ interior (momentBody μ π R)) (h₁ : y₁ ∈ interior (momentBody μ π R)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : y₀ + s • (y₁ - y₀) ∈ interior (momentBody μ π R) :=
  (convex_momentBody R).interior.add_smul_sub_mem h₀ h₁ hs

section

variable [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

theorem meanMap_mem_interior (a : ι → ℝ) : meanMap μ π L₀ R t a ∈ interior (momentBody μ π R) := by
  rw [← range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  exact ⟨a, rfl⟩

theorem meanMap_meanLine {y₀ d : ι → ℝ} {s : ℝ} (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    meanMap μ π L₀ R t (meanLine μ π L₀ R t y₀ d s) = y₀ + s • d := by
  have hmem : y₀ + s • d ∈ Set.range (meanMap μ π L₀ R t) := by
    rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]; exact hM
  exact Function.invFun_eq hmem

omit [Nonempty ι] in
theorem meanLine_zero (a₀ : ι → ℝ) (d : ι → ℝ) :
    meanLine μ π L₀ R t (meanMap μ π L₀ R t a₀) d 0 = a₀ := by
  simp only [meanLine, zero_smul, add_zero]
  exact invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a₀

omit [Nonempty ι] in
theorem meanLine_one (a₀ a₁ : ι → ℝ) :
    meanLine μ π L₀ R t (meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) 1 = a₁ := by
  simp only [meanLine, one_smul, add_sub_cancel]
  exact invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a₁

/-- The coefficient of the mean segment moves with the inverse Jacobian of the mean map. -/
theorem hasDerivAt_meanLine {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (meanLine μ π L₀ R t y₀ d)
      (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
        (meanLine μ π L₀ R t y₀ d s) d) s := by
  have h := (hasStrictFDerivAt_invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht
    hnd (meanLine μ π L₀ R t y₀ d s)).hasFDerivAt
  rw [meanMap_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM] at h
  exact h.comp_hasDerivAt s (hasDerivAt_affineLine y₀ d s)

omit [Nonempty ι] in
/-- The Hessian of the dual potential is the inverse covariance matrix. -/
theorem dualHessian_eq_inv_mulVec [DecidableEq ι] (a v : ι → ℝ) :
    dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v =
      (featCov μ π L₀ R t a)⁻¹.mulVec v := by
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)
  have h := featCov_mulVec_dualHessian hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a v
  calc dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v
      = ((featCov μ π L₀ R t a)⁻¹ * featCov μ π L₀ R t a).mulVec
          (dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v) := by
        rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    _ = (featCov μ π L₀ R t a)⁻¹.mulVec ((featCov μ π L₀ R t a).mulVec
          (dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v)) := by
        rw [Matrix.mulVec_mulVec]
    _ = (featCov μ π L₀ R t a)⁻¹.mulVec v := by rw [h]

omit [Nonempty ι] in
/-- The inverse Jacobian of the mean map is `−(1/t)` times the inverse covariance. -/
theorem invJac_apply_eq [DecidableEq ι] (a v : ι → ℝ) :
    invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v =
      (-t)⁻¹ • (featCov μ π L₀ R t a)⁻¹.mulVec v := by
  rw [← dualHessian_eq_inv_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a v]
  unfold dualHessian
  rw [_root_.smul_apply, smul_smul, inv_mul_cancel₀ (by linarith : (-t) ≠ 0), one_smul]

/-- The dual potential along a mean segment: `d/ds I(M₀ + sΔ) = −t ⟨Δ, a(s)⟩`. -/
theorem hasDerivAt_dualPotential_meanLine {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun s ↦ dualPotential μ π L₀ R t (y₀ + s • d))
      (-t * dotJ d (meanLine μ π L₀ R t y₀ d s)) s := by
  have h := hasFDerivAt_dualPotential hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
    (meanLine μ π L₀ R t y₀ d s)
  rw [meanMap_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM] at h
  have h2 := h.comp_hasDerivAt s (hasDerivAt_affineLine y₀ d s)
  refine h2.congr_deriv ?_
  rw [_root_.smul_apply, dotCLM_apply, smul_eq_mul]

/-- **The second derivative of the dual potential along a mean segment is the inverse-covariance
form**: `d/ds (−t ⟨Δ, a(s)⟩) = Δ ⬝ Cov_{a(s)}(R,R)⁻¹ Δ`. -/
theorem hasDerivAt_meanLine_pairing [DecidableEq ι] {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun s ↦ -t * dotJ d (meanLine μ π L₀ R t y₀ d s))
      (meanSpeed μ π L₀ R t y₀ d s) s := by
  have ha := hasDerivAt_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM
  have hsum : HasDerivAt (fun s ↦ ∑ i, d i * meanLine μ π L₀ R t y₀ d s i)
      (∑ i, d i * invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
        (meanLine μ π L₀ R t y₀ d s) d i) s :=
    HasDerivAt.fun_sum fun i _ ↦ (hasDerivAt_pi.mp ha i).const_mul (d i)
  have h := hsum.const_mul (-t)
  refine h.congr_deriv ?_
  rw [invJac_apply_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  unfold meanSpeed
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have ht' : t ≠ 0 := ht.ne'
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp

omit [Nonempty ι] in
/-- The inverse-covariance form is nonnegative: `Δ ⬝ C⁻¹ Δ = Var(R_{C⁻¹Δ}) ≥ 0`. -/
theorem meanSpeed_nonneg [DecidableEq ι] (y₀ d : ι → ℝ) (s : ℝ) :
    0 ≤ meanSpeed μ π L₀ R t y₀ d s := by
  obtain ⟨a, ha⟩ : ∃ a, meanLine μ π L₀ R t y₀ d s = a := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, (featCov μ π L₀ R t a)⁻¹.mulVec d = w := ⟨_, rfl⟩
  have hunit := (Matrix.isUnit_iff_isUnit_det _).1
    (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht a)
  have hd : (featCov μ π L₀ R t a).mulVec w = d := by
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have e : meanSpeed μ π L₀ R t y₀ d s =
      priorCov μ π (affLoss L₀ R a) (dirLoss R w) (dirLoss R w) t := by
    unfold meanSpeed
    rw [ha, hw]
    conv_lhs => rw [← hd]
    rw [← sum_mul_priorCov_eq hν hR (bdd_dirLoss hR w) w]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a w i, mul_comm]
  rw [e]
  exact priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR a (bdd_dirLoss hR w)

omit [Nonempty ι] hnd in
/-- The covariance matrix depends continuously on the data coefficient. -/
theorem continuous_featCov : Continuous (featCov μ π L₀ R t) := by
  refine continuous_matrix fun i j ↦ ?_
  obtain ⟨hijm, Mij, hijb⟩ := (hR i).mul (hR j)
  obtain ⟨him, Mi, hib⟩ := hR i
  obtain ⟨hjm, Mj, hjb⟩ := hR j
  simp only [featCov, Matrix.of_apply, priorCov]
  exact (continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hijm hijb ht).sub
    ((continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR him hib ht).mul
      (continuous_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hjm hjb ht))

/-- The inverse-covariance speed is continuous along a mean segment inside the response space. -/
theorem continuousOn_meanSpeed [DecidableEq ι] {y₀ y₁ : ι → ℝ}
    (h₀ : y₀ ∈ interior (momentBody μ π R)) (h₁ : y₁ ∈ interior (momentBody μ π R)) :
    ContinuousOn (meanSpeed μ π L₀ R t y₀ (y₁ - y₀)) (Icc 0 1) := by
  have hline : ContinuousOn (meanLine μ π L₀ R t y₀ (y₁ - y₀)) (Icc 0 1) := fun s hs ↦
    (hasDerivAt_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
      (segment_mem_interior_momentBody h₀ h₁ hs)).continuousAt.continuousWithinAt
  have hinv : ContinuousOn
      (fun s ↦ (featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) s))⁻¹) (Icc 0 1) := by
    intro s hs
    have hdet : (featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) s)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1
        (isUnit_featCov hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht _)).ne_zero
    have hc : ContinuousAt Inv.inv (featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) s)) := by
      refine continuousAt_matrix_inv _ ?_
      have := NormedRing.inverse_continuousAt (Units.mk0 _ hdet)
      simpa using this
    have hfeat : ContinuousOn
        (fun s ↦ featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) s)) (Icc 0 1) :=
      (continuous_featCov hπm hπi hπ hπpos hL₀m hL₀ hR ht).comp_continuousOn hline
    exact ContinuousAt.comp_continuousWithinAt (g := Inv.inv)
      (f := fun u ↦ featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) u)) (x := s) hc
      (hfeat s hs)
  have hij : ∀ i j, ContinuousOn
      (fun s ↦ (featCov μ π L₀ R t (meanLine μ π L₀ R t y₀ (y₁ - y₀) s))⁻¹ i j) (Icc 0 1) :=
    fun i j ↦ (continuous_id.matrix_elem i j).comp_continuousOn hinv
  unfold meanSpeed
  simp only [dotProduct, Matrix.mulVec]
  exact continuousOn_finsetSum _ fun i _ ↦ continuousOn_const.mul
    (continuousOn_finsetSum _ fun j _ ↦ (hij i j).mul continuousOn_const)

/-- The primitive of `(1 − s) q(s)`: `(1 − s) I'(s) + I(s)`. -/
theorem hasDerivAt_meanJourney_primitive [DecidableEq ι] {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun s ↦ (1 - s) * (-t * dotJ d (meanLine μ π L₀ R t y₀ d s)) +
        dualPotential μ π L₀ R t (y₀ + s • d))
      ((1 - s) * meanSpeed μ π L₀ R t y₀ d s) s := by
  have hp := hasDerivAt_meanLine_pairing hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM
  have hf := hasDerivAt_dualPotential_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM
  have h := (((hasDerivAt_id s).const_sub 1).mul hp).add hf
  refine h.congr_deriv ?_
  simp only [id_eq]
  ring

/-- **The mean journey**: `KL(P_{a₁} ‖ P_{a₀}) = ∫₀¹ (1 − s) Δ ⬝ Cov_{θ(M(s))}(R,R)⁻¹ Δ ds`
along the mean segment `M(s) = m(a₀) + s (m(a₁) − m(a₀))`. -/
theorem famKL_eq_integral_meanSpeed [DecidableEq ι] (a₀ a₁ : ι → ℝ) :
    famKL μ π L₀ R t a₁ a₀ = ∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π L₀ R t
      (meanMap μ π L₀ R t a₀) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, meanMap μ π L₀ R t a₀ = y := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y, meanMap μ π L₀ R t a₁ = y := ⟨_, rfl⟩
  have h₀ := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀
  have h₁ := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁
  rw [hy₀] at h₀
  rw [hy₁] at h₁
  rw [hy₀, hy₁]
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, y₀ + s • (y₁ - y₀) ∈ interior (momentBody μ π R) :=
    fun s hs ↦ segment_mem_interior_momentBody h₀ h₁ hs
  have hcont : ContinuousOn (fun s ↦ (1 - s) * meanSpeed μ π L₀ R t y₀ (y₁ - y₀) s)
      (uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd h₀ h₁)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ (1 - s) * (-t * dotJ (y₁ - y₀) (meanLine μ π L₀ R t y₀ (y₁ - y₀) s)) +
      dualPotential μ π L₀ R t (y₀ + s • (y₁ - y₀)))
    (f' := fun s ↦ (1 - s) * meanSpeed μ π L₀ R t y₀ (y₁ - y₀) s)
    (fun s hs ↦ hasDerivAt_meanJourney_primitive hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
      (hseg s (by rwa [Set.uIcc_of_le zero_le_one] at hs)))
    hcont.intervalIntegrable
  rw [hFTC]
  have h0 : meanLine μ π L₀ R t y₀ (y₁ - y₀) 0 = a₀ := by
    rw [← hy₀]; exact meanLine_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ _
  simp only [sub_self, zero_mul, zero_add, one_smul, add_sub_cancel, zero_smul, add_zero,
    sub_zero, one_mul, h0]
  rw [famKL, mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a₀ a₁,
    hy₀, hy₁, dotJ_comm (y₁ - y₀) a₀]
  ring

/-- **The two journeys spend the same information**: the covariance along the straight natural
journey, weighted by `s`, equals the inverse covariance along the straight mean journey, weighted by
`1 − s`; both are `KL(P_{a₁} ‖ P_{a₀})`. -/
theorem famKL_e_journey_eq_m_journey [DecidableEq ι] (a₀ a₁ : ι → ℝ) :
    t ^ 2 * ∫ s in (0 : ℝ)..1, s * segVar μ π L₀ R t a₀ (a₁ - a₀) s =
      ∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π L₀ R t
        (meanMap μ π L₀ R t a₀) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s := by
  rw [← famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁, famKL,
    mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a₀ a₁]

/-- **Jeffreys' divergence is the integrated inverse-covariance form**:
`KL(P_{a₁} ‖ P_{a₀}) + KL(P_{a₀} ‖ P_{a₁}) = ∫₀¹ Δ ⬝ Cov_{θ(M(s))}(R,R)⁻¹ Δ ds`. -/
theorem famKL_add_famKL_eq_integral_meanSpeed [DecidableEq ι] (a₀ a₁ : ι → ℝ) :
    famKL μ π L₀ R t a₁ a₀ + famKL μ π L₀ R t a₀ a₁ = ∫ s in (0 : ℝ)..1, meanSpeed μ π L₀ R t
      (meanMap μ π L₀ R t a₀) (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, meanMap μ π L₀ R t a₀ = y := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y, meanMap μ π L₀ R t a₁ = y := ⟨_, rfl⟩
  have h₀ := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀
  have h₁ := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁
  rw [hy₀] at h₀
  rw [hy₁] at h₁
  rw [hy₀, hy₁]
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, y₀ + s • (y₁ - y₀) ∈ interior (momentBody μ π R) :=
    fun s hs ↦ segment_mem_interior_momentBody h₀ h₁ hs
  have hcont : ContinuousOn (meanSpeed μ π L₀ R t y₀ (y₁ - y₀)) (uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd h₀ h₁
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ -t * dotJ (y₁ - y₀) (meanLine μ π L₀ R t y₀ (y₁ - y₀) s))
    (f' := meanSpeed μ π L₀ R t y₀ (y₁ - y₀))
    (fun s hs ↦ hasDerivAt_meanLine_pairing hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
      (hseg s (by rwa [Set.uIcc_of_le zero_le_one] at hs)))
    hcont.intervalIntegrable
  rw [hFTC]
  have h0 : meanLine μ π L₀ R t y₀ (y₁ - y₀) 0 = a₀ := by
    rw [← hy₀]; exact meanLine_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ _
  have h1 : meanLine μ π L₀ R t y₀ (y₁ - y₀) 1 = a₁ := by
    rw [← hy₀, ← hy₁]; exact meanLine_one hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁
  rw [h0, h1, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR a₁ a₀,
    famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR a₀ a₁, hy₀, hy₁]
  have hs : ∑ i, (a₀ i - a₁ i) * y₁ i + ∑ i, (a₁ i - a₀ i) * y₀ i =
      -dotJ (y₁ - y₀) a₁ + dotJ (y₁ - y₀) a₀ := by
    simp only [dotJ, Pi.sub_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  linear_combination t * hs

/-- The inverse-covariance length of the mean segment is bounded by the square root of the Jeffreys
divergence: `(∫₀¹ √q)² ≤ KL(P_{a₁} ‖ P_{a₀}) + KL(P_{a₀} ‖ P_{a₁})`. -/
theorem sq_integral_sqrt_meanSpeed_le [DecidableEq ι] (a₀ a₁ : ι → ℝ) :
    (∫ s in (0 : ℝ)..1, Real.sqrt (meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀) s)) ^ 2 ≤
      famKL μ π L₀ R t a₁ a₀ + famKL μ π L₀ R t a₀ a₁ := by
  rw [famKL_add_famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀ a₁]
  have h := sq_integral_sqrt_mul_le
    (f := meanSpeed μ π L₀ R t (meanMap μ π L₀ R t a₀)
      (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t a₀)) (g := fun _ ↦ (1 : ℝ))
    (continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
      (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₀)
      (meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁))
    continuousOn_const (fun s _ ↦ meanSpeed_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd _ _ s)
    (fun _ _ ↦ zero_le_one)
  simpa using h

/-! ### The relative entropy in mean coordinates -/

omit [Nonempty ι] in
theorem meanEntropy_meanMap (a : ι → ℝ) :
    meanEntropy μ π L₀ R t (meanMap μ π L₀ R t a) = -famKL μ π L₀ R t a 0 := by
  unfold meanEntropy
  rw [invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a]

omit [Nonempty ι] in
/-- `𝒮_t(m(a)) = I(m(0)) − I(m(a))`: the entropy in mean coordinates is the dual potential,
reflected and anchored at the featureless response. -/
theorem meanEntropy_eq_dual (a : ι → ℝ) :
    meanEntropy μ π L₀ R t (meanMap μ π L₀ R t a) =
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) -
        dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) := by
  rw [meanEntropy_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a, famKL,
    mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd 0 a, dotJ_zero_left]
  ring

/-- **The relative entropy is concave in mean coordinates.** -/
theorem meanEntropy_concaveOn :
    ConcaveOn ℝ (Set.range (meanMap μ π L₀ R t)) (meanEntropy μ π L₀ R t) := by
  have h := ((dualPotential_convexOn hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd).neg).add_const
    (dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0))
  refine h.congr ?_
  rintro _ ⟨a, rfl⟩
  rw [meanEntropy_eq_dual hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a]
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- The entropy along a mean segment: `d/ds 𝒮_t(M₀ + sΔ) = t ⟨Δ, a(s)⟩`. -/
theorem hasDerivAt_meanEntropy_line {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun s ↦ meanEntropy μ π L₀ R t (y₀ + s • d))
      (t * dotJ d (meanLine μ π L₀ R t y₀ d s)) s := by
  have hf := hasDerivAt_dualPotential_meanLine hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM
  have h := (hasDerivAt_const s (dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0))).sub hf
  have hev : (fun s ↦ dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) -
      dualPotential μ π L₀ R t (y₀ + s • d)) =ᶠ[𝓝 s]
      fun s ↦ meanEntropy μ π L₀ R t (y₀ + s • d) := by
    have hline : Continuous fun s : ℝ ↦ y₀ + s • d := by fun_prop
    filter_upwards [hline.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hM)] with u hu
    have hu' : y₀ + u • d ∈ Set.range (meanMap μ π L₀ R t) := by
      rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]; exact hu
    obtain ⟨b, hb⟩ := hu'
    simp only [← hb]
    rw [meanEntropy_eq_dual hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b]
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  ring

/-- The entropy along a mean segment bends by minus the inverse-covariance form:
`d/ds (t ⟨Δ, a(s)⟩) = −Δ ⬝ Cov_{a(s)}(R,R)⁻¹ Δ`. -/
theorem hasDerivAt_meanEntropy_line_deriv [DecidableEq ι] {y₀ d : ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun s ↦ t * dotJ d (meanLine μ π L₀ R t y₀ d s))
      (-meanSpeed μ π L₀ R t y₀ d s) s := by
  have h := (hasDerivAt_meanLine_pairing hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hM).neg
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)).congr_deriv rfl
  simp only [Pi.neg_apply]
  ring

/-- **The mean journey from the featureless response spends its entropy through the
inverse-covariance form**: `−𝒮_t(m(a₁)) = ∫₀¹ (1 − s) Δ ⬝ Cov_{θ(M(s))}(R,R)⁻¹ Δ ds` along
`M(s) = m(0) + s (m(a₁) − m(0))`. -/
theorem meanEntropy_eq_neg_integral [DecidableEq ι] (a₁ : ι → ℝ) :
    meanEntropy μ π L₀ R t (meanMap μ π L₀ R t a₁) = -∫ s in (0 : ℝ)..1, (1 - s) *
      meanSpeed μ π L₀ R t (meanMap μ π L₀ R t 0)
        (meanMap μ π L₀ R t a₁ - meanMap μ π L₀ R t 0) s := by
  rw [meanEntropy_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a₁,
    famKL_eq_integral_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0 a₁]

/-- **Entropy decreases along the mean journey from the featureless response**: with
`M(s) = m(0) + s (M₁ − m(0))`, `s ↦ 𝒮_t(M(s))` is antitone on `[0, 1]`. -/
theorem meanEntropy_line_antitoneOn {y₁ : ι → ℝ}
    (h₁ : y₁ ∈ interior (momentBody μ π R)) :
    AntitoneOn (fun s : ℝ ↦ meanEntropy μ π L₀ R t
      (meanMap μ π L₀ R t 0 + s • (y₁ - meanMap μ π L₀ R t 0))) (Icc 0 1) := by
  classical
  obtain ⟨y₀, hy₀⟩ : ∃ y, meanMap μ π L₀ R t 0 = y := ⟨_, rfl⟩
  have h₀ := meanMap_mem_interior hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0
  rw [hy₀] at h₀ ⊢
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, y₀ + s • (y₁ - y₀) ∈ interior (momentBody μ π R) :=
    fun s hs ↦ segment_mem_interior_momentBody h₀ h₁ hs
  have hD : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun s ↦ meanEntropy μ π L₀ R t (y₀ + s • (y₁ - y₀)))
      (t * dotJ (y₁ - y₀) (meanLine μ π L₀ R t y₀ (y₁ - y₀) s)) s :=
    fun s hs ↦ hasDerivAt_meanEntropy_line hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd (hseg s hs)
  have h0 : meanLine μ π L₀ R t y₀ (y₁ - y₀) 0 = 0 := by
    rw [← hy₀]; exact meanLine_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0 _
  -- the derivative is `−∫₀ˢ q ≤ 0`
  have hnonpos : ∀ s ∈ Icc (0 : ℝ) 1,
      t * dotJ (y₁ - y₀) (meanLine μ π L₀ R t y₀ (y₁ - y₀) s) ≤ 0 := by
    intro s hs
    have hcont : ContinuousOn (meanSpeed μ π L₀ R t y₀ (y₁ - y₀)) (uIcc 0 s) := by
      refine (continuousOn_meanSpeed hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd h₀ h₁).mono ?_
      rw [Set.uIcc_of_le hs.1]
      exact Icc_subset_Icc le_rfl hs.2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s ↦ t * dotJ (y₁ - y₀) (meanLine μ π L₀ R t y₀ (y₁ - y₀) s))
      (f' := fun s ↦ -meanSpeed μ π L₀ R t y₀ (y₁ - y₀) s)
      (fun u hu ↦ hasDerivAt_meanEntropy_line_deriv hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
        (hseg u (by rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, hu.2.trans hs.2⟩)))
      hcont.neg.intervalIntegrable
    have hint : ∫ u in (0 : ℝ)..s, -meanSpeed μ π L₀ R t y₀ (y₁ - y₀) u ≤ 0 := by
      rw [intervalIntegral.integral_neg, neg_nonpos]
      exact intervalIntegral.integral_nonneg hs.1 fun u _ ↦
        meanSpeed_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd _ _ u
    rw [hFTC, h0, dotJ_zero_right] at hint
    simpa using hint
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    (f := fun s : ℝ ↦ meanEntropy μ π L₀ R t (y₀ + s • (y₁ - y₀))) ?_ ?_ ?_
  · exact fun s hs ↦ (hD s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (hD s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hD s (Ioo_subset_Icc_self hs)).deriv]
    exact hnonpos s (Ioo_subset_Icc_self hs)

end

end Laplace.Multi
