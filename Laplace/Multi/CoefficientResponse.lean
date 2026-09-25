/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The coefficient-response calculus: the leading measure as a function of the mixture weight

Inside the open weight simplex the singular type `(λ, m)` of a mixture `L_a = ∑ aᵢ fᵢ` with a
common minimiser is rigid (`MixtureRigidity`), so the variation of the asymptotic response map
there is carried entirely by the **leading coefficient measure** `μ_a`. After principalising the
losses in a common chart, `L_a = x^N U_a(x)` with the affine unit `U_a = ∑ aᵢ hᵢ`, and the face
formula of the leading term reads

  `μ_a(φ) = ∫_F φ(y) U_a(y)^{-λ} dν(y)`   (`faceCoef`),

with `ν` the face measure (all chart factors absorbed) and `λ` the leading exponent. This module
records the differential calculus of this map in the weight `a`, on the open simplex where
`U_a ≥ c > 0`:

* the differential in a data direction `v` is `−λ ∫ φ U_a^{-λ-1} R_v dν` with `R_v = ∑ vᵢ hᵢ`
  (`FaceData.hasDerivAt_faceCoef`, dominated differentiation);
* the normalised limiting posterior `φ ↦ μ_a(φ)/μ_a(1)` has differential
  `−λ Cov_{ν_a}(φ, R_v / U_a)` where `ν_a ∝ U_a^{-λ} ν` is the limiting posterior on the face
  (`FaceData.hasDerivAt_facePosterior`):

the **singular fluctuation–response identity**. It is the `t → ∞` shadow of the exact identity
`d/ds ⟨φ⟩ = −t Cov(φ, R_v)`: the inverse temperature is replaced by the exponent `λ` and the
direction loss `R_v` by its ratio `R_v / U_a` to the unit.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) {ι : Type*} [Fintype ι]

/-- The affine unit `U_a = ∑ᵢ aᵢ hᵢ` of the principalised mixture. -/
noncomputable def faceUnit (h : ι → Y → ℝ) (a : ι → ℝ) (y : Y) : ℝ := ∑ i, a i * h i y

/-- The face coefficient `μ_a(φ) = ∫ φ U_a^{-λ} dν`. -/
noncomputable def faceCoef (φ : Y → ℝ) (h : ι → Y → ℝ) (lam : ℝ) (a : ι → ℝ) : ℝ :=
  ∫ y, φ y * faceUnit h a y ^ (-lam) ∂ν

/-- The normalised limiting posterior on the face, `μ_a(φ) / μ_a(1)`. -/
noncomputable def facePosterior (φ : Y → ℝ) (h : ι → Y → ℝ) (lam : ℝ) (a : ι → ℝ) : ℝ :=
  faceCoef ν φ h lam a / faceCoef ν (fun _ ↦ 1) h lam a

/-- The limiting-posterior covariance on the face. -/
noncomputable def faceCov (φ ψ : Y → ℝ) (h : ι → Y → ℝ) (lam : ℝ) (a : ι → ℝ) : ℝ :=
  facePosterior ν (fun y ↦ φ y * ψ y) h lam a -
    facePosterior ν φ h lam a * facePosterior ν ψ h lam a

variable {ν}

omit [MeasurableSpace Y] in
theorem faceUnit_add_smul (h : ι → Y → ℝ) (a v : ι → ℝ) (ε : ℝ) (y : Y) :
    faceUnit h (a + ε • v) y = faceUnit h a y + ε * faceUnit h v y := by
  simp only [faceUnit, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- `u ^ z ≤ c ^ z` for `0 < c ≤ u` and `z ≤ 0`. -/
theorem rpow_le_rpow_of_le_of_nonpos {c u z : ℝ} (hc : 0 < c) (hcu : c ≤ u) (hz : z ≤ 0) :
    u ^ z ≤ c ^ z := by
  rw [← neg_neg z, Real.rpow_neg hc.le, Real.rpow_neg (hc.trans_le hcu).le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hc _) (Real.rpow_le_rpow hc.le hcu (neg_nonneg.mpr hz))

/-- Standing hypotheses on the face: a finite face measure, bounded measurable `hᵢ`, and a
uniformly positive unit `U_a ≥ c`. -/
structure FaceData (ν : Measure Y) (h : ι → Y → ℝ) (a : ι → ℝ) (c Mh : ℝ) : Prop where
  finite : IsFiniteMeasure ν
  h_meas : ∀ i, Measurable (h i)
  h_bound : ∀ i y, |h i y| ≤ Mh
  c_pos : 0 < c
  unit_ge : ∀ y, c ≤ faceUnit h a y

namespace FaceData

variable {h : ι → Y → ℝ} {a : ι → ℝ} {c Mh : ℝ}

theorem measurable_faceUnit (hd : FaceData ν h a c Mh) (b : ι → ℝ) :
    Measurable (faceUnit h b) :=
  Finset.measurable_sum Finset.univ fun i _ ↦ (hd.h_meas i).const_mul (b i)

theorem abs_faceUnit_le (hd : FaceData ν h a c Mh) (b : ι → ℝ) (y : Y) :
    |faceUnit h b y| ≤ (∑ i, |b i|) * Mh := by
  unfold faceUnit
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hd.h_bound i y) (abs_nonneg _)

/-- The radius of the ball of weights on which the perturbed unit stays `≥ c/2`. -/
noncomputable def radius (_hd : FaceData ν h a c Mh) (v : ι → ℝ) : ℝ :=
  c / (2 * ((∑ i, |v i|) * Mh + 1))

theorem Mh_nonneg [Nonempty ι] [Nonempty Y] (hd : FaceData ν h a c Mh) : 0 ≤ Mh :=
  le_trans (abs_nonneg _) (hd.h_bound (Classical.arbitrary ι) (Classical.arbitrary Y))

theorem radius_pos [Nonempty ι] [Nonempty Y] (hd : FaceData ν h a c Mh) (v : ι → ℝ) :
    0 < hd.radius v := by
  have hS : 0 ≤ (∑ i, |v i|) * Mh :=
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hd.Mh_nonneg
  exact div_pos hd.c_pos (by linarith)

/-- On `|ε| ≤ radius` the perturbed unit stays `≥ c/2`. -/
theorem unit_perturbed_ge [Nonempty ι] [Nonempty Y] (hd : FaceData ν h a c Mh) (v : ι → ℝ)
    {ε : ℝ} (hε : |ε| ≤ hd.radius v) (y : Y) : c / 2 ≤ faceUnit h (a + ε • v) y := by
  have hS : 0 ≤ (∑ i, |v i|) * Mh :=
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hd.Mh_nonneg
  rw [faceUnit_add_smul]
  have h1 : |ε * faceUnit h v y| ≤ c / 2 := by
    rw [abs_mul]
    calc |ε| * |faceUnit h v y| ≤ hd.radius v * ((∑ i, |v i|) * Mh) :=
          mul_le_mul hε (hd.abs_faceUnit_le v y) (abs_nonneg _) (hd.radius_pos v).le
      _ ≤ c / 2 := by
          unfold radius
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
          nlinarith [hd.c_pos]
  have := hd.unit_ge y
  linarith [neg_abs_le (ε * faceUnit h v y)]

theorem unit_pos (hd : FaceData ν h a c Mh) (y : Y) : 0 < faceUnit h a y :=
  hd.c_pos.trans_le (hd.unit_ge y)

/-- **The differential of the face coefficient in a data direction**:
`d/dε μ_{a + εv}(φ) |_{ε=0} = −λ ∫ φ U_a^{-λ-1} R_v dν`. -/
theorem hasDerivAt_faceCoef [Nonempty ι] [Nonempty Y] (hd : FaceData ν h a c Mh) {φ : Y → ℝ}
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ y, |φ y| ≤ Mφ) {lam : ℝ} (hlam : 0 ≤ lam)
    (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ faceCoef ν φ h lam (a + ε • v))
      (-lam * ∫ y, φ y * faceUnit h a y ^ (-lam - 1) * faceUnit h v y ∂ν) 0 := by
  have := hd.finite
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ (Classical.arbitrary Y))
  have hc2 : 0 < c / 2 := by linarith [hd.c_pos]
  have hball : Metric.closedBall (0 : ℝ) (hd.radius v) ∈ 𝓝 0 :=
    Metric.closedBall_mem_nhds 0 (hd.radius_pos v)
  have hmemball : ∀ ε ∈ Metric.closedBall (0 : ℝ) (hd.radius v), |ε| ≤ hd.radius v := fun ε hε ↦ by
    simpa [Real.dist_eq] using hε
  have hmeasF : ∀ ε : ℝ, Measurable fun y ↦ φ y * faceUnit h (a + ε • v) y ^ (-lam) := fun ε ↦
    hφm.mul ((hd.measurable_faceUnit (a + ε • v)).pow_const (-lam))
  have hmeasF' : ∀ ε : ℝ, Measurable fun y ↦
      φ y * (faceUnit h v y * -lam * faceUnit h (a + ε • v) y ^ (-lam - 1)) := fun ε ↦
    hφm.mul (((hd.measurable_faceUnit v).mul_const (-lam)).mul
      ((hd.measurable_faceUnit (a + ε • v)).pow_const (-lam - 1)))
  have hint : Integrable (fun y ↦ φ y * faceUnit h (a + (0 : ℝ) • v) y ^ (-lam)) ν := by
    refine (integrable_const (Mφ * c ^ (-lam))).mono' (hmeasF 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [zero_smul, add_zero]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hd.unit_pos y) _)]
    exact mul_le_mul (hφ y) (rpow_le_rpow_of_le_of_nonpos hd.c_pos (hd.unit_ge y)
      (neg_nonpos.mpr hlam)) (Real.rpow_pos_of_pos (hd.unit_pos y) _).le hMφ
  have hbound : ∀ᵐ y ∂ν, ∀ ε ∈ Metric.closedBall (0 : ℝ) (hd.radius v),
      ‖φ y * (faceUnit h v y * -lam * faceUnit h (a + ε • v) y ^ (-lam - 1))‖ ≤
        Mφ * (((∑ i, |v i|) * Mh) * lam * (c / 2) ^ (-lam - 1)) := by
    refine Filter.Eventually.of_forall fun y ε hε ↦ ?_
    have hU := hd.unit_perturbed_ge v (hmemball ε hε) y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam,
      abs_of_pos (Real.rpow_pos_of_pos (hc2.trans_le hU) _)]
    have h1 := hd.abs_faceUnit_le v y
    have h2 := rpow_le_rpow_of_le_of_nonpos hc2 hU (by linarith : -lam - 1 ≤ 0)
    have hS : 0 ≤ (∑ i, |v i|) * Mh :=
      mul_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hd.Mh_nonneg
    have hUp : 0 < faceUnit h (a + ε • v) y ^ (-lam - 1) :=
      Real.rpow_pos_of_pos (hc2.trans_le hU) _
    exact mul_le_mul (hφ y) (mul_le_mul (mul_le_mul_of_nonneg_right h1 hlam) h2 hUp.le
      (mul_nonneg hS hlam)) (mul_nonneg (mul_nonneg (abs_nonneg _) hlam) hUp.le) hMφ
  have hdiff : ∀ᵐ y ∂ν, ∀ ε ∈ Metric.closedBall (0 : ℝ) (hd.radius v),
      HasDerivAt (fun ε ↦ φ y * faceUnit h (a + ε • v) y ^ (-lam))
        (φ y * (faceUnit h v y * -lam * faceUnit h (a + ε • v) y ^ (-lam - 1))) ε := by
    refine Filter.Eventually.of_forall fun y ε hε ↦ ?_
    have hU := hd.unit_perturbed_ge v (hmemball ε hε) y
    have hlin : HasDerivAt (fun ε ↦ faceUnit h (a + ε • v) y) (faceUnit h v y) ε := by
      have h0 : HasDerivAt (fun ε : ℝ ↦ faceUnit h a y + ε * faceUnit h v y)
          (faceUnit h v y) ε := by
        have := ((hasDerivAt_id ε).mul_const (faceUnit h v y)).const_add (faceUnit h a y)
        simpa only [id, one_mul] using this
      exact h0.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun ε ↦ faceUnit_add_smul h a v ε y)
    exact (hlin.rpow_const (Or.inl (hc2.trans_le hU).ne')).const_mul (φ y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε y ↦ φ y * faceUnit h (a + ε • v) y ^ (-lam))
    (F' := fun ε y ↦ φ y * (faceUnit h v y * -lam * faceUnit h (a + ε • v) y ^ (-lam - 1)))
    hball (Filter.Eventually.of_forall fun ε ↦ (hmeasF ε).aestronglyMeasurable) hint
    (hmeasF' 0).aestronglyMeasurable hbound (integrable_const _) hdiff
  have hderiv := key.2
  have hrw : (∫ y, φ y * (faceUnit h v y * -lam * faceUnit h (a + (0 : ℝ) • v) y ^ (-lam - 1)) ∂ν)
      = -lam * ∫ y, φ y * faceUnit h a y ^ (-lam - 1) * faceUnit h v y ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    simp only [zero_smul, add_zero]
    ring
  rw [hrw] at hderiv
  exact hderiv

/-- **The singular fluctuation–response identity**: the differential of the normalised limiting
posterior `φ ↦ μ_a(φ)/μ_a(1)` in a data direction `v` is `−λ Cov_{ν_a}(φ, R_v / U_a)`, the
covariance under the limiting posterior of the observable with the direction loss divided by the
unit. -/
theorem hasDerivAt_facePosterior [Nonempty ι] [Nonempty Y] (hd : FaceData ν h a c Mh)
    {φ : Y → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ y, |φ y| ≤ Mφ) {lam : ℝ} (hlam : 0 ≤ lam)
    (v : ι → ℝ) (hZ : faceCoef ν (fun _ ↦ 1) h lam a ≠ 0) :
    HasDerivAt (fun ε : ℝ ↦ facePosterior ν φ h lam (a + ε • v))
      (-lam * faceCov ν φ (fun y ↦ faceUnit h v y / faceUnit h a y) h lam a) 0 := by
  have hN := hd.hasDerivAt_faceCoef hφm hφ hlam v
  have hZ' := hd.hasDerivAt_faceCoef (φ := fun _ ↦ (1 : ℝ)) measurable_const (Mφ := 1)
    (fun _ ↦ by simp) hlam v
  have hZ0 : faceCoef ν (fun _ ↦ (1 : ℝ)) h lam (a + (0 : ℝ) • v) ≠ 0 := by simpa using hZ
  have hdiv := hN.div hZ' hZ0
  refine hdiv.congr_deriv ?_
  unfold faceCov facePosterior faceCoef
  simp only [zero_smul, add_zero, one_mul]
  have e1 : ∀ y, φ y * faceUnit h a y ^ (-lam - 1) * faceUnit h v y =
      (φ y * (faceUnit h v y / faceUnit h a y)) * faceUnit h a y ^ (-lam) := fun y ↦ by
    rw [Real.rpow_sub_one (hd.unit_pos y).ne']
    field_simp
  have e2 : ∀ y, faceUnit h a y ^ (-lam - 1) * faceUnit h v y =
      (faceUnit h v y / faceUnit h a y) * faceUnit h a y ^ (-lam) := fun y ↦ by
    rw [Real.rpow_sub_one (hd.unit_pos y).ne']
    field_simp
  simp only [e1, e2]
  set N := ∫ y, φ y * faceUnit h a y ^ (-lam) ∂ν with hN'
  set NL := ∫ y, φ y * (faceUnit h v y / faceUnit h a y) * faceUnit h a y ^ (-lam) ∂ν with hNL
  set ZL := ∫ y, faceUnit h v y / faceUnit h a y * faceUnit h a y ^ (-lam) ∂ν with hZL
  set Z := ∫ y, faceUnit h a y ^ (-lam) ∂ν with hZ''
  clear_value N NL ZL Z
  field_simp
  ring

end FaceData

end Laplace.Multi
