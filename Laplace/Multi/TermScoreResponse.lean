/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CoefficientResponse

/-!
# The score response of an exponential-form term of the atlas

A term of the atlas has the exponential form (`termDensity` of `LimitingMeasure`)

  `dμ_a = H(x) · exp(−B U_a(u∞(x)) P(x)) dm(x)`,

with `H` the limiting weight (density, chart factors, indicator of the limiting domain), `P` the
monomial profile `∏ u^κ` of the scaled coordinates, `u∞` the face point of `x`, and `U_a` the unit
of the phase along the face — affine in the mixture weight, `U_a = ∑ aᵢ hᵢ`, for a mixture of
populations with a common resolution. Astra's round-20 architecture: **differentiate first,
marginalise second**. The foundational theorem is the score identity

  `D_v ∫ φ dμ_a = −∫ φ S_v dμ_a`,   `S_v = B R_v(u∞) P`   (`ScoreData.hasDerivAt_termCoef`),

for a fixed integrable observable, obtained by dominated differentiation under the sole
hypothesis that `|φ| H (1 + P) e^{-B(c/2)P}` is `m`-integrable (the polynomial factor from the
score absorbed by halving the exponential decay). Its normalised form is the **singular
fluctuation–response identity in exponential form**,

  `D_v ⟨φ⟩_{μ̄_a} = −Cov_{μ̄_a}(φ, S_v)`   (`ScoreData.hasDerivAt_termPosterior`):

the response of the leading law of a chart term to a data direction is minus the covariance of
the observable with the score, exactly as at finite temperature (`−t Cov(φ, R_v)`) with the score
`t R_v` replaced by `B R_v P`. Integrating out the scaled coordinate turns the score into the
face score `β R_v/U_a` of `CoefficientResponse` (`GammaFaceMarginal`).
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {ι : Type*} [Fintype ι]

/-- The unnormalised term integral `∫ φ H e^{-B U_a(u∞) P} dm`. -/
noncomputable def termCoef (m : Measure X) (H P : X → ℝ) (uw : X → Y) (h : ι → Y → ℝ) (B : ℝ)
    (φ : X → ℝ) (a : ι → ℝ) : ℝ :=
  ∫ x, φ x * H x * Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m

/-- The score of the data direction `v`: `S_v = B R_v(u∞) P`. -/
noncomputable def termScore (P : X → ℝ) (uw : X → Y) (h : ι → Y → ℝ) (B : ℝ) (v : ι → ℝ)
    (x : X) : ℝ :=
  B * faceUnit h v (uw x) * P x

/-- The normalised term law `⟨φ⟩_{μ̄_a} = termCoef φ / termCoef 1`. -/
noncomputable def termPosterior (m : Measure X) (H P : X → ℝ) (uw : X → Y) (h : ι → Y → ℝ)
    (B : ℝ) (φ : X → ℝ) (a : ι → ℝ) : ℝ :=
  termCoef m H P uw h B φ a / termCoef m H P uw h B (fun _ ↦ 1) a

/-- The covariance under the normalised term law. -/
noncomputable def termCov (m : Measure X) (H P : X → ℝ) (uw : X → Y) (h : ι → Y → ℝ) (B : ℝ)
    (φ ψ : X → ℝ) (a : ι → ℝ) : ℝ :=
  termPosterior m H P uw h B (fun x ↦ φ x * ψ x) a -
    termPosterior m H P uw h B φ a * termPosterior m H P uw h B ψ a

/-- Standing hypotheses of an exponential-form term: nonnegative measurable `H`, `P`, a
measurable face map, bounded measurable `hᵢ`, positive `B`, and a unit `U_a ≥ c > 0`. -/
structure ScoreData (m : Measure X) (H P : X → ℝ) (uw : X → Y) (h : ι → Y → ℝ) (a : ι → ℝ)
    (B c Mh : ℝ) : Prop where
  H_meas : Measurable H
  H_nonneg : ∀ x, 0 ≤ H x
  P_meas : Measurable P
  P_nonneg : ∀ x, 0 ≤ P x
  uw_meas : Measurable uw
  h_meas : ∀ i, Measurable (h i)
  h_bound : ∀ i y, |h i y| ≤ Mh
  B_pos : 0 < B
  c_pos : 0 < c
  unit_ge : ∀ y, c ≤ faceUnit h a y

namespace ScoreData

variable {m : Measure X} {H P : X → ℝ} {uw : X → Y} {h : ι → Y → ℝ} {a : ι → ℝ} {B c Mh : ℝ}

theorem measurable_unit (hd : ScoreData m H P uw h a B c Mh) (b : ι → ℝ) :
    Measurable fun x ↦ faceUnit h b (uw x) :=
  (Finset.measurable_sum Finset.univ fun i _ ↦ (hd.h_meas i).const_mul (b i)).comp hd.uw_meas

/-- The face data of the term (on the zero measure, used only for the unit bounds). -/
theorem toFaceData (hd : ScoreData m H P uw h a B c Mh) : FaceData (0 : Measure Y) h a c Mh where
  finite := inferInstance
  h_meas := hd.h_meas
  h_bound := hd.h_bound
  c_pos := hd.c_pos
  unit_ge := hd.unit_ge

/-- The domination envelope `|φ| H (1 + P) e^{-B (c/2) P}`. -/
noncomputable def envelope (_hd : ScoreData m H P uw h a B c Mh) (φ : X → ℝ) (x : X) : ℝ :=
  |φ x| * H x * (1 + P x) * Real.exp (-(B * (c / 2) * P x))

/-- **The score identity**: `D_v ∫ φ dμ_a = −∫ φ S_v dμ_a`. -/
theorem hasDerivAt_termCoef [Nonempty ι] [Nonempty Y] (hd : ScoreData m H P uw h a B c Mh)
    {φ : X → ℝ} (hφm : Measurable φ) (hdom : Integrable (hd.envelope φ) m) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ termCoef m H P uw h B φ (a + ε • v))
      (-∫ x, φ x * termScore P uw h B v x * H x *
        Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m) 0 := by
  have hfd := hd.toFaceData
  have hc2 : 0 < c / 2 := by linarith [hd.c_pos]
  have hMh : 0 ≤ Mh := hfd.Mh_nonneg
  have hS : 0 ≤ (∑ i, |v i|) * Mh :=
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hMh
  have hball : Metric.closedBall (0 : ℝ) (hfd.radius v) ∈ 𝓝 0 :=
    Metric.closedBall_mem_nhds 0 (hfd.radius_pos v)
  have hmemball : ∀ ε ∈ Metric.closedBall (0 : ℝ) (hfd.radius v), |ε| ≤ hfd.radius v :=
    fun ε hε ↦ by simpa [Real.dist_eq] using hε
  have hUε : ∀ ε ∈ Metric.closedBall (0 : ℝ) (hfd.radius v), ∀ x,
      c / 2 ≤ faceUnit h (a + ε • v) (uw x) := fun ε hε x ↦
    hfd.unit_perturbed_ge v (hmemball ε hε) (uw x)
  have hexp_le : ∀ ε ∈ Metric.closedBall (0 : ℝ) (hfd.radius v), ∀ x,
      Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) ≤
        Real.exp (-(B * (c / 2) * P x)) := fun ε hε x ↦ by
    rw [Real.exp_le_exp]
    have := hUε ε hε x
    nlinarith [hd.P_nonneg x, hd.B_pos, mul_nonneg hd.B_pos.le (hd.P_nonneg x)]
  have hmeasF : ∀ ε : ℝ, Measurable fun x ↦
      φ x * H x * Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) := fun ε ↦
    (hφm.mul hd.H_meas).mul (Real.measurable_exp.comp
      (((hd.measurable_unit (a + ε • v)).const_mul B).mul hd.P_meas).neg)
  have hmeasF' : ∀ ε : ℝ, Measurable fun x ↦
      φ x * H x * (Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) *
        (-(B * faceUnit h v (uw x) * P x))) := fun ε ↦
    (hφm.mul hd.H_meas).mul ((Real.measurable_exp.comp
      (((hd.measurable_unit (a + ε • v)).const_mul B).mul hd.P_meas).neg).mul
      (((hd.measurable_unit v).const_mul B).mul hd.P_meas).neg)
  have hint : Integrable (fun x ↦ φ x * H x *
      Real.exp (-(B * faceUnit h (a + (0 : ℝ) • v) (uw x) * P x))) m := by
    refine hdom.mono' (hmeasF 0).aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
    have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (hfd.radius v) :=
      Metric.mem_closedBall_self (hfd.radius_pos v).le
    have he := hexp_le 0 h0 x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hd.H_nonneg x),
      abs_of_pos (Real.exp_pos _)]
    unfold envelope
    have hP := hd.P_nonneg x
    have hH := hd.H_nonneg x
    calc |φ x| * H x * Real.exp (-(B * faceUnit h (a + (0 : ℝ) • v) (uw x) * P x))
        ≤ |φ x| * H x * Real.exp (-(B * (c / 2) * P x)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg _) hH)
      _ ≤ |φ x| * H x * (1 + P x) * Real.exp (-(B * (c / 2) * P x)) := by
          have : |φ x| * H x ≤ |φ x| * H x * (1 + P x) :=
            le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hH) (by linarith)
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hbound : ∀ᵐ x ∂m, ∀ ε ∈ Metric.closedBall (0 : ℝ) (hfd.radius v),
      ‖φ x * H x * (Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) *
        (-(B * faceUnit h v (uw x) * P x)))‖ ≤ (B * ((∑ i, |v i|) * Mh)) * hd.envelope φ x := by
    refine Filter.Eventually.of_forall fun x ε hε ↦ ?_
    have he := hexp_le ε hε x
    have hR := hfd.abs_faceUnit_le v (uw x)
    have hP := hd.P_nonneg x
    have hH := hd.H_nonneg x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, abs_mul,
      abs_of_nonneg hH, abs_of_pos (Real.exp_pos _), abs_of_pos hd.B_pos, abs_of_nonneg hP]
    unfold envelope
    calc |φ x| * H x * (Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) *
          (B * |faceUnit h v (uw x)| * P x))
        ≤ |φ x| * H x * (Real.exp (-(B * (c / 2) * P x)) * (B * ((∑ i, |v i|) * Mh) * P x)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul he ?_ ?_ (Real.exp_pos _).le)
            (mul_nonneg (abs_nonneg _) hH)
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hd.B_pos.le) hP
          · exact mul_nonneg (mul_nonneg hd.B_pos.le (abs_nonneg _)) hP
      _ ≤ (B * ((∑ i, |v i|) * Mh)) * (|φ x| * H x * (1 + P x) *
          Real.exp (-(B * (c / 2) * P x))) := by
          have : P x ≤ 1 + P x := by linarith
          have h1 : |φ x| * H x * (Real.exp (-(B * (c / 2) * P x)) *
              (B * ((∑ i, |v i|) * Mh) * P x)) =
              (B * ((∑ i, |v i|) * Mh)) * (|φ x| * H x * P x *
                Real.exp (-(B * (c / 2) * P x))) := by ring
          rw [h1]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hd.B_pos.le hS)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this
            (mul_nonneg (abs_nonneg _) hH)) (Real.exp_pos _).le
  have hdiff : ∀ᵐ x ∂m, ∀ ε ∈ Metric.closedBall (0 : ℝ) (hfd.radius v),
      HasDerivAt (fun ε ↦ φ x * H x * Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)))
        (φ x * H x * (Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) *
          (-(B * faceUnit h v (uw x) * P x)))) ε := by
    refine Filter.Eventually.of_forall fun x ε _ ↦ ?_
    have hlin : HasDerivAt (fun ε ↦ faceUnit h (a + ε • v) (uw x)) (faceUnit h v (uw x)) ε := by
      have h0 : HasDerivAt (fun ε : ℝ ↦ faceUnit h a (uw x) + ε * faceUnit h v (uw x))
          (faceUnit h v (uw x)) ε := by
        have := ((hasDerivAt_id ε).mul_const (faceUnit h v (uw x))).const_add
          (faceUnit h a (uw x))
        simpa only [id, one_mul] using this
      exact h0.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun ε ↦ faceUnit_add_smul h a v ε (uw x))
    have h1 : HasDerivAt (fun ε ↦ -(B * faceUnit h (a + ε • v) (uw x) * P x))
        (-(B * faceUnit h v (uw x) * P x)) ε :=
      ((hlin.const_mul B).mul_const (P x)).neg
    exact h1.exp.const_mul (φ x * H x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε x ↦ φ x * H x * Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)))
    (F' := fun ε x ↦ φ x * H x * (Real.exp (-(B * faceUnit h (a + ε • v) (uw x) * P x)) *
      (-(B * faceUnit h v (uw x) * P x))))
    hball (Filter.Eventually.of_forall fun ε ↦ (hmeasF ε).aestronglyMeasurable) hint
    (hmeasF' 0).aestronglyMeasurable hbound (hdom.const_mul _) hdiff
  refine key.2.congr_deriv ?_
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  simp only [zero_smul, add_zero, termScore]
  ring

/-- **The singular fluctuation–response identity in exponential form**:
`D_v ⟨φ⟩_{μ̄_a} = −Cov_{μ̄_a}(φ, S_v)`. -/
theorem hasDerivAt_termPosterior [Nonempty ι] [Nonempty Y] (hd : ScoreData m H P uw h a B c Mh)
    {φ : X → ℝ} (hφm : Measurable φ) (hdom : Integrable (hd.envelope φ) m)
    (hdom1 : Integrable (hd.envelope fun _ ↦ 1) m)
    (hZ : termCoef m H P uw h B (fun _ ↦ 1) a ≠ 0) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ termPosterior m H P uw h B φ (a + ε • v))
      (-termCov m H P uw h B φ (termScore P uw h B v) a) 0 := by
  have hN := hd.hasDerivAt_termCoef hφm hdom v
  have hZ' := hd.hasDerivAt_termCoef (φ := fun _ ↦ (1 : ℝ)) measurable_const hdom1 v
  have hZ0 : termCoef m H P uw h B (fun _ ↦ (1 : ℝ)) a ≠ 0 := hZ
  have hZ0' : termCoef m H P uw h B (fun _ ↦ (1 : ℝ)) (a + (0 : ℝ) • v) ≠ 0 := by
    simpa using hZ0
  have hdiv := hN.div hZ' hZ0'
  refine hdiv.congr_deriv ?_
  unfold termCov termPosterior termCoef
  simp only [zero_smul, add_zero, one_mul]
  set N := ∫ x, φ x * H x * Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m with hN'
  set NS := ∫ x, φ x * termScore P uw h B v x * H x *
    Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m with hNS
  set ZS := ∫ x, termScore P uw h B v x * H x *
    Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m with hZS
  set Z := ∫ x, H x * Real.exp (-(B * faceUnit h a (uw x) * P x)) ∂m with hZ''
  clear_value N NS ZS Z
  field_simp
  ring

end ScoreData

end Laplace.Multi
