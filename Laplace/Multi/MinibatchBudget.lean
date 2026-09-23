/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ULAFluctuationBudget

/-!
# Minibatch gradient noise in the LLC error budget (E8 into E2–E4)

SGLD with a constant gradient-noise covariance `C` is the linear chain `x' = Ax + ξ`, `A = 1 − hP`,
`Cov ξ = 2h·1 + h²t²C` (`minibatchNoise`); its stationary covariance is the Lyapunov solution
`Σ^{mb} = lyapunovVia U ρ (minibatchNoise h t C)`, here for any orthogonal frame `U` diagonalising
`P`
(`minibatch_fixed_iff_frame`), with frame entries **`(UᵀΣ^{mb}U)ᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1 −
ρᵢρⱼ)`** and diagonal
**`(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`**, `Ĉ = UᵀCU` (`minibatchCov_frame_apply`, `minibatchCov_frame_diag`).
For `H` in the same frame
the stationary energy is **`(t/2)tr(HΣ^{mb}) = (t/2)∑ᵢλᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`**
(`minibatch_llc_frame`): only the frame
diagonal of the gradient-noise covariance enters the mean of the LLC statistic. Since additive
noise leaves the
anchored mean unchanged, the stationary budget of `ULAFluctuationBudget` extends to
**`t⟨L∘A⟩_loc − [(t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²] = C₁′/t − (th/4)∑λᵢ/κᵢ −
(ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ) + O(t⁻²)`**
(`ulaAnchored_llc_budget_minibatch`): a third sampler bias, `≈ (ht²/4)∑Ĉᵢᵢ/κᵢ`, growing with `t` at
the β-scaled step
unless the batch grows with `t`.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-- Frame entries of the minibatch stationary covariance. -/
theorem minibatchCov_frame_apply (hU : Uᵀ * U = 1) (h t : ℝ) (C : Matrix ι ι ℝ) (i j : ι) :
    (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) i j =
      ((2 * h) * (if i = j then 1 else 0) + h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j) /
        (h * (p i + p j) - h ^ 2 * p i * p j) := by
  rw [lyapunovVia_conj_apply _ _ _ hU]
  simp only [minibatchNoise, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  congr 1
  ring

/-- The frame diagonal of the minibatch law: the ULA variance times `1 + ht²Ĉᵢᵢ/2`. -/
theorem minibatchCov_frame_diag (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (t : ℝ) (C : Matrix ι ι ℝ) (i : ι) :
    (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) i i =
      (1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2)) := by
  rw [minibatchCov_frame_apply hU h t C i i]
  have hpi := hp i
  have hhp := hev i
  have hne : p i * (1 - h * p i / 2) ≠ 0 := mul_ne_zero hpi.ne' (by linarith)
  have hne2 : h * (p i + p i) - h ^ 2 * p i * p i ≠ 0 := by nlinarith [mul_pos hh hpi]
  simp only [if_true]
  rw [div_eq_div_iff hne2 hne]
  ring

/-- The minibatch stationary covariance is the unique fixed point of its covariance step, in any
frame diagonalising `P`. -/
theorem minibatch_fixed_iff_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) (C X : Matrix ι ι ℝ) :
    covStep (ulaStep P h) (minibatchNoise h t C) X = X ↔
      X = lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) :=
  lyapunovVia_fixed_iff U (ulaStep P h) (minibatchNoise h t C) X _ hU (mul_transpose_eq_one_of hU)
    (ulaStep_eq_conj_frame hU hdiag h) fun i => abs_one_sub_mul_lt_one hh (hp i) (hev i)

/-- `tr(HX) = ∑ᵢλᵢ(UᵀXU)ᵢᵢ` for `UᵀHU = diag(λ)`. -/
theorem trace_mul_eq_sum_conj_diag (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam)
    (X : Matrix ι ι ℝ) : (H * X).trace = ∑ i, lam i * (Uᵀ * X * U) i i := by
  rw [frame_eq_conj hU hdiagH, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- **The minibatch stationary energy**: `(t/2)·tr(HΣ^{mb}) = (t/2)∑ᵢλᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`. -/
theorem minibatch_llc_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam) (hp : ∀ i, 0 < p
    i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) (C : Matrix ι ι ℝ) :
    t / 2 * (H * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C)).trace =
      t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) :=
          by
  rw [trace_mul_eq_sum_conj_diag hU hdiagH]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [minibatchCov_frame_diag hU hp hh hev t C i]

end Frame

end Laplace.Sampler

namespace Laplace.Multi

/-! ### The minibatch bias: nonnegative, its β-scaled form, and a batch-size condition -/

section MinibatchBias

variable {d : ℕ} {lam : Fin d → ℝ} {g : ℝ}

theorem posSemidef_conj_frame {Q C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) :
    (Qᵀ * C * Q).PosSemidef := by
  have := hC.conjTranspose_mul_mul_same Q
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Minibatching inflates the statistic**: the minibatch bias is nonnegative for `C ⪰ 0`. -/
theorem minibatch_bias_nonneg (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t h : ℝ} (ht : 0 < t) (hh : 0 <
    h)
    (hev : ∀ i, h * (t * lam i + g) < 2) {Q C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) :
    0 ≤ h * t ^ 3 / 4 *
      ∑ i, lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) := by
  have hĈ := posSemidef_conj_frame (Q := Q) hC
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  have hl := hlam i
  have hκ : 0 < 1 - h * (t * lam i + g) / 2 := by have := hev i; linarith
  have hc := hĈ.diag_nonneg (i := i)
  positivity

/-- At the β-scaled step `h = η/t` the minibatch bias is `(ηt/4)∑ᵢ(tλᵢ/pᵢ)(Ĉᵢᵢ/κᵢ)`. -/
theorem minibatch_bias_scaled (lam : Fin d → ℝ) (g η : ℝ) {t : ℝ} (ht : t ≠ 0) (Cd : Fin d → ℝ) :
    η / t * t ^ 3 / 4 * ∑ i, lam i * Cd i / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)) =
      η * t / 4 * ∑ i, (t * lam i / (t * lam i + g)) * (Cd i / (1 - η / t * (t * lam i + g) / 2))
          := by
  have e : η / t * t ^ 3 / 4 = η * t / 4 * t := by
    field_simp
  rw [e, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [div_mul_div_comm]; ring

/-- **A batch-size condition**: if every `κᵢ ≥ δ > 0` then the minibatch bias is at most
`(ht²/(4δ))·tr C`, so it stays bounded iff the gradient-noise covariance is `O(1/t²)` per unit `h`
(at `h = η/t`: `tr C = O(1/t)`). -/
theorem minibatch_bias_le (hlam : ∀ i, 0 < lam i) (hg : 0 ≤ g) {t h δ : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hδ : 0 < δ) (hκ : ∀ i, δ ≤ 1 - h * (t * lam i + g) / 2) {Q C : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Qᵀ * Q = 1) (hC : C.PosSemidef) :
    h * t ^ 3 / 4 *
        ∑ i, lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) ≤
      h * t ^ 2 / (4 * δ) * C.trace := by
  have hĈ := posSemidef_conj_frame (Q := Q) hC
  have htr : C.trace = ∑ i, (Qᵀ * C * Q) i i := by
    have : (Qᵀ * C * Q).trace = C.trace := by
      rw [Matrix.trace_mul_cycle, Laplace.Sampler.mul_transpose_eq_one_of hQ, Matrix.one_mul]
    rw [← this]
    rfl
  rw [htr, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl := hlam i
  have hκi := hκ i
  have hc := hĈ.diag_nonneg (i := i)
  have hp : 0 < t * lam i + g := by positivity
  have hκpos : 0 < 1 - h * (t * lam i + g) / 2 := lt_of_lt_of_le hδ hκi
  have h2 : lam i * (t * δ) ≤ (t * lam i + g) * (1 - h * (t * lam i + g) / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hκi (mul_pos ht hl).le, mul_nonneg hg hκpos.le]
  have h1 : lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) ≤
      (Qᵀ * C * Q) i i / (t * δ) :=
    calc lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))
        ≤ lam i * (Qᵀ * C * Q) i i / (lam i * (t * δ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = (Qᵀ * C * Q) i i / (t * δ) := mul_div_mul_left _ _ hl.ne'
  calc h * t ^ 3 / 4 * (lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) /
      2)))
      ≤ h * t ^ 3 / 4 * ((Qᵀ * C * Q) i i / (t * δ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = h * t ^ 2 / (4 * δ) * (Qᵀ * C * Q) i i := by
        field_simp

end MinibatchBias

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The stationary budget with minibatch noise**: the minibatch bias `(ht³/4)∑ᵢλᵢĈᵢᵢ/(pᵢκᵢ)`
joins the
step-size bias, `t⟨L∘A⟩_loc − stationary^{mb} = C₁′/t − (th/4)∑λᵢ/κᵢ − (ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ) +
    O(t⁻²)`. -/
theorem ulaAnchored_llc_budget_minibatch (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (C : Matrix (Fin d) (Fin d) ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {h : ℝ}, 0 < h → (∀ i, h * (t * lam i + g) < 2)
        →
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - (t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Qᵀ * C *
        Q) i i / 2) / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))) + t / 2 * ∑ i, lam i * (g *
        affineFrame Q c w₀ i / (t * lam i + g)) ^ 2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i)
        (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 *
        lam i))) / t + t * h / 4 * ∑ i, lam i / (1 - h * (t * lam i + g) / 2) + h * t ^ 3 / 4 * ∑ i,
        lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))| ≤ K / t ^ 2 :=
        by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    ulaAnchored_llc_budget_stationary (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  refine ⟨K₁, T₁, hK₁, hT₁, fun {t} ht {h} hh hev => ?_⟩
  have e₁ := h₁ ht hh hev
  have key : t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Qᵀ * C * Q) i i / 2) / ((t * lam i + g) * (1 -
      h * (t * lam i + g) / 2))) = t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i
      + g) / 2))) + h * t ^ 3 / 4 * ∑ i, lam i * (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t *
      lam i + g) / 2)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) - (t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Qᵀ * C * Q)
      i i / 2) / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))) + t / 2 * ∑ i, lam i * (g *
      affineFrame Q c w₀ i / (t * lam i + g)) ^ 2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma
      i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i)))
      / t + t * h / 4 * ∑ i, lam i / (1 - h * (t * lam i + g) / 2) + h * t ^ 3 / 4 * ∑ i, lam i *
      (Qᵀ * C * Q) i i / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) = t * gibbsExpectation
      (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha
      gamma) - (t / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2))) + t / 2
      * ∑ i, lam i * (g * affineFrame Q c w₀ i / (t * lam i + g)) ^ 2) - (∑ i, (energyLocCoeff1 (lam
      i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i)
      ^ 2 / (2 * lam i))) / t + t * h / 4 * ∑ i, lam i / (1 - h * (t * lam i + g) / 2) := by
    rw [key]
    ring
  rw [e]
  exact e₁

end Multi

end Laplace.Multi
