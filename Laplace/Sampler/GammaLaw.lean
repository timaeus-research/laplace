/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.ULALocalised

/-!
# The Gamma law of the LLC statistic under the sampler's Gaussian laws (E3)

For a centred Gaussian law with precision `Q` (the seabed's `tiltedExpectation Q 0`) and a
symmetric `H`, the Laplace transform of the quadratic form is *exactly* a ratio of Gaussian
partition functions,
`⟨exp(−c·½uᵀHu)⟩_Q = √(det Q)/√(det(Q + cH))` whenever `Q + cH ≻ 0`
(`tiltedExpectation_exp_quadForm`;
no commutation, no sign of `c`). In the eigenbasis of `H` the determinants are products, so for the
LLC statistic `X = t·½uᵀHu` of the note's E3:

* under the exact localised Gibbs law `Q = tH + γI` (`laplace_localisedGibbs`):
  `⟨e^{−sX}⟩ = ∏ᵢ ((tλᵢ + γ)/((1+s)tλᵢ + γ))^{1/2}`, a sum of independent
  `Gamma(½, rate (tλᵢ+γ)/(tλᵢ))` whose mean is E3/E6's localised LLC `½∑tλᵢ/(tλᵢ + γ)`; at
  `γ = 0` (`laplace_gibbs`) exactly
  `(1+s)^{−d/2}` for every `t`: the Gaussian LLC statistic is `Gamma(d/2, 1)` — the law that
  `LocalisedLaplaceTransform` reaches only asymptotically for the anharmonic target;
* under the ULA stationary law `Q = P_γ − (h/2)P_γ²`, `P_γ = tH + γI`, `aᵢ = tλᵢ + γ`, `haᵢ < 2`
  (`laplace_ulaLocalised`, `s ≥ 0`): `⟨e^{−sX}⟩ = ∏ᵢ (aᵢ(1 − haᵢ/2)/(aᵢ(1 − haᵢ/2) + s tλᵢ))^{1/2}`,
  independent `Gamma(½, rate aᵢ(1 − haᵢ/2)/(tλᵢ))`; unlocalised (`laplace_ula`):
  `∏ᵢ ((1 − hpᵢ/2)/(1 − hpᵢ/2 + s))^{1/2}`, `pᵢ = tλᵢ` — the "ULA inflation" of `ula_llc`
  (mean `½∑1/(1 − hpᵢ/2)`) is a per-direction Gamma *rate* shift `1 ↦ 1 − hpᵢ/2`, not a shape
  change.

Localisation raises the rates (suppressing the mean), discretisation lowers them (inflating it);
both act direction by direction with parameters `γ/(tλᵢ)` and `hpᵢ = htλᵢ`. The
Gamma identifications and the cumulants `κₙ = (n−1)!/2·∑ᵢrᵢ⁻ⁿ` are prose consequences of the
transform
formulas; the identification of `tiltedExpectation Q 0` with Mathlib's `multivariateGaussian 0 Q⁻¹`
(the sampler files' representation of the ULA invariant law) is standard but not machine-checked
here. `d = 0` gives the transform `1` (the point mass at `0`).
-/

open Matrix Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The quadratic form is affine in the matrix. -/
theorem dotProduct_add_smul_mulVec (Q H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    u ⬝ᵥ (Q + c • H) *ᵥ u = u ⬝ᵥ Q *ᵥ u + c * (u ⬝ᵥ H *ᵥ u) := by
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- **The Laplace transform of a quadratic form under a centred Gaussian is a partition-function
ratio**: `⟨exp(−c·½uᵀHu)⟩_Q = √(det Q)/√(det(Q + cH))` whenever `Q ≻ 0` and `Q + cH ≻ 0`. -/
theorem tiltedExpectation_exp_quadForm {Q H : Matrix ι ι ℝ} (hQ : Q.PosDef) {c : ℝ}
    (hQc : (Q + c • H).PosDef) :
    tiltedExpectation Q 0 (fun u => Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.sqrt Q.det / Real.sqrt (Q + c • H).det := by
  have e : ∀ u : ι → ℝ, Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u)))) * tiltedWeight Q 0 u =
      tiltedWeight (Q + c • H) 0 u := by
    intro u
    unfold tiltedWeight
    rw [← Real.exp_add, dotProduct_add_smul_mulVec]
    congr 1
    ring
  have hnum : (∫ u : ι → ℝ, Real.exp (-(c * ((1 / 2) * (u ⬝ᵥ H *ᵥ u)))) * tiltedWeight Q 0 u) =
      tiltedZ (Q + c • H) 0 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall e)
  unfold tiltedExpectation
  rw [hnum, tiltedZ_eq hQc 0, tiltedZ_eq hQ 0, gaussianZ_matCLM hQc, gaussianZ_matCLM hQ]
  simp only [tiltMean, Matrix.mulVec_zero, zero_dotProduct, mul_zero, Real.exp_zero, one_mul]
  have h1 : Real.sqrt Q.det ≠ 0 := (Real.sqrt_pos.mpr hQ.det_pos).ne'
  have h2 : Real.sqrt (Q + c • H).det ≠ 0 := (Real.sqrt_pos.mpr hQc.det_pos).ne'
  have h3 : Real.sqrt (2 * Real.pi) ^ Fintype.card ι ≠ 0 := by positivity
  field_simp

/-! ### Determinants and positive definiteness in the eigenbasis of `H` -/

/-- `det(UᵀBU) = det B` for the orthogonal eigenbasis `U = orthoOf hA`. -/
theorem det_conj_orthoOf {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (B : Matrix ι ι ℝ) :
    ((orthoOf hA)ᵀ * B * orthoOf hA).det = B.det := by
  have h1 : (orthoOf hA).det * (orthoOf hA).det = 1 := by
    have := congrArg Matrix.det (orthoOf_transpose_mul hA)
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  linear_combination B.det * h1

/-- `det(tH + γI) = ∏ᵢ (tλᵢ + γ)`. -/
theorem det_localisedPrecision {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (t γ : ℝ) :
    (t • H + γ • (1 : Matrix ι ι ℝ)).det = ∏ i, (t * hH.eigenvalues i + γ) := by
  rw [← det_conj_orthoOf hH, orthoOf_transpose_localised_mul hH t γ, Matrix.det_diagonal]

/-- A matrix conjugated by the eigenbasis to a positive diagonal is positive definite. -/
theorem posDef_of_orthoOf_conj {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {Q : Matrix ι ι ℝ}
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hQ : (orthoOf hA)ᵀ * Q * orthoOf hA = diagonal v) :
    Q.PosDef := by
  have hU' := orthoOf_mul_transpose hA
  have hQ' : Q = orthoOf hA * diagonal v * (orthoOf hA)ᵀ := by
    rw [← hQ]
    calc Q = (orthoOf hA * (orthoOf hA)ᵀ) * Q * (orthoOf hA * (orthoOf hA)ᵀ) := by
          rw [hU', Matrix.one_mul, Matrix.mul_one]
      _ = orthoOf hA * ((orthoOf hA)ᵀ * Q * orthoOf hA) * (orthoOf hA)ᵀ := by
          simp only [Matrix.mul_assoc]
  have hd : (diagonal v).PosDef := Matrix.PosDef.diagonal hv
  have hinj : Function.Injective (orthoOf hA)ᵀ.mulVec := by
    intro x y hxy
    have := congrArg (orthoOf hA).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hU'] using this
  have := Matrix.PosDef.conjTranspose_mul_mul_same hd hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this
  rw [hQ']
  exact this

/-! ### The exact Gibbs law -/

/-- **The Gamma law under the localised Gibbs target** (E3/E6): for `Q = tH + γI` and `s > −1`,
`⟨exp(−s·t·½uᵀHu)⟩_Q = √(∏ᵢ (tλᵢ + γ)/((1+s)tλᵢ + γ))` — a sum of independent
`Gamma(½, rate (tλᵢ + γ)/(tλᵢ))` variables. -/
theorem laplace_localisedGibbs {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ s : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hs : -1 < s) :
    tiltedExpectation (t • H + γ • (1 : Matrix ι ι ℝ)) 0
        (fun u => Real.exp (-(s * t * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.sqrt (∏ i, (t * hH.1.eigenvalues i + γ) /
        ((1 + s) * t * hH.1.eigenvalues i + γ)) := by
  have hQ := effectivePrecision_posDef hH ht hγ
  have ha : 0 < 1 + s := by linarith
  have e : t • H + γ • (1 : Matrix ι ι ℝ) + (s * t) • H =
      ((1 + s) * t) • H + γ • (1 : Matrix ι ι ℝ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hQs : (t • H + γ • (1 : Matrix ι ι ℝ) + (s * t) • H).PosDef := by
    rw [e]
    exact effectivePrecision_posDef hH (mul_pos ha ht) hγ
  have hB : ∀ i, 0 ≤ (1 + s) * t * hH.1.eigenvalues i + γ := fun i => by
    have := hH.eigenvalues_pos i
    positivity
  rw [tiltedExpectation_exp_quadForm hQ hQs, e, det_localisedPrecision hH.1,
    det_localisedPrecision hH.1, Finset.prod_div_distrib,
    Real.sqrt_div' _ (Finset.prod_nonneg fun i _ => hB i)]

omit [DecidableEq ι] in
/-- **The Gaussian LLC statistic is exactly `Gamma(d/2, 1)`**: under the Gibbs law `Q = tH`,
`⟨exp(−s·t·½uᵀHu)⟩ = (1+s)^{−d/2}` for every `t > 0` and `s > −1`. -/
theorem laplace_gibbs {H : Matrix ι ι ℝ} (hH : H.PosDef) {t s : ℝ} (ht : 0 < t) (hs : -1 < s) :
    tiltedExpectation (t • H) 0 (fun u => Real.exp (-(s * t * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      (1 / Real.sqrt (1 + s)) ^ Fintype.card ι := by
  classical
  have h := laplace_localisedGibbs hH ht le_rfl hs (γ := 0)
  simp only [zero_smul, add_zero] at h
  rw [h]
  have ha : 0 < 1 + s := by linarith
  have e : ∀ i, t * hH.1.eigenvalues i / ((1 + s) * t * hH.1.eigenvalues i) = 1 / (1 + s) :=
    fun i => by
      have := hH.eigenvalues_pos i
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
  rw [Finset.prod_congr rfl fun i _ => e i, Real.sqrt_prod _ (fun i _ => by positivity),
    Finset.prod_const, Finset.card_univ, one_div, Real.sqrt_inv, one_div]

/-! ### The ULA stationary law -/

/-- **The Gamma law under the (localised) ULA stationary law** (E3): for `P_γ = tH + γI`,
`Q = P_γ − (h/2)P_γ²`, `aᵢ = tλᵢ + γ`, `haᵢ < 2` and `s ≥ 0`,
`⟨exp(−s·t·½uᵀHu)⟩_Q = √(∏ᵢ aᵢ(1 − haᵢ/2)/(aᵢ(1 − haᵢ/2) + s·tλᵢ))` — a sum of independent
`Gamma(½, rate aᵢ(1 − haᵢ/2)/(tλᵢ))` variables, whose mean is the ULA-corrected localised LLC. -/
theorem laplace_ulaLocalised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ h s : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) (hev : ∀ i, h * (t * hH.1.eigenvalues i + γ) < 2) (hs : 0 ≤ s) :
    tiltedExpectation ((t • H + γ • (1 : Matrix ι ι ℝ)) -
        (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))) 0
        (fun u => Real.exp (-(s * t * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.sqrt (∏ i, (t * hH.1.eigenvalues i + γ) * (1 - h * (t * hH.1.eigenvalues i + γ) / 2) /
        ((t * hH.1.eigenvalues i + γ) * (1 - h * (t * hH.1.eigenvalues i + γ) / 2) +
          s * t * hH.1.eigenvalues i)) := by
  have hdiagQ := orthoOf_transpose_ulaDenom_mul hH.1 t γ h
  have hpos : ∀ i, 0 < (t * hH.1.eigenvalues i + γ) - h / 2 * (t * hH.1.eigenvalues i + γ) ^ 2 :=
    fun i => by
      have hl := hH.eigenvalues_pos i
      have ha : 0 < t * hH.1.eigenvalues i + γ := by positivity
      have := hev i
      nlinarith
  have hQ : ((t • H + γ • (1 : Matrix ι ι ℝ)) -
      (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))).PosDef :=
    posDef_of_orthoOf_conj hH.1 hpos hdiagQ
  have hQs : ((t • H + γ • (1 : Matrix ι ι ℝ)) -
      (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ))) +
      (s * t) • H).PosDef :=
    hQ.add_posSemidef (hH.posSemidef.smul (by positivity))
  have hdiagH := orthoOf_transpose_localised_mul hH.1 (s * t) 0
  simp only [zero_smul, add_zero] at hdiagH
  have hdetQ : ((t • H + γ • (1 : Matrix ι ι ℝ)) -
      (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ)))).det =
      ∏ i, ((t * hH.1.eigenvalues i + γ) - h / 2 * (t * hH.1.eigenvalues i + γ) ^ 2) := by
    rw [← det_conj_orthoOf hH.1, hdiagQ, Matrix.det_diagonal]
  have hdetQs : ((t • H + γ • (1 : Matrix ι ι ℝ)) -
      (h / 2) • ((t • H + γ • (1 : Matrix ι ι ℝ)) * (t • H + γ • (1 : Matrix ι ι ℝ))) +
      (s * t) • H).det =
      ∏ i, ((t * hH.1.eigenvalues i + γ) - h / 2 * (t * hH.1.eigenvalues i + γ) ^ 2 +
        s * t * hH.1.eigenvalues i) := by
    rw [← det_conj_orthoOf hH.1, Matrix.mul_add, Matrix.add_mul, hdiagQ, hdiagH,
      Matrix.diagonal_add, Matrix.det_diagonal]
  have hB : ∀ i, 0 ≤ (t * hH.1.eigenvalues i + γ) * (1 - h * (t * hH.1.eigenvalues i + γ) / 2) +
      s * t * hH.1.eigenvalues i := fun i => by
    have hl := hH.eigenvalues_pos i
    have h1 := hpos i
    linarith [mul_nonneg (mul_nonneg hs ht.le) hl.le]
  rw [tiltedExpectation_exp_quadForm hQ hQs, hdetQ, hdetQs, Finset.prod_div_distrib,
    Real.sqrt_div' _ (Finset.prod_nonneg fun i _ => hB i)]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun i _ => by ring
  · congr 1
    exact Finset.prod_congr rfl fun i _ => by ring

/-- **The ULA inflation is a Gamma rate shift**: under the ULA stationary law for the Gibbs target
`P = tH` (`pᵢ = tλᵢ`, `hpᵢ < 2`), `⟨exp(−s·t·½uᵀHu)⟩ = √(∏ᵢ (1 − hpᵢ/2)/(1 − hpᵢ/2 + s))` for
`s ≥ 0`: the sampled LLC statistic is a sum of independent `Gamma(½, rate 1 − hpᵢ/2)` variables
(mean `ula_llc = ½∑ᵢ 1/(1 − hpᵢ/2)`), against `Gamma(d/2, 1)` under the Gibbs law. -/
theorem laplace_ula {H : Matrix ι ι ℝ} (hH : H.PosDef) {t h s : ℝ} (ht : 0 < t)
    (hev : ∀ i, h * (t * hH.1.eigenvalues i) < 2) (hs : 0 ≤ s) :
    tiltedExpectation (t • H - (h / 2) • ((t • H) * (t • H))) 0
        (fun u => Real.exp (-(s * t * ((1 / 2) * (u ⬝ᵥ H *ᵥ u))))) =
      Real.sqrt (∏ i, (1 - h * (t * hH.1.eigenvalues i) / 2) /
        (1 - h * (t * hH.1.eigenvalues i) / 2 + s)) := by
  have h0 := laplace_ulaLocalised hH ht le_rfl (γ := 0) (fun i => by simpa using hev i) hs
  simp only [zero_smul, add_zero] at h0
  rw [h0]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    have hl := hH.eigenvalues_pos i
    have hp : 0 < t * hH.1.eigenvalues i := by positivity
    have h1 : 0 < 1 - h * (t * hH.1.eigenvalues i) / 2 := by linarith [hev i]
    have h2 : 0 < 1 - h * (t * hH.1.eigenvalues i) / 2 + s := by linarith
    have h3 : 0 < t * hH.1.eigenvalues i * (1 - h * (t * hH.1.eigenvalues i) / 2) +
        s * t * hH.1.eigenvalues i := by positivity
    rw [div_eq_div_iff h3.ne' h2.ne']
    ring

end Laplace.Sampler
