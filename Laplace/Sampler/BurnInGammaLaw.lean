/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.GammaLaw
import Laplace.Sampler.FrobeniusTarget

/-!
# The burn-in Gamma law of the ULA-sampled LLC statistic (E3/E4)

ULA from the mode on the Gaussian target with precision `P` (`P = tH`, eigenvalues `pᵢ = tλᵢ`,
`ρᵢ = 1 − hpᵢ`, stability `hpᵢ < 2`) has after `k` updates the centred Gaussian law with covariance
`Σ_k = ulaCov P h · (1 − (ulaStep P h)^{2k}) = S(1 − A^{2k})` (`covStep_iterate_zero_of_comm`,
`gaussStep_iterate_zero`). In the eigenbasis `U = orthoOf hP.1`:

* `burnInCov_eq_conj`: `Σ_k = U diag(fᵢ(k)/(pᵢaᵢ)) Uᵀ` with `aᵢ = 1 − hpᵢ/2`, `fᵢ(k) = 1 − ρᵢ^{2k}`;
  `burnInCov_inv_eq_conj`: for `k ≥ 1`, `Σ_k⁻¹ = U diag(pᵢaᵢ/fᵢ(k)) Uᵀ ≻ 0`
  (`burnInCov_inv_posDef`);
* `laplace_ulaBurnIn`: for `s ≥ 0`, `k ≥ 1`, the Laplace transform of the LLC statistic `X = ½uᵀPu`
  under the burn-in law is `√(∏ᵢ aᵢ/(aᵢ + s fᵢ(k)))` — a sum of independent
  `Gamma(½, rate aᵢ/fᵢ(k))` variables whose rates decrease to the stationary ULA rates `aᵢ`
  (`GammaLaw.laplace_ula`);
* `burnIn_mean`: the mean `⟨½uᵀPu⟩ = ½∑ᵢ fᵢ(k)/aᵢ` (the eigen form of `llc_ula_trajectory`'s trace),
  `burnIn_bias`: it lies below the stationary ULA mean `½∑ᵢ1/aᵢ` by exactly `½∑ᵢ ρᵢ^{2k}/aᵢ`
  (E4's zero-start factor `ρ^{2(b+1)}` is `k = b + 1` updates);
* `burnInTransform_antitone`, `burnInTransform_tendsto`: the transform
  `L_k(s) = √(∏ aᵢ/(aᵢ + s fᵢ(k)))` is nonincreasing in `k` and tends to the stationary transform
  `√(∏ aᵢ/(aᵢ + s))`.

`k = 0` (the point mass at the mode, transform `1`) is excluded from the precision statements. Exact
for the quadratic model and the exact ULA recursion; the marginal law at time `k`, not the law of
the pooled estimator; the identification of `tiltedExpectation Σ_k⁻¹ 0` with Mathlib's
`multivariateGaussian 0 Σ_k` (the sampler files' trajectory law) is standard but not
machine-checked.
-/

open Matrix Filter Topology Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Conjugation by the eigenbasis -/

/-- `(U D₁ Uᵀ)(U D₂ Uᵀ) = U (D₁D₂) Uᵀ`. -/
theorem conj_mul_conj {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (D₁ D₂ : Matrix ι ι ℝ) :
    (orthoOf hA * D₁ * (orthoOf hA)ᵀ) * (orthoOf hA * D₂ * (orthoOf hA)ᵀ) =
      orthoOf hA * (D₁ * D₂) * (orthoOf hA)ᵀ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (orthoOf hA)ᵀ (orthoOf hA), orthoOf_transpose_mul hA, Matrix.one_mul]

/-- `(U D Uᵀ)ⁿ = U Dⁿ Uᵀ`. -/
theorem conj_pow {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (D : Matrix ι ι ℝ) (n : ℕ) :
    (orthoOf hA * D * (orthoOf hA)ᵀ) ^ n = orthoOf hA * D ^ n * (orthoOf hA)ᵀ := by
  induction n with
  | zero => simp [orthoOf_mul_transpose hA]
  | succ n ih => rw [pow_succ, ih, conj_mul_conj hA, pow_succ]

/-- `1 − U D Uᵀ = U (1 − D) Uᵀ`. -/
theorem one_sub_conj {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (D : Matrix ι ι ℝ) :
    (1 : Matrix ι ι ℝ) - orthoOf hA * D * (orthoOf hA)ᵀ =
      orthoOf hA * (1 - D) * (orthoOf hA)ᵀ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, orthoOf_mul_transpose hA]

/-- `Uᵀ (U D Uᵀ) U = D`. -/
theorem conj_left_inv {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (D : Matrix ι ι ℝ) :
    (orthoOf hA)ᵀ * (orthoOf hA * D * (orthoOf hA)ᵀ) * orthoOf hA = D := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (orthoOf hA)ᵀ (orthoOf hA), orthoOf_transpose_mul hA, Matrix.one_mul,
    Matrix.mul_one]

/-- `(U diag(d) Uᵀ)⁻¹ = U diag(d⁻¹) Uᵀ` for `d ≠ 0`. -/
theorem inv_conj_diagonal {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {d : ι → ℝ}
    (hd : ∀ i, d i ≠ 0) :
    (orthoOf hA * diagonal d * (orthoOf hA)ᵀ)⁻¹ =
      orthoOf hA * diagonal (fun i => (d i)⁻¹) * (orthoOf hA)ᵀ := by
  apply Matrix.inv_eq_left_inv
  rw [conj_mul_conj hA, diagonal_mul_diagonal]
  have e : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) := funext fun i => by
    simp [inv_mul_cancel₀ (hd i)]
  rw [e, Matrix.diagonal_one, Matrix.mul_one, orthoOf_mul_transpose hA]

/-- `det(U D Uᵀ) = det D`. -/
theorem det_orthoOf_conj {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (D : Matrix ι ι ℝ) :
    (orthoOf hA * D * (orthoOf hA)ᵀ).det = D.det := by
  rw [← det_conj_orthoOf hA (orthoOf hA * D * (orthoOf hA)ᵀ), conj_left_inv hA]

/-! ### The burn-in covariance and its precision -/

/-- **The burn-in covariance in the eigenbasis**:
`ulaCov P h · (1 − (ulaStep P h)^{2k}) = U diag((1 − ρᵢ^{2k})/(pᵢ(1 − hpᵢ/2))) Uᵀ`. -/
theorem burnInCov_eq_conj {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (k : ℕ) :
    ulaCov P h * (1 - ulaStep P h ^ (2 * k)) =
      orthoOf hP.1 *
        diagonal (fun i => 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
          (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k))) * (orthoOf hP.1)ᵀ := by
  rw [ulaCov_eq_conj_diagonal hP hh hev, ulaStep_eq_conj hP.1 h, conj_pow hP.1, one_sub_conj hP.1,
    conj_mul_conj hP.1, diagonal_pow, ← Matrix.diagonal_one, diagonal_sub, diagonal_mul_diagonal]
  simp only [Pi.pow_apply]

/-- The burn-in variances are positive for `k ≥ 1` under stability. -/
theorem burnInVar_pos {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (i : ι) :
    0 < 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) := by
  have hp := hP.eigenvalues_pos i
  have h2 := hev i
  have ha : 0 < 1 - h * hP.1.eigenvalues i / 2 := by linarith
  have hρ : (1 - h * hP.1.eigenvalues i) ^ 2 < 1 := by nlinarith [mul_pos hh hp]
  have hf : (1 - h * hP.1.eigenvalues i) ^ (2 * k) < 1 := by
    rw [pow_mul]
    exact pow_lt_one₀ (sq_nonneg _) hρ (by omega)
  have : 0 < 1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k) := by linarith
  positivity

/-- **The burn-in precision**: for `k ≥ 1`,
`(ulaCov P h · (1 − (ulaStep P h)^{2k}))⁻¹ = U diag(pᵢ(1 − hpᵢ/2)/(1 − ρᵢ^{2k})) Uᵀ`. -/
theorem burnInCov_inv_eq_conj {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ =
      orthoOf hP.1 *
        diagonal (fun i => (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
          (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹) * (orthoOf hP.1)ᵀ := by
  rw [burnInCov_eq_conj hP hh hev k]
  exact inv_conj_diagonal hP.1 fun i => (burnInVar_pos hP hh hev hk i).ne'

theorem burnInCov_inv_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹.PosDef := by
  rw [burnInCov_inv_eq_conj hP hh hev hk]
  exact posDef_of_orthoOf_conj hP.1 (fun i => inv_pos.mpr (burnInVar_pos hP hh hev hk i))
    (conj_left_inv hP.1 _)

/-! ### The burn-in Gamma law -/

/-- The per-direction factor: `q/(q + s p) = a/(a + s f)` for `q = p a / f`. -/
theorem burnIn_factor {p a f s : ℝ} (hp : 0 < p) (ha : 0 < a) (hf : 0 < f) (hs : 0 ≤ s) :
    (1 / (p * a) * f)⁻¹ / ((1 / (p * a) * f)⁻¹ + s * p) = a / (a + s * f) := by
  have e : (1 / (p * a) * f)⁻¹ = p * a / f := by
    field_simp
  rw [e, div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-- **The burn-in Gamma law**: for `s ≥ 0` and `k ≥ 1`, the Laplace transform of the LLC statistic
`½uᵀPu` under the centred Gaussian law with the burn-in covariance `Σ_k` is
`√(∏ᵢ (1 − hpᵢ/2)/((1 − hpᵢ/2) + s(1 − ρᵢ^{2k})))` — a sum of independent
`Gamma(½, rate (1 − hpᵢ/2)/(1 − ρᵢ^{2k}))` variables. -/
theorem laplace_ulaBurnIn {P : Matrix ι ι ℝ} (hP : P.PosDef) {h s : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (hs : 0 ≤ s) {k : ℕ} (hk : 1 ≤ k) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ 0
        (fun u => Real.exp (-(s * ((1 / 2) * (u ⬝ᵥ P *ᵥ u))))) =
      Real.sqrt (∏ i, (1 - h * hP.1.eigenvalues i / 2) /
        (1 - h * hP.1.eigenvalues i / 2 + s * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  have hQs : ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P).PosDef :=
    hQ.add_posSemidef (hP.posSemidef.smul hs)
  rw [tiltedExpectation_exp_quadForm hQ hQs]
  have hdiagP := orthoOf_transpose_localised_mul hP.1 s 0
  simp only [zero_smul, add_zero] at hdiagP
  have hdet1 : (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹.det =
      ∏ i, (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
        (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ := by
    rw [burnInCov_inv_eq_conj hP hh hev hk, det_orthoOf_conj hP.1, Matrix.det_diagonal]
  have hdet2 : ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P).det =
      ∏ i, ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
        (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i) := by
    rw [← det_conj_orthoOf hP.1, Matrix.mul_add, Matrix.add_mul, burnInCov_inv_eq_conj hP hh hev hk,
      conj_left_inv hP.1, hdiagP, Matrix.diagonal_add, Matrix.det_diagonal]
  have hnum : ∀ i, 0 ≤ (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i := fun i => by
    have := burnInVar_pos hP hh hev hk i
    have := hP.eigenvalues_pos i
    positivity
  rw [hdet1, hdet2, ← Real.sqrt_div' _ (Finset.prod_nonneg fun i _ => hnum i),
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hp := hP.eigenvalues_pos i
  have ha : 0 < 1 - h * hP.1.eigenvalues i / 2 := by linarith [hev i]
  have hf : 0 < 1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k) := by
    have h1 := burnInVar_pos hP hh hev hk i
    have h2 : 0 < 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := by positivity
    exact (pos_iff_pos_of_mul_pos h1).mp h2
  exact burnIn_factor hp ha hf hs

/-! ### The mean along the trajectory -/

/-- **The burn-in mean**: `⟨½uᵀPu⟩_{Σ_k} = ½∑ᵢ (1 − ρᵢ^{2k})/(1 − hpᵢ/2)`, the eigen form of the
trajectory trace `½ tr(P Σ_k)`. -/
theorem burnIn_mean {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ 0
        (fun u => (1 / 2) * (u ⬝ᵥ P *ᵥ u)) =
      (1 / 2) * ∑ i, (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) /
        (1 - h * hP.1.eigenvalues i / 2) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hQ]
  have hm : tiltMean (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ 0 = 0 := by simp [tiltMean]
  rw [hm, zero_dotProduct, add_zero]
  congr 1
  have hinv : ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹)⁻¹ =
      ulaCov P h * (1 - ulaStep P h ^ (2 * k)) :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (by rw [burnInCov_eq_conj hP hh hev k, det_orthoOf_conj hP.1, Matrix.det_diagonal]
          exact (Finset.prod_pos fun i _ => burnInVar_pos hP hh hev hk i).ne'))
  rw [hinv, sum_mul_apply_eq_trace, burnInCov_eq_conj hP hh hev k]
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [hPt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc, orthoOf_transpose_mul_mul hP.1, diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := hP.eigenvalues_pos i
  have ha : 0 < 1 - h * hP.1.eigenvalues i / 2 := by linarith [hev i]
  field_simp

/-- **The burn-in bias of the LLC**: the stationary ULA mean `½∑ᵢ 1/(1 − hpᵢ/2)` exceeds the burn-in
mean by exactly `½∑ᵢ ρᵢ^{2k}/(1 − hpᵢ/2)`. -/
theorem burnIn_bias {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    (1 / 2) * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) -
      tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ 0
        (fun u => (1 / 2) * (u ⬝ᵥ P *ᵥ u)) =
      (1 / 2) * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * k) / (1 - h * hP.1.eigenvalues i / 2) := by
  rw [burnIn_mean hP hh hev hk, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_sub_div_same]
  ring_nf

/-! ### Monotonicity in `k` and the stationary limit -/

/-- The burn-in transform, as an explicit function of the step count. -/
noncomputable def burnInTransform (p : ι → ℝ) (h s : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (∏ i, (1 - h * p i / 2) / (1 - h * p i / 2 + s * (1 - (1 - h * p i) ^ (2 * k))))

omit [DecidableEq ι] in
/-- The transform is nonincreasing in the step count: `L_{k+1}(s) ≤ L_k(s)`. -/
theorem burnInTransform_antitone {p : ι → ℝ} {h s : ℝ} (hh : 0 < h) (hp : ∀ i, 0 < p i)
    (hev : ∀ i, h * p i < 2) (hs : 0 ≤ s) : Antitone (burnInTransform p h s) := by
  refine antitone_nat_of_succ_le fun k => ?_
  unfold burnInTransform
  apply Real.sqrt_le_sqrt
  apply Finset.prod_le_prod
  · intro i _
    have ha : 0 < 1 - h * p i / 2 := by linarith [hev i]
    have hρ : (1 - h * p i) ^ 2 < 1 := by nlinarith [mul_pos hh (hp i)]
    have hf : (1 - h * p i) ^ (2 * (k + 1)) ≤ 1 := by
      rw [pow_mul]
      exact pow_le_one₀ (sq_nonneg _) hρ.le
    have : 0 ≤ 1 - (1 - h * p i) ^ (2 * (k + 1)) := by linarith
    positivity
  · intro i _
    have ha : 0 < 1 - h * p i / 2 := by linarith [hev i]
    have hρ : (1 - h * p i) ^ 2 < 1 := by nlinarith [mul_pos hh (hp i)]
    have hmono : (1 - h * p i) ^ (2 * (k + 1)) ≤ (1 - h * p i) ^ (2 * k) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_of_le_one (sq_nonneg _) hρ.le (by omega)
    have hk0 : (1 - h * p i) ^ (2 * k) ≤ 1 := by
      rw [pow_mul]
      exact pow_le_one₀ (sq_nonneg _) hρ.le
    apply div_le_div_of_nonneg_left ha.le
    · have : 0 ≤ 1 - (1 - h * p i) ^ (2 * k) := by linarith
      positivity
    · nlinarith

omit [DecidableEq ι] in
/-- **The stationary limit**: `L_k(s) → √(∏ᵢ (1 − hpᵢ/2)/(1 − hpᵢ/2 + s))`, the stationary ULA
transform (`GammaLaw.laplace_ula`), as `k → ∞`. -/
theorem burnInTransform_tendsto {p : ι → ℝ} {h s : ℝ} (hh : 0 < h) (hp : ∀ i, 0 < p i)
    (hev : ∀ i, h * p i < 2) (hs : 0 ≤ s) :
    Tendsto (burnInTransform p h s) atTop
      (𝓝 (Real.sqrt (∏ i, (1 - h * p i / 2) / (1 - h * p i / 2 + s)))) := by
  unfold burnInTransform
  refine (Real.continuous_sqrt.tendsto _).comp ?_
  refine tendsto_finsetProd _ fun i _ => ?_
  have hρ : |1 - h * p i| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hp i, hev i, mul_pos hh (hp i)]
  have h1 : Tendsto (fun k : ℕ => (1 - h * p i) ^ (2 * k)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ
    exact this.comp (tendsto_id.const_mul_atTop' two_pos)
  have h2 : Tendsto (fun k : ℕ => 1 - h * p i / 2 + s * (1 - (1 - h * p i) ^ (2 * k))) atTop
      (𝓝 (1 - h * p i / 2 + s * (1 - 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub h1))
  rw [sub_zero, mul_one] at h2
  exact tendsto_const_nhds.div h2 (by linarith [hev i] : (0 : ℝ) < 1 - h * p i / 2 + s).ne'

end Laplace.Sampler
