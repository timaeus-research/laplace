/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnchoredCovarianceGap

/-!
# The ULA burn-in law from an arbitrary start (E4)

ULA on the Gaussian target with precision `P` from a start `x₀` has after `k` updates the law
`N(m_k, Σ_k)`, `m_k = (1 − hP)^k x₀` (`burnInMean`), `Σ_k = ulaCov·(1 − ulaStep^{2k})` (tide 92),
which we
formalise as the tilted Gaussian `tiltedExpectation Σ_k⁻¹ (Σ_k⁻¹ m_k)` (`burnInTilt`). In the
eigenbasis
(`pᵢ`, `ρᵢ = 1 − hpᵢ`, `aᵢ = 1 − hpᵢ/2`, `fᵢ = 1 − ρᵢ^{2k}`, `bᵢ = (Uᵀx₀)ᵢ`), for `k ≥ 1`:
* `burnIn_mean_start`: `⟨½uᵀPu⟩_k = ½∑ᵢfᵢ/aᵢ + ½∑ᵢpᵢρᵢ^{2k}bᵢ²` — tide 92's covariance part plus the
  geometrically decaying energy of the mean; `burnIn_bias_start`: against the stationary ULA mean
  `½∑1/aᵢ` the bias is `½∑ᵢρᵢ^{2k}(pᵢbᵢ² − 1/aᵢ)`, so each mode's contribution keeps the sign of
  `pᵢbᵢ² − 1/aᵢ` (start energy above or below the stationary mode energy) and a hot start can sit
  *above* the stationary mean and approach it non-monotonically;
* `burnIn_var_start`: `Var_k(½uᵀPu) = ½∑ᵢ(fᵢ/aᵢ)² + ∑ᵢpᵢρᵢ^{2k}bᵢ²·fᵢ/aᵢ` (tide 96's tilted
variance);
* `laplace_ulaBurnIn_start`: for `s ≥ 0`,
  `⟨e^{−s·½uᵀPu}⟩_k = exp(−½∑ᵢ s pᵢaᵢρᵢ^{2k}bᵢ²/(aᵢ + s fᵢ))·√∏ᵢaᵢ/(aᵢ + s fᵢ)` — a sum of
  independent
  noncentral `Gamma(½)` variables (mode `i` is `(fᵢ/(2aᵢ))·χ²₁(δᵢ)`, `δᵢ = pᵢaᵢρᵢ^{2k}bᵢ²/fᵢ`),
  reducing to
  tide 92's Gamma law at `x₀ = 0`;
* `burnIn_transient_tendsto`, `burnIn_mean_start_tendsto`: the transient vanishes and the mean
tends to
  the stationary ULA mean as `k → ∞`.
As in tide 92, the identification of the tilted Gaussian with the trajectory law is prose.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `k`-step ULA mean from the start `x₀`: `m_k = (1 − hP)^k x₀`. -/
noncomputable def burnInMean (P : Matrix ι ι ℝ) (h : ℝ) (k : ℕ) (x₀ : ι → ℝ) : ι → ℝ :=
  ulaStep P h ^ k *ᵥ x₀

/-- The tilt of the `k`-step law from `x₀`: `Σ_k⁻¹ m_k`. -/
noncomputable def burnInTilt (P : Matrix ι ι ℝ) (h : ℝ) (k : ℕ) (x₀ : ι → ℝ) : ι → ℝ :=
  (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ *ᵥ burnInMean P h k x₀

/-! ### Algebra of the tilt and of the burn-in covariance -/

theorem tiltMean_mulVec_self {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) (m : ι → ℝ) :
    tiltMean Q (Q *ᵥ m) = m := by
  unfold tiltMean
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'),
    Matrix.one_mulVec]

theorem ulaStep_pow_eq_conj {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) (k : ℕ) :
    ulaStep P h ^ k =
      orthoOf hP * diagonal (fun i => (1 - h * hP.eigenvalues i) ^ k) * (orthoOf hP)ᵀ := by
  rw [ulaStep_eq_conj hP h, conj_pow hP, diagonal_pow]
  rfl

theorem burnInMean_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) (h : ℝ) (k : ℕ) (x₀ : ι → ℝ) :
    burnInMean P h k x₀ = orthoOf hP.1 *ᵥ
      (diagonal (fun i => (1 - h * hP.1.eigenvalues i) ^ k) *ᵥ ((orthoOf hP.1)ᵀ *ᵥ x₀)) := by
  unfold burnInMean
  rw [ulaStep_pow_eq_conj hP.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem burnInCov_det_ne_zero {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h
    * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) : (ulaCov P h * (1 - ulaStep P h ^ (2 * k))).det
        ≠ 0 := by
  rw [burnInCov_eq_conj hP hh hev k, det_orthoOf_conj hP.1, Matrix.det_diagonal]
  exact (Finset.prod_pos fun i _ => burnInVar_pos hP hh hev hk i).ne'

theorem burnInCov_inv_inv {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) : (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ =
        (ulaCov P h * (1 - ulaStep P h ^ (2 * k))) :=
  Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (burnInCov_det_ne_zero hP hh hev hk))

/-- `tr(PΣ_k) = ∑ᵢ fᵢ/aᵢ`, read off tide 92's `burnIn_mean`. -/
theorem burnIn_trace {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i, ∑ j, P i j * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ i j = ∑ i, (1 - (1 - h *
        hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i / 2) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  have h0 := burnIn_mean hP hh hev hk
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hQ] at h0
  have hm : tiltMean (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ 0 = 0 := by simp [tiltMean]
  rw [hm, Matrix.mulVec_zero, dotProduct_zero, add_zero] at h0
  linarith

/-- `m_kᵀPm_k = ∑ᵢ pᵢρᵢ^{2k}bᵢ²`. -/
theorem burnIn_quadForm_mean {P : Matrix ι ι ℝ} (hP : P.PosDef) (h : ℝ) (k : ℕ) (x₀ : ι → ℝ) :
    burnInMean P h k x₀ ⬝ᵥ P *ᵥ burnInMean P h k x₀ =
      ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀) i
          ^ 2) := by
  rw [burnInMean_eq hP, Matrix.mulVec_mulVec _ P (orthoOf hP.1), mul_orthoOf_eq hP.1,
    ← Matrix.mulVec_mulVec, dotProduct_orthoOf_mulVec hP.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The mean and its bias -/

/-- **The burn-in mean from a start `x₀`**: `⟨½uᵀPu⟩_k = ½∑ᵢfᵢ/aᵢ + ½∑ᵢpᵢρᵢ^{2k}bᵢ²`. -/
theorem burnIn_mean_start {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) (fun u =>
        (1 / 2) * (u ⬝ᵥ P *ᵥ u)) =
      1 / 2 * ∑ i, (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i / 2)
          + 1 / 2 * ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf
              hP.1)ᵀ *ᵥ x₀) i ^ 2) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  unfold burnInTilt
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hQ, tiltMean_mulVec_self hQ,
    burnIn_trace hP hh hev hk, burnIn_quadForm_mean hP]
  ring

/-- **The signed burn-in bias**: `⟨½uᵀPu⟩_k − ½∑1/aᵢ = ½∑ᵢρᵢ^{2k}(pᵢbᵢ² − 1/aᵢ)`. -/
theorem burnIn_bias_start {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) (fun u =>
        (1 / 2) * (u ⬝ᵥ P *ᵥ u)) -
      1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) =
      1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * k) * (hP.1.eigenvalues i * ((orthoOf hP.1)ᵀ
          *ᵥ x₀) i ^ 2 - 1 / (1 - h * hP.1.eigenvalues i / 2)) := by
  rw [burnIn_mean_start hP hh hev hk x₀]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The variance -/

theorem mul_burnInCov_eq_conj {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h
    * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    P * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ = orthoOf hP.1 * diagonal (fun i =>
        hP.1.eigenvalues i * (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1
            - h * hP.1.eigenvalues i) ^ (2 * k)))) * (orthoOf hP.1)ᵀ := by
  rw [burnInCov_inv_inv hP hh hev hk, burnInCov_eq_conj hP hh hev k, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, mul_orthoOf_eq hP.1, Matrix.mul_assoc (orthoOf hP.1),
    Matrix.diagonal_mul_diagonal]

theorem burnIn_trace_sq {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) :
    ∑ a, ∑ c, (P * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) a c * (P * (ulaCov P h * (1 -
        ulaStep P h ^ (2 * k)))⁻¹⁻¹) c a = ∑ i, (hP.1.eigenvalues i * (1 / (hP.1.eigenvalues i * (1
            - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))) ^ 2 :=
                by
  have e : ∑ a, ∑ c, (P * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) a c * (P * (ulaCov P h *
      (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) c a =
      Matrix.trace ((P * (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹) * (P * (ulaCov P h * (1 -
          ulaStep P h ^ (2 * k)))⁻¹⁻¹)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, mul_burnInCov_eq_conj hP hh hev hk, Laplace.Sampler.conj_mul_conj hP.1,
    Matrix.trace_mul_cycle, orthoOf_transpose_mul hP.1, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem burnIn_cross {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    (P *ᵥ burnInMean P h k x₀) ⬝ᵥ (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ *ᵥ (P *ᵥ
        burnInMean P h k x₀) =
      ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i) *
          ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h *
              hP.1.eigenvalues i) ^ (2 * k))) * (hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i)
                  ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i))) := by
  have hPm : P *ᵥ burnInMean P h k x₀ = orthoOf hP.1 *ᵥ (diagonal hP.1.eigenvalues *ᵥ
      (diagonal (fun i => (1 - h * hP.1.eigenvalues i) ^ k) *ᵥ ((orthoOf hP.1)ᵀ *ᵥ x₀))) := by
    rw [burnInMean_eq hP, Matrix.mulVec_mulVec _ P (orthoOf hP.1), mul_orthoOf_eq hP.1,
      ← Matrix.mulVec_mulVec]
  rw [hPm, burnInCov_inv_inv hP hh hev hk, burnInCov_eq_conj hP hh hev k, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (orthoOf hP.1)ᵀ (orthoOf hP.1),
    orthoOf_transpose_mul hP.1, Matrix.one_mulVec, dotProduct_orthoOf_mulVec hP.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]

/-- **The burn-in variance from a start `x₀`**: `Var_k(½uᵀPu) = ½∑ᵢ(fᵢ/aᵢ)² +
∑ᵢpᵢρᵢ^{2k}bᵢ²·fᵢ/aᵢ`. -/
theorem burnIn_var_start {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) (fun u =>
        ((1 / 2) * (u ⬝ᵥ P *ᵥ u)) ^ 2) -
      (tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) (fun u
          => (1 / 2) * (u ⬝ᵥ P *ᵥ u))) ^ 2 =
      1 / 2 * ∑ i, ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i /
          2)) ^ 2 +
        ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀)
            i ^ 2) * ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i /
                2)) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  have e1 : (fun u : ι → ℝ => ((1 / 2 : ℝ) * (u ⬝ᵥ P *ᵥ u)) ^ 2) =
      fun u => (1 / 4 : ℝ) * (u ⬝ᵥ P *ᵥ u) ^ 2 := by
    funext u
    ring
  unfold burnInTilt
  rw [e1, tiltedExpectation_const_mul, tiltedExpectation_const_mul]
  have hvar := tiltedVar_quadForm hQ ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ *ᵥ burnInMean P
      h k x₀) hP.1
  rw [tiltMean_mulVec_self hQ, burnIn_trace_sq hP hh hev hk, burnIn_cross hP hh hev hk x₀] at hvar
  have hne : ∀ i, hP.1.eigenvalues i ≠ 0 ∧ (1 - h * hP.1.eigenvalues i / 2) ≠ 0 := fun i =>
    ⟨(hP.eigenvalues_pos i).ne', by have := hev i; intro h0; linarith⟩
  have e2 : ∑ i, (hP.1.eigenvalues i * (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))
      * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))) ^ 2 = ∑ i, ((1 - (1 - h * hP.1.eigenvalues
          i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i / 2)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      obtain ⟨hp, ha⟩ := hne i
      field_simp
  have e3 : ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀)
      i) * ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h *
          hP.1.eigenvalues i) ^ (2 * k))) * (hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ k
              * ((orthoOf hP.1)ᵀ *ᵥ x₀) i))) =
      ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀) i
          ^ 2) * ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i / 2))
              :=
    Finset.sum_congr rfl fun i _ => by
      obtain ⟨hp, ha⟩ := hne i
      field_simp
      ring
  rw [e2, e3] at hvar
  linear_combination (1 / 4 : ℝ) * hvar

/-! ### The Laplace transform: a noncentral Gamma law -/

theorem burnInPrecision_add_eq_conj {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev :
    ∀ i, h * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (s : ℝ) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P = orthoOf hP.1 * diagonal (fun i => (1 /
        (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h * hP.1.eigenvalues i)
            ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i) * (orthoOf hP.1)ᵀ := by
  have hP' := frame_eq_conj (orthoOf_transpose_mul hP.1) (orthoOf_transpose_mul_mul hP.1)
  have e : diagonal (fun i => (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 -
      (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i) =
      diagonal (fun i => (1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h
          * hP.1.eigenvalues i) ^ (2 * k)))⁻¹) + s • diagonal hP.1.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [burnInCov_inv_eq_conj hP hh hev hk, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← hP']

theorem burnInPrecision_add_inv {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i,
    h * hP.1.eigenvalues i < 2) {s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : 1 ≤ k) :
    ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P)⁻¹ =
      orthoOf hP.1 * diagonal (fun i => ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i /
          2)) * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i)⁻¹) *
              (orthoOf hP.1)ᵀ := by
  rw [burnInPrecision_add_eq_conj hP hh hev hk s]
  exact inv_conj_diagonal hP.1 fun i =>
    (add_pos_of_pos_of_nonneg (inv_pos.mpr (burnInVar_pos hP hh hev hk i))
      (mul_nonneg hs (hP.eigenvalues_pos i).le)).ne'

theorem burnInTilt_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    burnInTilt P h k x₀ = orthoOf hP.1 *ᵥ (diagonal (fun i => (1 / (hP.1.eigenvalues i * (1 - h *
        hP.1.eigenvalues i / 2)) * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹) *ᵥ
      (diagonal (fun i => (1 - h * hP.1.eigenvalues i) ^ k) *ᵥ ((orthoOf hP.1)ᵀ *ᵥ x₀))) := by
  unfold burnInTilt
  rw [burnInCov_inv_eq_conj hP hh hev hk, burnInMean_eq hP, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (orthoOf hP.1)ᵀ (orthoOf hP.1),
    orthoOf_transpose_mul hP.1, Matrix.one_mulVec]

theorem burnIn_tiltMean_shift_dot {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀
    i, h * hP.1.eigenvalues i < 2) {s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltMean ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P) (burnInTilt P h k x₀) ⬝ᵥ
        burnInTilt P h k x₀ =
      ∑ i, ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h *
          hP.1.eigenvalues i) ^ (2 * k)))⁻¹ + s * hP.1.eigenvalues i)⁻¹ * ((1 / (hP.1.eigenvalues i
              * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹
                  * ((1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i)) *
        ((1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h *
            hP.1.eigenvalues i) ^ (2 * k)))⁻¹ * ((1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf
                hP.1)ᵀ *ᵥ x₀) i)) := by
  unfold tiltMean
  rw [burnInPrecision_add_inv hP hh hev hs hk, burnInTilt_eq hP hh hev hk x₀, ←
      Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (orthoOf hP.1)ᵀ (orthoOf hP.1),
    orthoOf_transpose_mul hP.1, Matrix.one_mulVec, dotProduct_orthoOf_mulVec hP.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]

theorem burnIn_tiltMean_dot {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h *
    hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltMean (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) ⬝ᵥ burnInTilt P h k
        x₀ =
      ∑ i, (1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i * ((1 / (hP.1.eigenvalues i
          * (1 - h * hP.1.eigenvalues i / 2)) * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))⁻¹ *
              ((1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i)) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  have hm : tiltMean (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) =
      burnInMean P h k x₀ := by
    unfold burnInTilt
    exact tiltMean_mulVec_self hQ _
  rw [hm, burnInTilt_eq hP hh hev hk x₀, burnInMean_eq hP, dotProduct_orthoOf_mulVec hP.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]

/-- **The burn-in Laplace transform from a start `x₀`** (a sum of independent noncentral `Gamma(½)`
variables): for `s ≥ 0`, `k ≥ 1`,
`⟨e^{−s·½uᵀPu}⟩_k = exp(−½∑ᵢ s pᵢaᵢρᵢ^{2k}bᵢ²/(aᵢ + s fᵢ))·√∏ᵢ aᵢ/(aᵢ + s fᵢ)`. -/
theorem laplace_ulaBurnIn_start {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i,
    h * hP.1.eigenvalues i < 2) {s : ℝ} (hs : 0 ≤ s) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀)
        (fun u => Real.exp (-(s * ((1 / 2) * (u ⬝ᵥ P *ᵥ u))))) =
      Real.exp (-(1 / 2 * ∑ i, s * hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2) * ((1 - h
          * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2) / ((1 - h *
              hP.1.eigenvalues i / 2) + s * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k))))) *
        Real.sqrt (∏ i, (1 - h * hP.1.eigenvalues i / 2) / ((1 - h * hP.1.eigenvalues i / 2) + s *
            (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))) := by
  have hQ := burnInCov_inv_posDef hP hh hev hk
  have hQs : ((ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P).PosDef := hQ.add_posSemidef
      (hP.posSemidef.smul hs)
  have hratio : Real.sqrt (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹.det / Real.sqrt ((ulaCov P h
      * (1 - ulaStep P h ^ (2 * k)))⁻¹ + s • P).det =
      Real.sqrt (∏ i, (1 - h * hP.1.eigenvalues i / 2) / ((1 - h * hP.1.eigenvalues i / 2) + s * (1
          - (1 - h * hP.1.eigenvalues i) ^ (2 * k)))) := by
    have h0 := laplace_ulaBurnIn hP hh hev hs hk
    rw [tiltedExpectation_exp_quadForm_tilted hQ hQs 0] at h0
    simpa using h0
  rw [tiltedExpectation_exp_quadForm_tilted hQ hQs, hratio, burnIn_tiltMean_shift_dot hP hh hev hs
      hk x₀,
    burnIn_tiltMean_dot hP hh hev hk x₀]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ←
      Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := hP.eigenvalues_pos i
  have ha : 0 < (1 - h * hP.1.eigenvalues i / 2) := by linarith [hev i]
  have hf : 0 < (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) := by
    have h1 := burnInVar_pos hP hh hev hk i
    have h2 : 0 < 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := by positivity
    exact (pos_iff_pos_of_mul_pos h1).mp h2
  have hafs : 0 < (1 - h * hP.1.eigenvalues i / 2) + s * (1 - (1 - h * hP.1.eigenvalues i) ^ (2 *
      k)) := by positivity
  set pp := hP.1.eigenvalues i with hpp
  set aa := (1 - h * hP.1.eigenvalues i / 2) with haa
  set ff := (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) with hff
  set y := (1 - h * hP.1.eigenvalues i) ^ k * ((orthoOf hP.1)ᵀ *ᵥ x₀) i with hy
  have hp' := hp.ne'
  have ha' := ha.ne'
  have hf' := hf.ne'
  have hafs' := hafs.ne'
  have hq : (1 / (pp * aa) * ff)⁻¹ = pp * aa / ff := by
    rw [one_div, inv_mul_eq_div, inv_div]
  have e1 : pp * aa / ff + s * pp = pp * (aa + s * ff) / ff := by
    rw [div_add' _ _ _ hf']
    congr 1
    ring
  have hy2 : (1 - h * pp) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2 = y ^ 2 := by
    rw [hy]
    ring
  rw [hq, e1, inv_div, hy2]
  field_simp
  ring

/-! ### The stationary limit -/

theorem burnIn_rho_pow_tendsto {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i,
    h * hP.1.eigenvalues i < 2) (i : ι) :
    Tendsto (fun k : ℕ => (1 - h * hP.1.eigenvalues i) ^ (2 * k)) atTop (𝓝 0) := by
  have hp := hP.eigenvalues_pos i
  have habs : |1 - h * hP.1.eigenvalues i| < 1 := by
    have := hev i
    rw [abs_lt]
    constructor <;> nlinarith
  have hsq : |(1 - h * hP.1.eigenvalues i) ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (1 - h * hP.1.eigenvalues i)]
  simp_rw [pow_mul]
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hsq

/-- The mean-energy transient `∑ᵢpᵢρᵢ^{2k}bᵢ²` vanishes as `k → ∞`. -/
theorem burnIn_transient_tendsto {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀
    i, h * hP.1.eigenvalues i < 2) (x₀ : ι → ℝ) :
    Tendsto (fun k : ℕ => ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) *
        ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2)) atTop (𝓝 0) := by
  have : ∀ i, Tendsto (fun k : ℕ => hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) *
      ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2)) atTop (𝓝 0) := fun i => by
    simpa using ((burnIn_rho_pow_tendsto hP hh hev i).mul_const (((orthoOf hP.1)ᵀ *ᵥ x₀) i ^
        2)).const_mul (hP.1.eigenvalues i)
  simpa using tendsto_finsetSum Finset.univ fun i _ => this i

/-- **The burn-in mean from any start tends to the stationary ULA mean** `½∑ᵢ1/aᵢ`. -/
theorem burnIn_mean_start_tendsto {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀
    i, h * hP.1.eigenvalues i < 2) (x₀ : ι → ℝ) :
    Tendsto (fun k : ℕ => 1 / 2 * ∑ i, (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
        hP.1.eigenvalues i / 2) + 1 / 2 * ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^
            (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2))
      atTop (𝓝 (1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2))) := by
  have h1 : Tendsto (fun k : ℕ => ∑ i, (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
      hP.1.eigenvalues i / 2)) atTop (𝓝 (∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (burnIn_rho_pow_tendsto hP hh hev
        i)).div_const (1 - h * hP.1.eigenvalues i / 2)
  have h2 := burnIn_transient_tendsto hP hh hev x₀
  simpa using (h1.const_mul (1 / 2 : ℝ)).add (h2.const_mul (1 / 2 : ℝ))

/-- **The stationary variance limit**: `Var_k(½uᵀPu) → ½∑ᵢ1/aᵢ²`. -/
theorem burnIn_var_start_tendsto {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀
    i, h * hP.1.eigenvalues i < 2) (x₀ : ι → ℝ) :
    Tendsto (fun k : ℕ => 1 / 2 * ∑ i, ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
        hP.1.eigenvalues i / 2)) ^ 2 +
        ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k) * ((orthoOf hP.1)ᵀ *ᵥ x₀)
            i ^ 2) * ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h * hP.1.eigenvalues i /
                2)))
      atTop (𝓝 (1 / 2 * ∑ i, (1 / (1 - h * hP.1.eigenvalues i / 2)) ^ 2)) := by
  have hw : ∀ i, Tendsto (fun k : ℕ => (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
      hP.1.eigenvalues i / 2)) atTop (𝓝 (1 / (1 - h * hP.1.eigenvalues i / 2))) := fun i => by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (burnIn_rho_pow_tendsto hP hh hev
        i)).div_const (1 - h * hP.1.eigenvalues i / 2)
  have h1 : Tendsto (fun k : ℕ => ∑ i, ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
      hP.1.eigenvalues i / 2)) ^ 2) atTop (𝓝 (∑ i, (1 / (1 - h * hP.1.eigenvalues i / 2)) ^ 2)) :=
    tendsto_finsetSum _ fun i _ => (hw i).pow 2
  have h2 : Tendsto (fun k : ℕ => ∑ i, hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k)
      * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2) * ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
          hP.1.eigenvalues i / 2))) atTop
      (𝓝 0) := by
    have : ∀ i, Tendsto (fun k : ℕ => hP.1.eigenvalues i * ((1 - h * hP.1.eigenvalues i) ^ (2 * k)
        * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2) * ((1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) / (1 - h *
            hP.1.eigenvalues i / 2))) atTop
        (𝓝 0) := fun i => by
      simpa using (((burnIn_rho_pow_tendsto hP hh hev i).mul_const (((orthoOf hP.1)ᵀ *ᵥ x₀) i ^
          2)).const_mul (hP.1.eigenvalues i)).mul (hw i)
    simpa using tendsto_finsetSum Finset.univ fun i _ => this i
  simpa using (h1.const_mul (1 / 2 : ℝ)).add h2

/-- **A geometric bias bound**: if `ρᵢ² ≤ R` for all modes then
`|⟨½uᵀPu⟩_k − ½∑1/aᵢ| ≤ ½R^k∑ᵢ|pᵢbᵢ² − 1/aᵢ|` — burn-in from any start at the rate of the slowest
mode. -/
theorem burnIn_bias_start_le {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h
    * hP.1.eigenvalues i < 2) {k : ℕ} (hk : 1 ≤ k) (x₀ : ι → ℝ) {R : ℝ}
    (hR : ∀ i, (1 - h * hP.1.eigenvalues i) ^ 2 ≤ R) :
    |tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTilt P h k x₀) (fun u =>
        (1 / 2) * (u ⬝ᵥ P *ᵥ u)) -
        1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)| ≤
      1 / 2 * R ^ k * ∑ i, |hP.1.eigenvalues i * ((orthoOf hP.1)ᵀ *ᵥ x₀) i ^ 2 - 1 / (1 - h *
          hP.1.eigenvalues i / 2)| := by
  rw [burnIn_bias_start hP hh hev hk x₀, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    mul_assoc, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) (by norm_num)
  rw [abs_mul, pow_mul, abs_pow, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) (hR i) k) (abs_nonneg _)

end Laplace.Sampler
