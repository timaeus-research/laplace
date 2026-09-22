/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FrobeniusBridge
import Laplace.Multi.OneLoop

/-!
# Reading a covariance along an eigendirection

Two sentences of the note read a covariance matrix along the eigenvectors `uᵢ` of `P = tH`
(eigenvalues `pᵢ`, `κ = p_max/p_min`, `d = |ι|`):

* E7, "along an eigenvector `s` of `P` the corrected variance is `1/p_s + Π_ss/p_s²`":
  `directional_variance_eq` for any `P⁻¹ + P⁻¹ Π P⁻¹`, and `oneLoopCov_directional` for the
  one-loop covariance of `Laplace.Multi.OneLoop`;
* Summary 4, "the whole-covariance Frobenius norm hides this because flat directions dominate it;
  the LLC exposes it because stiff directions dominate `K`": for the eigen-perturbation
  `Σ' = P⁻¹ + U diag(δ) Uᵀ`, `frobenius_rel_eigen_perturb`
  (`‖Σ' − P⁻¹‖_F²/‖P⁻¹‖_F² = ∑ᵢ δᵢ²/∑ᵢ pᵢ⁻²`) and `llc_shift_eigen_perturb`
  (`½ tr(P Σ') − d/2 = ½ ∑ᵢ pᵢ δᵢ`); then
  `stiff_perturbation_hidden` (a perturbation of the stiffest direction:
  `LLC_rel² ≥ (κ/d)² Frob_rel²`) and
  `flat_perturbation_dominates` (of the flattest: `Frob_rel² ≥ d · LLC_rel²`);
* the sharp fixed-spectrum comparison for all-inflation perturbations `δ ≥ 0`
  (`sum_mul_sq_bounds`): `p_min² ∑ δᵢ² ≤ (∑ pᵢ δᵢ)² ≤ (∑ pᵢ²)(∑ δᵢ²)`.

The "LLC" here is the quadratic, centred statistic `½ tr(P Σ)` (the note's `t⟨K⟩` at second
order), which is `d/2` at `Σ = P⁻¹`.
-/

open Matrix Finset

namespace Laplace.Sampler

section Directional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P⁻¹ s = s/p` for an eigenvector `P s = p s` of a positive definite `P`. -/
theorem inv_mulVec_eigen {P : Matrix ι ι ℝ} (hP : P.PosDef) {s : ι → ℝ} {p : ℝ} (hp : p ≠ 0)
    (hs : P *ᵥ s = p • s) : P⁻¹ *ᵥ s = p⁻¹ • s := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  calc P⁻¹ *ᵥ s = p⁻¹ • (P⁻¹ *ᵥ (P *ᵥ s)) := by
        rw [hs, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hp, one_smul]
    _ = p⁻¹ • s := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

/-- `s P⁻¹ = s/p` as a row vector, by symmetry of `P⁻¹`. -/
theorem vecMul_inv_eigen {P : Matrix ι ι ℝ} (hP : P.PosDef) {s : ι → ℝ} {p : ℝ} (hp : p ≠ 0)
    (hs : P *ᵥ s = p • s) : s ᵥ* P⁻¹ = p⁻¹ • s := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv, hPt, inv_mulVec_eigen hP hp hs]

/-- **E7's directional reading**: along an eigenvector `s` of `P` (`P s = p s`), the quadratic form
of `P⁻¹ + P⁻¹ Π P⁻¹` is `(s·s)/p + (sᵀ Π s)/p²`; no symmetry of `Π` is needed. -/
theorem directional_variance_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) {s : ι → ℝ} {p : ℝ} (hp : p ≠ 0)
    (hs : P *ᵥ s = p • s) (M : Matrix ι ι ℝ) :
    s ⬝ᵥ ((P⁻¹ + P⁻¹ * M * P⁻¹) *ᵥ s) = (s ⬝ᵥ s) / p + (s ⬝ᵥ (M *ᵥ s)) / p ^ 2 := by
  have h1 := inv_mulVec_eigen hP hp hs
  have h2 := vecMul_inv_eigen hP hp hs
  have h3 : s ⬝ᵥ (P⁻¹ *ᵥ (M *ᵥ s)) = p⁻¹ * (s ⬝ᵥ (M *ᵥ s)) := by
    rw [Matrix.dotProduct_mulVec, h2, smul_dotProduct, smul_eq_mul]
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
    Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, h3, smul_eq_mul,
    smul_eq_mul]
  ring

end Directional

section OneLoop

variable {d : ℕ}

/-- The eigenvector columns of `orthoOf` have unit Euclidean length. -/
theorem orthoCol_dotProduct_self {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsHermitian) (i : Fin d) :
    (orthoCol hQ i).ofLp ⬝ᵥ (orthoCol hQ i).ofLp = 1 := by
  have h := congrFun (congrFun (orthoOf_transpose_mul hQ) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simpa [orthoCol, dotProduct, transpose_apply] using h

/-- **E7, "one direction needs only `Π_ss`"**: along the `i`-th eigenvector of `P = tH`, the
one-loop variance is `1/pᵢ + (uᵢᵀ Π uᵢ)/pᵢ²` with `Π = oneLoopPi t T Q (tH)⁻¹`. -/
theorem oneLoopCov_directional {t : ℝ} {H : Matrix (Fin d) (Fin d) ℝ} (hP : (t • H).PosDef)
    (T : Fin d → Fin d → Fin d → ℝ) (Q : Fin d → Fin d → Fin d → Fin d → ℝ) (i : Fin d) :
    (orthoCol hP.1 i).ofLp ⬝ᵥ (Laplace.Multi.oneLoopCov t H T Q *ᵥ (orthoCol hP.1 i).ofLp) =
      1 / hP.1.eigenvalues i +
        ((orthoCol hP.1 i).ofLp ⬝ᵥ
          (Laplace.Multi.oneLoopPi t T Q (t • H)⁻¹ *ᵥ (orthoCol hP.1 i).ofLp)) /
          hP.1.eigenvalues i ^ 2 := by
  rw [Laplace.Multi.oneLoopCov, directional_variance_eq hP (hP.eigenvalues_pos i).ne'
    (mulVec_orthoCol hP.1 i), orthoCol_dotProduct_self hP.1 i]

end OneLoop

/-! ### Frobenius hides, the LLC exposes -/

section Perturbation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The eigen-perturbation law for the Frobenius error**: for `Σ' = P⁻¹ + U diag(δ) Uᵀ`,
`‖Σ' − P⁻¹‖_F² / ‖P⁻¹‖_F² = ∑ᵢ δᵢ² / ∑ᵢ (1/pᵢ)²`. -/
theorem frobenius_rel_eigen_perturb {P : Matrix ι ι ℝ} (hP : P.PosDef) (δ : ι → ℝ) :
    (∑ a, ∑ a', ((P⁻¹ + orthoOf hP.1 * diagonal δ * (orthoOf hP.1)ᵀ) a a' - P⁻¹ a a') ^ 2) /
        ∑ a, ∑ a', (P⁻¹) a a' ^ 2 =
      (∑ i, δ i ^ 2) / ∑ i, (1 / hP.1.eigenvalues i) ^ 2 := by
  rw [frobenius_inv hP]
  congr 1
  simp only [Matrix.add_apply, add_sub_cancel_left]
  have hc := sum_sq_conj (diagonal δ) (orthoOf hP.1)ᵀ
    (by rw [transpose_transpose]; exact orthoOf_transpose_mul hP.1)
  rw [transpose_transpose] at hc
  rw [hc, sum_sq_diagonal]

/-- **The eigen-perturbation law for the LLC statistic**: `½ tr(P Σ') − d/2 = ½ ∑ᵢ pᵢ δᵢ`. -/
theorem llc_shift_eigen_perturb {P : Matrix ι ι ℝ} (hP : P.PosDef) (δ : ι → ℝ) :
    1 / 2 * (P * (P⁻¹ + orthoOf hP.1 * diagonal δ * (orthoOf hP.1)ᵀ)).trace -
        (Fintype.card ι : ℝ) / 2 =
      1 / 2 * ∑ i, hP.1.eigenvalues i * δ i := by
  have hunit : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne')
  have htr : (P * (orthoOf hP.1 * diagonal δ * (orthoOf hP.1)ᵀ)).trace =
      ∑ i, hP.1.eigenvalues i * δ i := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
      orthoOf_transpose_mul_mul hP.1, diagonal_mul_diagonal, trace_diagonal]
  rw [Matrix.mul_add, Matrix.trace_add, hunit, Matrix.trace_one, htr]
  ring

omit [DecidableEq ι] in
/-- `∑ᵢ (1/pᵢ)² ≥ 1/p_min²` when `p_min` is attained. -/
theorem sum_inv_sq_ge {p : ι → ℝ} {pmin : ℝ} (i₀ : ι) (hi₀ : p i₀ = pmin) :
    (1 / pmin) ^ 2 ≤ ∑ i, (1 / p i) ^ 2 := by
  have := Finset.single_le_sum (f := fun i => (1 / p i) ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ i₀)
  simpa [hi₀] using this

omit [DecidableEq ι] in
/-- `∑ᵢ (1/pᵢ)² ≤ d/p_min²`. -/
theorem sum_inv_sq_le {p : ι → ℝ} {pmin : ℝ} (hpmin : 0 < pmin) (hmin : ∀ i, pmin ≤ p i) :
    ∑ i, (1 / p i) ^ 2 ≤ (Fintype.card ι : ℝ) * (1 / pmin) ^ 2 := by
  have : ∀ i, (1 / p i) ^ 2 ≤ (1 / pmin) ^ 2 := fun i =>
    pow_le_pow_left₀ (one_div_pos.mpr (lt_of_lt_of_le hpmin (hmin i))).le
      (one_div_le_one_div_of_le hpmin (hmin i)) 2
  calc ∑ i, (1 / p i) ^ 2 ≤ ∑ _i : ι, (1 / pmin) ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = (Fintype.card ι : ℝ) * (1 / pmin) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_sq_single (i₀ : ι) (a : ℝ) : ∑ i, ((Pi.single i₀ a : ι → ℝ) i) ^ 2 = a ^ 2 := by
  rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem sum_mul_single (p : ι → ℝ) (i₀ : ι) (a : ℝ) :
    ∑ i, p i * (Pi.single i₀ a : ι → ℝ) i = p i₀ * a := by
  rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **A stiff-direction error is hidden by the Frobenius norm and exposed by the LLC.** For the
perturbation `δ = a` along the eigenvector of `p_max` (zero elsewhere): the relative squared
Frobenius error is at most `(a p_min)²`, the relative LLC shift is `a p_max / d`, so
`LLC_rel² ≥ (κ/d)² · Frob_rel²` with `κ = p_max/p_min`. -/
theorem stiff_perturbation_hidden {p : ι → ℝ} {pmin pmax : ℝ} (hpmin : 0 < pmin) (imin : ι)
    (himin : p imin = pmin) (imax : ι) (himax : p imax = pmax) (a : ℝ) :
    (∑ i, ((Pi.single imax a : ι → ℝ) i) ^ 2) / ∑ i, (1 / p i) ^ 2 ≤ (a * pmin) ^ 2 ∧
      (1 / 2 * ∑ i, p i * (Pi.single imax a : ι → ℝ) i) / ((Fintype.card ι : ℝ) / 2) =
        a * pmax / Fintype.card ι ∧
      (pmax / pmin / Fintype.card ι) ^ 2 *
          ((∑ i, ((Pi.single imax a : ι → ℝ) i) ^ 2) / ∑ i, (1 / p i) ^ 2) ≤
        ((1 / 2 * ∑ i, p i * (Pi.single imax a : ι → ℝ) i) /
          ((Fintype.card ι : ℝ) / 2)) ^ 2 := by
  have hD := sum_inv_sq_ge imin himin
  have hDpos : 0 < ∑ i, (1 / p i) ^ 2 := lt_of_lt_of_le (by positivity) hD
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨imin⟩
  rw [sum_sq_single, sum_mul_single, himax]
  have hF : a ^ 2 / ∑ i, (1 / p i) ^ 2 ≤ (a * pmin) ^ 2 := by
    calc a ^ 2 / ∑ i, (1 / p i) ^ 2 ≤ a ^ 2 / (1 / pmin) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hD
      _ = (a * pmin) ^ 2 := by field_simp
  have hL : (1 / 2 * (pmax * a)) / ((Fintype.card ι : ℝ) / 2) = a * pmax / Fintype.card ι := by
    field_simp
  refine ⟨hF, hL, ?_⟩
  rw [hL]
  calc (pmax / pmin / Fintype.card ι) ^ 2 * (a ^ 2 / ∑ i, (1 / p i) ^ 2)
      ≤ (pmax / pmin / Fintype.card ι) ^ 2 * (a * pmin) ^ 2 :=
        mul_le_mul_of_nonneg_left hF (sq_nonneg _)
    _ = (a * pmax / Fintype.card ι) ^ 2 := by field_simp

/-- **A flat-direction error dominates the Frobenius norm.** For the perturbation `δ = a` along
the eigenvector of `p_min`: `Frob_rel² ≥ (a p_min)²/d = d · LLC_rel²`. -/
theorem flat_perturbation_dominates {p : ι → ℝ} {pmin : ℝ} (hpmin : 0 < pmin)
    (hmin : ∀ i, pmin ≤ p i) (imin : ι) (himin : p imin = pmin) (a : ℝ) :
    (Fintype.card ι : ℝ) *
        ((1 / 2 * ∑ i, p i * (Pi.single imin a : ι → ℝ) i) / ((Fintype.card ι : ℝ) / 2)) ^ 2 ≤
      (∑ i, ((Pi.single imin a : ι → ℝ) i) ^ 2) / ∑ i, (1 / p i) ^ 2 := by
  have hD := sum_inv_sq_le hpmin hmin
  have hDpos : 0 < ∑ i, (1 / p i) ^ 2 :=
    lt_of_lt_of_le (by positivity) (sum_inv_sq_ge imin himin)
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨imin⟩
  rw [sum_sq_single, sum_mul_single, himin]
  have hL : (1 / 2 * (pmin * a)) / ((Fintype.card ι : ℝ) / 2) = a * pmin / Fintype.card ι := by
    field_simp
  rw [hL]
  calc (Fintype.card ι : ℝ) * (a * pmin / Fintype.card ι) ^ 2
      = a ^ 2 / ((Fintype.card ι : ℝ) * (1 / pmin) ^ 2) := by field_simp
    _ ≤ a ^ 2 / ∑ i, (1 / p i) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hDpos hD

omit [DecidableEq ι] in
/-- **The sharp fixed-spectrum comparison** for all-inflation perturbations `δ ≥ 0`:
`p_min² ∑ᵢ δᵢ² ≤ (∑ᵢ pᵢ δᵢ)² ≤ (∑ᵢ pᵢ²)(∑ᵢ δᵢ²)`. -/
theorem sum_mul_sq_bounds {p δ : ι → ℝ} {pmin : ℝ} (hpmin : 0 ≤ pmin) (hmin : ∀ i, pmin ≤ p i)
    (hδ : ∀ i, 0 ≤ δ i) :
    pmin ^ 2 * ∑ i, δ i ^ 2 ≤ (∑ i, p i * δ i) ^ 2 ∧
      (∑ i, p i * δ i) ^ 2 ≤ (∑ i, p i ^ 2) * ∑ i, δ i ^ 2 := by
  refine ⟨?_, Finset.sum_mul_sq_le_sq_mul_sq _ _ _⟩
  have h1 : pmin * ∑ i, δ i ≤ ∑ i, p i * δ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (hδ i)
  have h2 : ∑ i, δ i ^ 2 ≤ (∑ i, δ i) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hδ i
  have h0 : 0 ≤ pmin * ∑ i, δ i := mul_nonneg hpmin (Finset.sum_nonneg fun i _ => hδ i)
  calc pmin ^ 2 * ∑ i, δ i ^ 2 ≤ pmin ^ 2 * (∑ i, δ i) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (pmin * ∑ i, δ i) ^ 2 := by ring
    _ ≤ (∑ i, p i * δ i) ^ 2 := pow_le_pow_left₀ h0 h1 2

end Perturbation

end Laplace.Sampler
