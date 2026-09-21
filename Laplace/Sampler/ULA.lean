/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.Lyapunov

/-!
# The ULA law and the minibatch law

For the Gaussian target with precision `P` (symmetric positive definite) the
Euler-discretised Langevin step with step size `h` is `x' = (1 - h P) x + √(2h) ξ`, so
`A = 1 - h P` and `N = 2h • 1`. With minibatch gradients of noise covariance `C` the
injected noise becomes `N = 2h • 1 + (h² t²) • C`.

* `ulaCov P h = (P - (h/2) P²)⁻¹` is a fixed point of the ULA covariance step (pure
  algebra: it commutes with `P`), and under `0 < h p_i < 2` it is the unique one and is
  positive definite, with eigenbasis entries `1 / (p_i (1 - h p_i / 2))` (the "ULA law").
* With minibatch noise, in the eigenbasis of `P` the stationary covariance has entries
  `(2h δ_ij + h² t² C̃_ij) / (h (p_i + p_j) - h² p_i p_j)`; on the diagonal this is
  `(1 + h t² C̃_ii / 2) / (p_i (1 - h p_i / 2))`, for any `C` (no commutation needed).
-/

namespace Laplace.Sampler

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- The ULA step matrix `A = 1 - h P`. -/
def ulaStep (P : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ := 1 - h • P

/-- The Langevin noise covariance `2h • 1`. -/
def ulaNoise (h : ℝ) : Matrix ι ι ℝ := (2 * h) • (1 : Matrix ι ι ℝ)

/-- Noise covariance with minibatch gradient noise `C`: `2h • 1 + h² t² • C`. -/
def minibatchNoise (h t : ℝ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (2 * h) • (1 : Matrix ι ι ℝ) + (h ^ 2 * t ^ 2) • C

/-- The ULA stationary covariance `(P - (h/2) P²)⁻¹ = P⁻¹ (1 - (h/2) P)⁻¹`. -/
def ulaCov (P : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ := (P - (h / 2) • (P * P))⁻¹

/-- `1 - A² = 2h P (1 - (h/2) P)` for `A = 1 - h P`. -/
lemma one_sub_ulaStep_sq (P : Matrix ι ι ℝ) (h : ℝ) :
    1 - ulaStep P h * ulaStep P h = (2 * h) • (P - (h / 2) • (P * P)) := by
  simp only [ulaStep, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
  module


lemma ulaCov_commute (P : Matrix ι ι ℝ) (h : ℝ) (hdet : IsUnit (P - (h / 2) • (P * P)).det) :
    P * ulaCov P h = ulaCov P h * P := by
  set M := P - (h / 2) • (P * P) with hM
  have hMP : M * P = P * M := by
    simp only [hM, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc]
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have h2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  change P * M⁻¹ = M⁻¹ * P
  calc P * M⁻¹ = (M⁻¹ * M) * P * M⁻¹ := by rw [h1, Matrix.one_mul]
    _ = M⁻¹ * (M * P) * M⁻¹ := by simp only [Matrix.mul_assoc]
    _ = M⁻¹ * (P * M) * M⁻¹ := by rw [hMP]
    _ = M⁻¹ * P * (M * M⁻¹) := by simp only [Matrix.mul_assoc]
    _ = M⁻¹ * P := by rw [h2, Matrix.mul_one]


/-- **ULA fixed point (algebraic form).** Whenever `P - (h/2) P²` is invertible,
`ulaCov P h` solves `X = A X Aᵀ + 2h • 1` for symmetric `P`. -/
theorem ulaCov_fixed (P : Matrix ι ι ℝ) (h : ℝ) (hP : Pᵀ = P)
    (hdet : IsUnit (P - (h / 2) • (P * P)).det) :
    covStep (ulaStep P h) (ulaNoise h) (ulaCov P h) = ulaCov P h := by
  have hAt : (ulaStep P h)ᵀ = ulaStep P h := by
    simp [ulaStep, Matrix.transpose_sub, Matrix.transpose_smul, hP]
  have hcomm : ulaStep P h * ulaCov P h = ulaCov P h * ulaStep P h := by
    simp only [ulaStep, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, ulaCov_commute P h hdet]
  have hkey : (1 - ulaStep P h * ulaStep P h) * ulaCov P h = ulaNoise h := by
    rw [one_sub_ulaStep_sq, Matrix.smul_mul]
    change (2 * h) • ((P - (h / 2) • (P * P)) * (P - (h / 2) • (P * P))⁻¹)
      = (2 * h) • (1 : Matrix ι ι ℝ)
    rw [Matrix.mul_nonsing_inv _ hdet]
  have hsplit : ulaStep P h * ulaStep P h * ulaCov P h
      = ulaCov P h - (1 - ulaStep P h * ulaStep P h) * ulaCov P h := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  unfold covStep
  rw [hAt, Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hsplit, hkey]
  abel


/-- The ULA step matrix in the eigenbasis of `P`. -/
lemma ulaStep_eq_conj {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) :
    ulaStep P h = orthoOf hP * diagonal (fun i => 1 - h * hP.eigenvalues i) * (orthoOf hP)ᵀ := by
  have hU' := orthoOf_mul_transpose hP
  have hspec := spectral_real hP
  have hdiag : diagonal (fun i => 1 - h * hP.eigenvalues i)
      = 1 - h • diagonal hP.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU', Matrix.mul_smul,
    Matrix.smul_mul, ← hspec]
  rfl


lemma abs_one_sub_mul_lt_one {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hhp : h * p < 2) :
    |1 - h * p| < 1 := by
  have hhp : 0 < h * p := mul_pos hh hp
  rw [abs_lt]
  constructor <;> linarith


/-- **Uniqueness of the ULA law.** Under `0 < h p_i < 2` for every eigenvalue `p_i` of the
symmetric matrix `P`, the ULA covariance step has exactly one fixed point. -/
theorem ula_fixed_iff {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) (X : Matrix ι ι ℝ) :
    covStep (ulaStep P h) (ulaNoise h) X = X ↔
      X = lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i) (ulaNoise h) := by
  exact lyapunovVia_fixed_iff (orthoOf hP) (ulaStep P h) (ulaNoise h) X _
    (orthoOf_transpose_mul hP) (orthoOf_mul_transpose hP) (ulaStep_eq_conj hP h)
    (fun i => abs_one_sub_mul_lt_one hh (hev i).1 (hev i).2)


/-- `P - (h/2) P²` is invertible under the stability condition. -/
lemma isUnit_det_ulaDenom {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) :
    IsUnit (P - (h / 2) • (P * P)).det := by
  have hfac : P - (h / 2) • (P * P) = P * ulaStep P (h / 2) := by
    simp only [ulaStep, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  have hdetU : (orthoOf hP).det * (orthoOf hP)ᵀ.det = 1 := by
    rw [← Matrix.det_mul, orthoOf_mul_transpose hP, Matrix.det_one]
  have hdetU' : (orthoOf hP).det ≠ 0 := fun h0 => by simp [h0] at hdetU
  have hdetUt : (orthoOf hP)ᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hdetU'
  have hpos1 : ∏ i, hP.eigenvalues i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hev i).1.ne'
  have hpos2 : ∏ i, (1 - h / 2 * hP.eigenvalues i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by have := (hev i).2; linarith
  rw [hfac, Matrix.det_mul, ulaStep_eq_conj hP (h / 2), Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, hP.det_eq_prod_eigenvalues, isUnit_iff_ne_zero]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact mul_ne_zero hpos1 (mul_ne_zero (mul_ne_zero hdetU' hpos2) hdetUt)


/-- **The ULA law.** The closed form `(P - (h/2) P²)⁻¹` is the stationary covariance. -/
theorem ulaCov_eq_lyapunov {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) :
    ulaCov P h = lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i) (ulaNoise h) := by
  have hPt : Pᵀ = P := by
    have := hP.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact (ula_fixed_iff hP h hh hev _).mp (ulaCov_fixed P h hPt (isUnit_det_ulaDenom hP h hev))


/-- Eigenbasis entries of the ULA law: `1 / (p_i (1 - h p_i / 2))` on the diagonal, zero off it. -/
theorem ulaCov_conj_apply {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) (i j : ι) :
    ((orthoOf hP)ᵀ * ulaCov P h * orthoOf hP) i j =
      if i = j then 1 / (hP.eigenvalues i * (1 - h * hP.eigenvalues i / 2)) else 0 := by
  rw [ulaCov_eq_lyapunov hP h hh hev, lyapunovVia_conj_apply _ _ _ (orthoOf_transpose_mul hP)]
  simp only [ulaNoise, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, orthoOf_transpose_mul hP,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have hp := (hev i).1
    have hhp := (hev i).2
    have hne : hP.eigenvalues i * (1 - h * hP.eigenvalues i / 2) ≠ 0 :=
      mul_ne_zero hp.ne' (by linarith)
    have hne2 : 1 - (1 - h * hP.eigenvalues i) * (1 - h * hP.eigenvalues i) ≠ 0 := by
      nlinarith [mul_pos hh hp]
    simp only [if_true]
    rw [div_eq_div_iff hne2 hne]
    ring
  · simp [hij]


/-- The ULA law is positive definite. -/
theorem ulaCov_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) : (ulaCov P h).PosDef := by
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  rw [ulaCov_eq_lyapunov hP.1 h hh hev']
  have hU := orthoOf_transpose_mul hP.1
  have hU' := orthoOf_mul_transpose hP.1
  -- the transported solution is `U Y Uᵀ` with `Y` diagonal with positive entries
  have hY : diagLyapunov (fun i => 1 - h * hP.1.eigenvalues i)
      ((orthoOf hP.1)ᵀ * ulaNoise h * orthoOf hP.1)
      = diagonal (fun i =>
          2 * h / (1 - (1 - h * hP.1.eigenvalues i) * (1 - h * hP.1.eigenvalues i))) := by
    ext i j
    simp only [diagLyapunov, ulaNoise, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU,
      Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; rw [mul_one]
    · simp
  have hYpos : (diagonal (fun i => 2 * h /
      (1 - (1 - h * hP.1.eigenvalues i) * (1 - h * hP.1.eigenvalues i)))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    have hp := (hev' i).1
    have hhp := (hev' i).2
    have hne2 : 0 < 1 - (1 - h * hP.1.eigenvalues i) * (1 - h * hP.1.eigenvalues i) := by
      nlinarith [mul_pos hh hp]
    positivity
  have hinj : Function.Injective (orthoOf hP.1)ᵀ.mulVec := by
    intro x y hxy
    have := congrArg (orthoOf hP.1).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hU'] using this
  have := Matrix.PosDef.conjTranspose_mul_mul_same hYpos hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this
  unfold lyapunovVia
  rw [hY]
  exact this


/-! ### Minibatch noise -/

/-- **Minibatch law, entry formula.** In the eigenbasis of `P`, with `C̃ = Uᵀ C U`, the
stationary covariance of SGLD with noise `2h • 1 + h² t² • C` has entries
`(2h δ_ij + h² t² C̃_ij) / (h (p_i + p_j) - h² p_i p_j)`. -/
theorem minibatchCov_conj_apply {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h t : ℝ)
    (C : Matrix ι ι ℝ) (i j : ι) :
    ((orthoOf hP)ᵀ * lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i)
        (minibatchNoise h t C) * orthoOf hP) i j =
      ((2 * h) * (if i = j then 1 else 0) + h ^ 2 * t ^ 2 * ((orthoOf hP)ᵀ * C * orthoOf hP) i j) /
        (h * (hP.eigenvalues i + hP.eigenvalues j)
          - h ^ 2 * hP.eigenvalues i * hP.eigenvalues j) := by
  rw [lyapunovVia_conj_apply _ _ _ (orthoOf_transpose_mul hP)]
  have hU := orthoOf_transpose_mul hP
  simp only [minibatchNoise, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  congr 1; ring


/-- The diagonal of the minibatch law: the ULA variance times `1 + h t² C̃_ii / 2`. -/
theorem minibatchCov_conj_diag {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h t : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) (C : Matrix ι ι ℝ) (i : ι) :
    ((orthoOf hP)ᵀ * lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i)
        (minibatchNoise h t C) * orthoOf hP) i i =
      (1 + h * t ^ 2 * ((orthoOf hP)ᵀ * C * orthoOf hP) i i / 2) /
        (hP.eigenvalues i * (1 - h * hP.eigenvalues i / 2)) := by
  rw [minibatchCov_conj_apply hP h t C i i]
  have hp := (hev i).1
  have hhp := (hev i).2
  have hne : hP.eigenvalues i * (1 - h * hP.eigenvalues i / 2) ≠ 0 :=
    mul_ne_zero hp.ne' (by linarith)
  have hne2 : h * (hP.eigenvalues i + hP.eigenvalues i)
      - h ^ 2 * hP.eigenvalues i * hP.eigenvalues i ≠ 0 := by
    nlinarith [mul_pos hh hp]
  simp only [if_true]
  rw [div_eq_div_iff hne2 hne]
  ring


/-- The minibatch stationary covariance is the unique fixed point of its covariance step. -/
theorem minibatch_fixed_iff {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h t : ℝ) (hh : 0 < h)
    (hev : ∀ i, 0 < hP.eigenvalues i ∧ h * hP.eigenvalues i < 2) (C X : Matrix ι ι ℝ) :
    covStep (ulaStep P h) (minibatchNoise h t C) X = X ↔
      X = lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i) (minibatchNoise h t C) := by
  exact lyapunovVia_fixed_iff (orthoOf hP) (ulaStep P h) (minibatchNoise h t C) X _
    (orthoOf_transpose_mul hP) (orthoOf_mul_transpose hP) (ulaStep_eq_conj hP h)
    (fun i => abs_one_sub_mul_lt_one hh (hev i).1 (hev i).2)


end

end Laplace.Sampler
