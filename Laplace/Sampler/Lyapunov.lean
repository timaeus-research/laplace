/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# Covariance recursions of linear samplers: Lyapunov laws

The Euler-discretised Langevin chain on a Gaussian target, and SGLD with minibatch
gradient noise on the same target, are linear recursions `x' = A x + ξ` with centred
noise of covariance `N` independent of `x`. Their covariance evolves by the affine map
`X ↦ A X Aᵀ + N` (`covStep`), and the stationary covariance is a fixed point of it: the
discrete Lyapunov equation `X = A X Aᵀ + N`.

This file proves the sampler-side laws of the note *Sanity on Sampling* (project
`sanity`) as finite-dimensional algebra:

* the diagonal Lyapunov equation `X = D X D + N`, `D = diagonal a`, `|a i| < 1`, has the
  unique solution `X i j = N i j / (1 - a i * a j)` (`diagLyapunov`);
* transported through an orthogonal matrix `U` with `A = U (diagonal a) Uᵀ`, this gives
  the unique solution of `X = A X Aᵀ + N` for any real symmetric `A` whose eigenvalues
  lie in `(-1, 1)` (`lyapunovVia`, `symmLyapunov`), with explicit entries in the
  eigenbasis;
* the finite-time identity `X_k - S = A^k (X₀ - S) (Aᵀ)^k` for the iterates from any
  start and any fixed point `S`, hence `X_k = S - A^k S (Aᵀ)^k` from `X₀ = 0` and, for
  symmetric `A` commuting with `S`, `X_k = S (1 - A^(2k))`.

The ULA closed form and the minibatch entry formula are in `Laplace.Sampler.ULA`.
-/

namespace Laplace.Sampler

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- One covariance step of the linear recursion `x' = A x + ξ` with `Cov ξ = N`. -/
def covStep (A N : Matrix ι ι ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ := A * X * Aᵀ + N

/-- Entrywise solution of the diagonal Lyapunov equation `X = (diagonal a) X (diagonal a) + N`. -/
def diagLyapunov (a : ι → ℝ) (N : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => N i j / (1 - a i * a j)

/-- The Lyapunov solution transported through an orthogonal matrix `U`: for
`A = U (diagonal a) Uᵀ` this is the unique solution of `X = A X Aᵀ + N`. -/
def lyapunovVia (U : Matrix ι ι ℝ) (a : ι → ℝ) (N : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  U * diagLyapunov a (Uᵀ * N * U) * Uᵀ

lemma one_sub_mul_pos_of_abs_lt_one {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    0 < 1 - x * y := by
  have h1 : |x * y| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg x) hx hy.le
  have h2 : x * y ≤ |x * y| := le_abs_self _
  linarith


lemma covStep_diagonal_apply (a : ι → ℝ) (N X : Matrix ι ι ℝ) (i j : ι) :
    covStep (diagonal a) N X i j = a i * X i j * a j + N i j := by
  simp only [covStep, diagonal_transpose, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]


/-- The entrywise formula is a fixed point of the diagonal covariance step. -/
theorem diagLyapunov_fixed (a : ι → ℝ) (ha : ∀ i, |a i| < 1) (N : Matrix ι ι ℝ) :
    covStep (diagonal a) N (diagLyapunov a N) = diagLyapunov a N := by
  ext i j
  rw [covStep_diagonal_apply]
  have hpos := one_sub_mul_pos_of_abs_lt_one (ha i) (ha j)
  simp only [diagLyapunov, Matrix.of_apply]
  field_simp
  ring


/-- Uniqueness of the fixed point of the diagonal covariance step. -/
theorem diagLyapunov_unique (a : ι → ℝ) (ha : ∀ i, |a i| < 1) (N X : Matrix ι ι ℝ)
    (hX : covStep (diagonal a) N X = X) : X = diagLyapunov a N := by
  ext i j
  have h := congrFun (congrFun hX i) j
  rw [covStep_diagonal_apply] at h
  have hpos := one_sub_mul_pos_of_abs_lt_one (ha i) (ha j)
  simp only [diagLyapunov, Matrix.of_apply]
  rw [eq_div_iff hpos.ne']
  linear_combination -h


theorem covStep_diagonal_fixed_iff (a : ι → ℝ) (ha : ∀ i, |a i| < 1) (N X : Matrix ι ι ℝ) :
    covStep (diagonal a) N X = X ↔ X = diagLyapunov a N := by
  constructor
  · exact diagLyapunov_unique a ha N X
  · rintro rfl
    exact diagLyapunov_fixed a ha N


/-- Conjugating the covariance step by an orthogonal `U` diagonalising `A`. -/
lemma covStep_conj (U A N X : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1)
    (hA : A = U * diagonal a * Uᵀ) :
    Uᵀ * covStep A N X * U = covStep (diagonal a) (Uᵀ * N * U) (Uᵀ * X * U) := by
  have hcancel : ∀ Z : Matrix ι ι ℝ, Uᵀ * (U * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  subst hA
  simp only [covStep, Matrix.transpose_mul, Matrix.transpose_transpose, diagonal_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hcancel, hU, Matrix.mul_one]


/-- **Symmetric Lyapunov theorem, transported form.** If `U` is orthogonal,
`A = U (diagonal a) Uᵀ` and every `|a i| < 1`, then `X = A X Aᵀ + N` has exactly one
solution, namely `lyapunovVia U a N`. -/
theorem lyapunovVia_fixed_iff (U A N X : Matrix ι ι ℝ) (a : ι → ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hA : A = U * diagonal a * Uᵀ)
    (ha : ∀ i, |a i| < 1) :
    covStep A N X = X ↔ X = lyapunovVia U a N := by
  have hcancel : ∀ Z : Matrix ι ι ℝ, Uᵀ * (U * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hcancel' : ∀ Z : Matrix ι ι ℝ, U * (Uᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  -- conjugation by the orthogonal matrix `U` is a bijection on matrices
  have hconj : ∀ X Y : Matrix ι ι ℝ, Uᵀ * X * U = Uᵀ * Y * U → X = Y := by
    intro X Y hXY
    have := congrArg (fun Z => U * Z * Uᵀ) hXY
    simpa only [Matrix.mul_assoc, hcancel', hU', Matrix.mul_one] using this
  constructor
  · intro hX
    have h1 : covStep (diagonal a) (Uᵀ * N * U) (Uᵀ * X * U) = Uᵀ * X * U := by
      rw [← covStep_conj U A N X a hU hA, hX]
    have h2 := diagLyapunov_unique a ha (Uᵀ * N * U) (Uᵀ * X * U) h1
    apply hconj
    rw [h2, lyapunovVia]
    simp only [Matrix.mul_assoc, hcancel, hU, Matrix.mul_one]
  · rintro rfl
    apply hconj
    rw [covStep_conj U A N _ a hU hA, lyapunovVia]
    simp only [Matrix.mul_assoc, hcancel, hU, Matrix.mul_one]
    simpa only [Matrix.mul_assoc] using diagLyapunov_fixed a ha (Uᵀ * N * U)


/-- Entries of the transported solution in the eigenbasis. -/
theorem lyapunovVia_conj_apply (U : Matrix ι ι ℝ) (a : ι → ℝ) (N : Matrix ι ι ℝ)
    (hU : Uᵀ * U = 1) (i j : ι) :
    (Uᵀ * lyapunovVia U a N * U) i j = (Uᵀ * N * U) i j / (1 - a i * a j) := by
  have hcancel : ∀ Z : Matrix ι ι ℝ, Uᵀ * (U * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [lyapunovVia, Matrix.mul_assoc, hcancel, hU, Matrix.mul_one, diagLyapunov,
    Matrix.of_apply]


/-! ### The real spectral theorem, packaged -/

/-- The orthogonal matrix of eigenvectors of a real symmetric matrix. -/
def orthoOf {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ)

lemma orthoOf_transpose_mul {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (orthoOf hA)ᵀ * orthoOf hA = 1 := by
  have h := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h


lemma orthoOf_mul_transpose {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    orthoOf hA * (orthoOf hA)ᵀ = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff).mp hA.eigenvectorUnitary.2
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h


/-- Real spectral theorem in the form `A = U D Uᵀ`. -/
theorem spectral_real {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A = orthoOf hA * diagonal hA.eigenvalues * (orthoOf hA)ᵀ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hdiag : diagonal (RCLike.ofReal ∘ hA.eigenvalues) = diagonal hA.eigenvalues := by
    congr 1
  rw [hdiag] at h
  exact h


/-- The Lyapunov solution of a real symmetric matrix through its spectral decomposition. -/
def symmLyapunov {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (N : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  lyapunovVia (orthoOf hA) hA.eigenvalues N

/-- **Symmetric Lyapunov theorem.** For real symmetric `A` with eigenvalues in `(-1, 1)`,
`X = A X Aᵀ + N` has the unique solution `symmLyapunov hA N`. -/
theorem symmLyapunov_fixed_iff {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hev : ∀ i, |hA.eigenvalues i| < 1) (N X : Matrix ι ι ℝ) :
    covStep A N X = X ↔ X = symmLyapunov hA N := by
  exact lyapunovVia_fixed_iff (orthoOf hA) A N X hA.eigenvalues (orthoOf_transpose_mul hA)
    (orthoOf_mul_transpose hA) (spectral_real hA) hev


/-! ### Finite-time identities -/

/-- **Finite-time identity.** For any fixed point `S` of the covariance step, the iterates
from `X₀` satisfy `X_k - S = A^k (X₀ - S) (Aᵀ)^k`. -/
theorem covStep_iterate_sub_fixed (A N X₀ S : Matrix ι ι ℝ) (hS : covStep A N S = S) (k : ℕ) :
    (covStep A N)^[k] X₀ - S = A ^ k * (X₀ - S) * (Aᵀ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_succ]
    have hstep : ∀ Y : Matrix ι ι ℝ, covStep A N Y - S = A * (Y - S) * Aᵀ := by
      intro Y
      conv_lhs => rhs; rw [← hS]
      simp only [covStep]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [hstep, ih]
    simp only [Matrix.mul_assoc]


/-- The chain started at zero covariance: `X_k = S - A^k S (Aᵀ)^k`. -/
theorem covStep_iterate_zero (A N S : Matrix ι ι ℝ) (hS : covStep A N S = S) (k : ℕ) :
    (covStep A N)^[k] 0 = S - A ^ k * S * (Aᵀ) ^ k := by
  have h := covStep_iterate_sub_fixed A N 0 S hS k
  rw [zero_sub, Matrix.mul_neg, Matrix.neg_mul, sub_eq_iff_eq_add] at h
  rw [h]
  abel


/-- For symmetric `A` commuting with the fixed point, `X_k = S (1 - A^(2k))`. -/
theorem covStep_iterate_zero_of_comm (A N S : Matrix ι ι ℝ) (hS : covStep A N S = S)
    (hAt : Aᵀ = A) (hcomm : A * S = S * A) (k : ℕ) :
    (covStep A N)^[k] 0 = S * (1 - A ^ (2 * k)) := by
  rw [covStep_iterate_zero A N S hS k, hAt]
  have hc : A ^ k * S = S * A ^ k := ((Commute.pow_left hcomm k))
  rw [Matrix.mul_sub, Matrix.mul_one, hc, Matrix.mul_assoc, ← pow_add, two_mul]


/-- The scalar AR(1) chain `s_{k+1} = ρ² s_k + v` from `s_0 = 0`: `s_k = v/(1-ρ²) (1 - ρ^(2k))`. -/
theorem ar1_var_iterate (ρ v : ℝ) (hρ : |ρ| < 1) (k : ℕ) :
    (fun s : ℝ => ρ ^ 2 * s + v)^[k] 0 = v / (1 - ρ ^ 2) * (1 - ρ ^ (2 * k)) := by
  have hsq : ρ ^ 2 < 1 := by
    have := abs_lt.mp hρ
    nlinarith [abs_nonneg ρ, sq_abs ρ]
  have hne : (1 - ρ ^ 2) ≠ 0 := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    field_simp
    ring


end

end Laplace.Sampler
