/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ULAAutocovariance
import Laplace.Multi.MinibatchBudget

/-!
# Positivity of the Lyapunov covariance and the minibatch fluctuation of the LLC statistic (E8)

The entrywise Lyapunov solution `diagLyapunov a N = (Nᵢⱼ/(1 − aᵢaⱼ))` is the geometric series of
the covariance step:
**`x ⬝ᵥ diagLyapunov a N x = ∑'_{r≥0} (aʳ∘x) ⬝ᵥ N (aʳ∘x)`** (`diagLyapunov_quadForm_eq_tsum`), so
it preserves positive
semidefiniteness and definiteness and dominates its source, `diagLyapunov a N − N ⪰ 0`
(`diagLyapunov_sub_posSemidef`,
`diagLyapunov_posSemidef`, `diagLyapunov_posDef`); transported through an orthogonal frame the same
holds for
`lyapunovVia U a N` (`lyapunovVia_posSemidef`, `lyapunovVia_posDef`). With `minibatchNoise h t C =
2h·1 + h²t²C ≻ 0`
(`minibatchNoise_posDef`) the minibatch stationary covariance `Σ^{mb}` is positive definite
(`minibatchCov_posDef_frame`), and
by linearity `Σ^{mb} − Σ^{ULA} = lyapunovVia U ρ (h²t²C) ⪰ 0` (`minibatchCov_sub_ulaCov`,
`minibatchCov_sub_ulaCov_posSemidef`).

Under the stationary law `N(m, Σ^{mb})` the energy `½uᵀHu` has variance
**`Var = ½∑ᵢⱼλᵢλⱼΣ̂ᵢⱼ² + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼΣ̂ᵢⱼ`** (`minibatchVar_frame`), `Σ̂ = UᵀΣ^{mb}U`, `m̂ = Uᵀm`,
with the frame entries
`Σ̂ᵢⱼ = σᵢ²[i=j] + Eᵢⱼ`, `Eᵢⱼ = h²t²Ĉᵢⱼ/(1 − ρᵢρⱼ)` (`minibatchCov_frame_split`): unlike the mean
(tide 101), the variance sees
the off-diagonal gradient-noise covariance. The excess over the ULA variance is
**`∑ᵢλᵢ²σᵢ²Eᵢᵢ + ½∑ᵢⱼλᵢλⱼEᵢⱼ² + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼEᵢⱼ`** (`minibatchVar_sub_ulaVar`) with `Eᵢᵢ =
(ht²/2)Ĉᵢᵢσᵢ²`
(`minibatchCov_frame_split_diag`): to first order in `C` the centred variance inflates by
`2·(ht²/2)Ĉᵢᵢ` per mode — twice
the relative increment of the mean — the off-diagonal entries entering quadratically (and linearly
through the mean term
when `m ≠ 0`).
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Lyapunov solution as a geometric series -/

section Lyapunov

variable {a : ι → ℝ} {N : Matrix ι ι ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem abs_mul_lt_one_of_abs_lt_one {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) : |x * y| < 1 := by
  rw [abs_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg x) hx hy.le

omit [Fintype ι] [DecidableEq ι] in
theorem diagLyapunov_isHermitian (a : ι → ℝ) (hN : N.IsHermitian) :
    (diagLyapunov a N).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  have := hN.apply i j
  rw [star_trivial] at this
  simp only [Matrix.transpose_apply, diagLyapunov, Matrix.of_apply, this, mul_comm (a j) (a i)]

omit [DecidableEq ι] in
/-- The quadratic form of `diag(a)ʳ x` against `N`, as a double sum. -/
theorem quadForm_pow_eq_sum (a : ι → ℝ) (N : Matrix ι ι ℝ) (x : ι → ℝ) (r : ℕ) :
    (fun i => a i ^ r * x i) ⬝ᵥ N *ᵥ (fun i => a i ^ r * x i) =
      ∑ i, ∑ j, x i * (N i j * (a i * a j) ^ r * x j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype ι] [DecidableEq ι] in
theorem summable_quadForm_pow (ha : ∀ i, |a i| < 1) (N : Matrix ι ι ℝ) (x : ι → ℝ) (i j : ι) :
    Summable (fun r : ℕ => x i * (N i j * (a i * a j) ^ r * x j)) :=
  (((summable_geometric_of_abs_lt_one (abs_mul_lt_one_of_abs_lt_one (ha i) (ha j))).mul_left
    (N i j)).mul_right (x j)).mul_left (x i)

omit [DecidableEq ι] in
/-- **The Lyapunov solution is the geometric series of the covariance step**:
`x ⬝ᵥ diagLyapunov a N x = ∑'ᵣ (aʳ∘x) ⬝ᵥ N (aʳ∘x)`. -/
theorem diagLyapunov_quadForm_eq_tsum (ha : ∀ i, |a i| < 1) (N : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ diagLyapunov a N *ᵥ x =
      ∑' r : ℕ, (fun i => a i ^ r * x i) ⬝ᵥ N *ᵥ (fun i => a i ^ r * x i) := by
  have e1 : ∀ i j, x i * (N i j / (1 - a i * a j) * x j) =
      ∑' r : ℕ, x i * (N i j * (a i * a j) ^ r * x j) := by
    intro i j
    rw [tsum_mul_left, tsum_mul_right, tsum_mul_left,
      tsum_geometric_of_abs_lt_one (abs_mul_lt_one_of_abs_lt_one (ha i) (ha j)), div_eq_mul_inv]
  have e2 : x ⬝ᵥ diagLyapunov a N *ᵥ x =
      ∑ i, ∑ j, ∑' r : ℕ, x i * (N i j * (a i * a j) ^ r * x j) := by
    simp only [dotProduct, Matrix.mulVec, diagLyapunov, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j
  have h1 : ∀ i, ∑ j, ∑' r : ℕ, x i * (N i j * (a i * a j) ^ r * x j) =
      ∑' r : ℕ, ∑ j, x i * (N i j * (a i * a j) ^ r * x j) := fun i =>
    (Summable.tsum_finsetSum fun j _ => summable_quadForm_pow ha N x i j).symm
  have h2 : ∑ i, ∑' r : ℕ, ∑ j, x i * (N i j * (a i * a j) ^ r * x j) =
      ∑' r : ℕ, ∑ i, ∑ j, x i * (N i j * (a i * a j) ^ r * x j) :=
    (Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => summable_quadForm_pow ha N x i
        j).symm
  rw [e2]
  simp_rw [h1]
  rw [h2]
  exact tsum_congr fun r => (quadForm_pow_eq_sum a N x r).symm

omit [DecidableEq ι] in
theorem summable_quadForm_pow_total (ha : ∀ i, |a i| < 1) (N : Matrix ι ι ℝ) (x : ι → ℝ) :
    Summable (fun r : ℕ => (fun i => a i ^ r * x i) ⬝ᵥ N *ᵥ (fun i => a i ^ r * x i)) := by
  simp_rw [quadForm_pow_eq_sum]
  exact summable_sum fun i _ => summable_sum fun j _ => summable_quadForm_pow ha N x i j

omit [DecidableEq ι] in
/-- `x ⬝ᵥ diagLyapunov a N x ≥ x ⬝ᵥ N x` for `N ⪰ 0`: the `r = 0` term of the series. -/
theorem quadForm_le_diagLyapunov_quadForm (ha : ∀ i, |a i| < 1) (hN : N.PosSemidef) (x : ι → ℝ) :
    x ⬝ᵥ N *ᵥ x ≤ x ⬝ᵥ diagLyapunov a N *ᵥ x := by
  rw [diagLyapunov_quadForm_eq_tsum ha N x]
  have h0 : (fun i => a i ^ 0 * x i) ⬝ᵥ N *ᵥ (fun i => a i ^ 0 * x i) = x ⬝ᵥ N *ᵥ x := by
    simp only [pow_zero, one_mul]
  rw [← h0]
  exact (summable_quadForm_pow_total ha N x).le_tsum 0 fun r _ => by
    have := hN.dotProduct_mulVec_nonneg (fun i => a i ^ r * x i)
    rwa [star_trivial] at this

omit [Fintype ι] [DecidableEq ι] in
/-- **`diagLyapunov a N − N ⪰ 0`** for `N ⪰ 0`. -/
theorem diagLyapunov_sub_posSemidef [Finite ι] (ha : ∀ i, |a i| < 1) (hN : N.PosSemidef) :
    (diagLyapunov a N - N).PosSemidef := by
  cases nonempty_fintype ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((diagLyapunov_isHermitian a hN.1).sub hN.1)
    fun x => ?_
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
  exact quadForm_le_diagLyapunov_quadForm ha hN x

omit [Fintype ι] [DecidableEq ι] in
theorem diagLyapunov_posSemidef [Finite ι] (ha : ∀ i, |a i| < 1) (hN : N.PosSemidef) :
    (diagLyapunov a N).PosSemidef := by
  cases nonempty_fintype ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (diagLyapunov_isHermitian a hN.1) fun x => ?_
  rw [star_trivial]
  have := hN.dotProduct_mulVec_nonneg x
  rw [star_trivial] at this
  exact this.trans (quadForm_le_diagLyapunov_quadForm ha hN x)

omit [Fintype ι] [DecidableEq ι] in
theorem diagLyapunov_posDef [Finite ι] (ha : ∀ i, |a i| < 1) (hN : N.PosDef) :
    (diagLyapunov a N).PosDef := by
  cases nonempty_fintype ι
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (diagLyapunov_isHermitian a hN.1) fun x hx => ?_
  rw [star_trivial]
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 hN).2 hx
  rw [star_trivial] at this
  exact this.trans_le (quadForm_le_diagLyapunov_quadForm ha hN.posSemidef x)

end Lyapunov

/-! ### Transport through an orthogonal frame -/

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

theorem mulVec_injective_of_transpose_mul (hU : Uᵀ * U = 1) : Function.Injective U.mulVec :=
  mulVec_injective_of_isUnit (isUnit_iff_exists.2 ⟨Uᵀ, mul_transpose_eq_one_of hU, hU⟩)

omit [DecidableEq ι] in
theorem lyapunovVia_posSemidef {a : ι → ℝ} (ha : ∀ i, |a i| < 1)
    {N : Matrix ι ι ℝ} (hN : N.PosSemidef) : (lyapunovVia U a N).PosSemidef := by
  have hN' : (Uᵀ * N * U).PosSemidef := by
    have := hN.conjTranspose_mul_mul_same U
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have := (diagLyapunov_posSemidef ha hN').conjTranspose_mul_mul_same Uᵀ
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

theorem lyapunovVia_posDef (hU : Uᵀ * U = 1) {a : ι → ℝ} (ha : ∀ i, |a i| < 1)
    {N : Matrix ι ι ℝ} (hN : N.PosDef) : (lyapunovVia U a N).PosDef := by
  have hN' : (Uᵀ * N * U).PosDef := by
    have := hN.conjTranspose_mul_mul_same (B := U) (mulVec_injective_of_transpose_mul hU)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have := (diagLyapunov_posDef ha hN').conjTranspose_mul_mul_same (B := Uᵀ)
    (mulVec_injective_of_transpose_mul (mul_transpose_eq_one_of hU))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

omit [Fintype ι] [DecidableEq ι] in
theorem diagLyapunov_add (a : ι → ℝ) (N₁ N₂ : Matrix ι ι ℝ) :
    diagLyapunov a (N₁ + N₂) = diagLyapunov a N₁ + diagLyapunov a N₂ := by
  ext i j
  simp only [diagLyapunov, Matrix.add_apply, Matrix.of_apply, add_div]

omit [DecidableEq ι] in
/-- `lyapunovVia` is additive in the noise. -/
theorem lyapunovVia_add (U : Matrix ι ι ℝ) (a : ι → ℝ) (N₁ N₂ : Matrix ι ι ℝ) :
    lyapunovVia U a (N₁ + N₂) = lyapunovVia U a N₁ + lyapunovVia U a N₂ := by
  unfold lyapunovVia
  rw [Matrix.mul_add, Matrix.add_mul, diagLyapunov_add, Matrix.mul_add, Matrix.add_mul]

omit [Fintype ι] in
/-- `minibatchNoise h t C = 2h·1 + h²t²C ≻ 0` for `h > 0`, `C ⪰ 0`. -/
theorem minibatchNoise_posDef {h : ℝ} (hh : 0 < h) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (minibatchNoise h t C).PosDef :=
  (Matrix.PosDef.one.smul (by linarith : (0 : ℝ) < 2 * h)).add_posSemidef
    (hC.smul (by positivity : (0 : ℝ) ≤ h ^ 2 * t ^ 2))

/-- The minibatch stationary covariance is positive definite. -/
theorem minibatchCov_posDef_frame (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C)).PosDef :=
  lyapunovVia_posDef hU (fun i => abs_one_sub_mul_lt_one hh (hp i) (hev i)) (minibatchNoise_posDef
      hh t hC)

/-- The Lyapunov solution for the ULA noise `2h·1` is the ULA covariance. -/
theorem lyapunovVia_ulaNoise_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) :
    lyapunovVia U (fun i => 1 - h * p i) ((2 * h) • (1 : Matrix ι ι ℝ)) = ulaCov P h := by
  rw [ulaCov_eq_conj_frame hU hdiag hp hev]
  unfold lyapunovVia diagLyapunov
  congr 2
  ext i j
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij
    have := (hp i).ne'
    have hκ : 1 - h * p i / 2 ≠ 0 := by linarith [hev i]
    have hκ' : 2 - h * p i ≠ 0 := by linarith [hev i]
    have hh' := hh.ne'
    have e : 1 - (1 - h * p i) * (1 - h * p i) = h * p i * (2 - h * p i) := by ring
    rw [e]
    field_simp
  · simp

/-- `Σ^{mb} − Σ^{ULA} = lyapunovVia U ρ (h²t²C)`. -/
theorem minibatchCov_sub_ulaCov (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) (C : Matrix ι ι ℝ) :
    lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) - ulaCov P h = lyapunovVia U (fun i
        => 1 - h * p i) ((h ^ 2 * t ^ 2) • C) := by
  have e : minibatchNoise h t C = (2 * h) • (1 : Matrix ι ι ℝ) + (h ^ 2 * t ^ 2) • C := rfl
  rw [e, lyapunovVia_add, lyapunovVia_ulaNoise_frame hU hdiag hp hh hev, add_sub_cancel_left]

theorem minibatchCov_sub_ulaCov_posSemidef (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) : (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) - ulaCov P
        h).PosSemidef := by
  rw [minibatchCov_sub_ulaCov hU hdiag hp hh hev t C]
  exact lyapunovVia_posSemidef (fun i => abs_one_sub_mul_lt_one hh (hp i) (hev i))
    (hC.smul (by positivity : (0 : ℝ) ≤ h ^ 2 * t ^ 2))

/-! ### Frame lemmas for a non-diagonal middle factor -/

theorem sum_sum_conj_mul_conj' (hU : Uᵀ * U = 1) (M₁ M₂ : Matrix ι ι ℝ) :
    ∑ a, ∑ c, (U * M₁ * Uᵀ) a c * (U * M₂ * Uᵀ) c a = ∑ i, ∑ j, M₁ i j * M₂ j i := by
  have e : ∑ a, ∑ c, (U * M₁ * Uᵀ) a c * (U * M₂ * Uᵀ) c a =
      ((U * M₁ * Uᵀ) * (U * M₂ * Uᵀ)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have e2 : (M₁ * M₂).trace = ∑ i, ∑ j, M₁ i j * M₂ j i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, conj_mul_conj_frame hU, Matrix.trace_mul_cycle, hU, Matrix.one_mul, e2]

omit [DecidableEq ι] in
theorem dotProduct_conj_mulVec_frame (U M : Matrix ι ι ℝ) (x y : ι → ℝ) :
    x ⬝ᵥ (U * M * Uᵀ) *ᵥ y = (Uᵀ *ᵥ x) ⬝ᵥ M *ᵥ (Uᵀ *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem conj_transpose_mul_mul_self (hU : Uᵀ * U = 1) (S : Matrix ι ι ℝ) :
    U * (Uᵀ * S * U) * Uᵀ = S := by
  have hUU := mul_transpose_eq_one_of hU
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_assoc, hUU,
    Matrix.mul_one]

/-! ### The variance of the energy under the minibatch stationary law -/

/-- **The minibatch fluctuation of the LLC statistic**: under `N(m, Σ^{mb})`,
`Var(½uᵀHu) = ½∑ᵢⱼλᵢλⱼΣ̂ᵢⱼ² + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼΣ̂ᵢⱼ`. -/
theorem minibatchVar_frame (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ι → ℝ) :
    tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ ((lyapunovVia
      U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^
      2) - (tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹
      ((lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (fun u => 1 / 2 * (u ⬝ᵥ
      H *ᵥ u))) ^ 2 = 1 / 2 * ∑ i, ∑ j, lam i * lam j * (Uᵀ * lyapunovVia U (fun i => 1 - h * p i)
      (minibatchNoise h t C) * U) i j ^ 2 + ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j *
      (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) i j := by
  have hS := minibatchCov_posDef_frame hU hp hh hev t hC
  have hQ := hS.inv
  have hinv : (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹⁻¹ = lyapunovVia U
      (fun i => 1 - h * p i) (minibatchNoise h t C) :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hH := isHermitian_of_frame hU hdiagH
  have hSsym : ∀ i j, (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) j i =
      (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) i j := by
    intro i j
    have := (isHermitian_conjTranspose_mul_mul U hS.1).apply i j
    rwa [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have e1 : (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^ 2) = fun u => (1 / 4 : ℝ) * (u ⬝ᵥ H *ᵥ u) ^ 2 := by
    funext u
    ring
  rw [e1, tiltedExpectation_const_mul, tiltedExpectation_const_mul]
  have hvar := tiltedVar_quadForm hQ ((lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t
      C))⁻¹ *ᵥ m) hH
  rw [tiltMean_mulVec_self hQ, hinv] at hvar
  rw [show ∀ a b : ℝ, 1 / 4 * a - (1 / 2 * b) ^ 2 = 1 / 4 * (a - b ^ 2) from fun a b => by ring,
      hvar]
  set S := (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U)
  have hSU : lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) = U * S * Uᵀ :=
      (conj_transpose_mul_mul_self hU _).symm
  rw [hSU, frame_eq_conj hU hdiagH, conj_mul_conj_frame hU, sum_sum_conj_mul_conj' hU,
    dotProduct_conj_mulVec_frame, transpose_mulVec_conj_mulVec hU, dotProduct_mulVec_eq_sum]
  simp only [Matrix.diagonal_mul, Matrix.mulVec_diagonal, mul_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hSsym i j]
  ring

/-! ### The frame entries and the excess over ULA -/

/-- `Σ̂ᵢⱼ = σᵢ²[i=j] + Eᵢⱼ`, `Eᵢⱼ = h²t²Ĉᵢⱼ/(1 − ρᵢρⱼ)`. -/
theorem minibatchCov_frame_split (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (t : ℝ) (C : Matrix ι ι ℝ) (i j : ι) :
    (Uᵀ * lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) * U) i j = (if i = j then 1 /
        (p i * (1 - h * p i / 2)) else 0) +
      h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j)) := by
  rw [minibatchCov_frame_apply hU h t C i j]
  split_ifs with hij
  · subst hij
    have := (hp i).ne'
    have hκ : 1 - h * p i / 2 ≠ 0 := by linarith [hev i]
    have hκ' : 2 - h * p i ≠ 0 := by linarith [hev i]
    have hh' := hh.ne'
    have e1 : h * (p i + p i) - h ^ 2 * p i * p i = h * p i * (2 - h * p i) := by ring
    have e2 : 1 - (1 - h * p i) * (1 - h * p i) = h * p i * (2 - h * p i) := by ring
    rw [e1, e2]
    field_simp
  · simp only [mul_zero, zero_add]
    congr 1
    ring

omit [DecidableEq ι] in
/-- `Eᵢᵢ = (ht²/2)·Ĉᵢᵢ·σᵢ²`. -/
theorem minibatchCov_frame_split_diag (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i
    < 2)
    (t : ℝ) (C : Matrix ι ι ℝ) (i : ι) :
    h ^ 2 * t ^ 2 * (Uᵀ * C * U) i i / (1 - (1 - h * p i) * (1 - h * p i)) =
      h * t ^ 2 / 2 * (Uᵀ * C * U) i i * (1 / (p i * (1 - h * p i / 2))) := by
  have := (hp i).ne'
  have hh' := hh.ne'
  have hκ : 1 - h * p i / 2 ≠ 0 := by linarith [hev i]
  have hκ' : 2 - h * p i ≠ 0 := by linarith [hev i]
  have e : 1 - (1 - h * p i) * (1 - h * p i) = h * p i * (2 - h * p i) := by ring
  rw [e]
  field_simp

/-- The excess of the minibatch variance over the ULA variance `½∑ᵢ(λᵢσᵢ²)² + ∑ᵢλᵢ²σᵢ²m̂ᵢ²`. -/
theorem minibatchVar_sub_ulaVar (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ι → ℝ) :
    tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ ((lyapunovVia
      U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^
      2) - (tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹
      ((lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (fun u => 1 / 2 * (u ⬝ᵥ
      H *ᵥ u))) ^ 2 - (1 / 2 * ∑ i, (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 + ∑ i, lam i ^ 2 *
      (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2) = ∑ i, lam i ^ 2 * (1 / (p i * (1 - h * p i
      / 2))) * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i i / (1 - (1 - h * p i) * (1 - h * p i))) + 1 / 2 * ∑
      i, ∑ j, lam i * lam j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p
      j))) ^ 2 + ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U)
      i j / (1 - (1 - h * p i) * (1 - h * p j))) := by
  rw [minibatchVar_frame hU hp hh hev hdiagH t hC m]
  simp only [minibatchCov_frame_split hU hp hh hev t C]
  have hsq : ∀ i j, lam i * lam j * ((if i = j then 1 / (p i * (1 - h * p i / 2)) else 0) +
      h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) ^ 2 =
      (if i = j then (lam i * (1 / (p i * (1 - h * p i / 2)))) ^ 2 + 2 * lam i ^ 2 * (1 / (p i * (1
          - h * p i / 2))) *
        (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) else 0) +
      lam i * lam j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) ^ 2
          := by
    intro i j
    split_ifs with hij
    · subst hij; ring
    · ring
  have hlin : ∀ i j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * ((if i = j then 1 / (p i * (1 - h
      * p i / 2)) else 0) +
      h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) =
      (if i = j then lam i ^ 2 * (1 / (p i * (1 - h * p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 else 0) +
      lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j *
        (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) := by
    intro i j
    split_ifs with hij
    · subst hij; ring
    · ring
  simp only [hsq, hlin, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Frame

end Laplace.Sampler
