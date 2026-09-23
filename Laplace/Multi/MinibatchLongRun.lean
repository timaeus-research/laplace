/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.MinibatchFluctuation

/-!
# The minibatch chain's k-step law, energy autocovariance and long-run variance (E8 + E5)

For the constant-noise SGLD chain `x' = m + A(x − m) + ξ`, `A = ulaStep P h = U diag(ρ) Uᵀ`, `Cov ξ
= N = 2h·1 + h²t²C`,
with stationary covariance `Σ = lyapunovVia U ρ N = U Ŝ Uᵀ` (`Ŝ = diagLyapunov ρ N̂`), the
covariance after `k` steps from a
point start is **`Σ_k = Σ − A^kΣ(Aᵀ)^k`**, the `k`-th covariance-step iterate from `0`
(`mbBurnInCov`, `mbBurnInCov_eq_iterate`);
in the frame `Σ_k = U·(Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k))·Uᵀ` with `Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k) = N̂ᵢⱼ∑_{r<k}(ρᵢρⱼ)^r`, so
`xᵀΣ̂_kx = ∑_{r<k}(ρ^r∘x)ᵀN̂(ρ^r∘x) ≥ xᵀN̂x`
and **`Σ_k ≻ 0` for `k ≥ 1`** (`mbBurnInCov_posDef`). The `k`-step law is the tilted Gaussian with
this covariance and the mean
`m + A^k(x₀ − m)`; its energy is **`⟨½uᵀHu⟩_k = ½∑ᵢλᵢŜᵢᵢ(1 − ρᵢ^{2k}) + ½∑ᵢλᵢ(m̂ᵢ + ρᵢ^k(x̂₀ᵢ −
m̂ᵢ))²`** (`mbBurnIn_energy_frame`),
a quadratic-plus-linear probe in `x₀` with tide 102's `B_k, b_k` (`mbCondEnergy_eq`). The
kernel-level autocovariance
`mbAutoCov ℓ = Cov_{N(m,Σ)}(½uᵀHu, mbCondEnergy ℓ)` is
**`½∑ᵢⱼλᵢλⱼŜᵢⱼ²ρⱼ^{2ℓ} + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼρⱼ^ℓ`** at every lag (`mbAutoCov_eq`; lag 0 is tide 104's
variance, diagonal `Ŝ` gives
tide 102), summable (`mbAutoCov_summable`), with long-run variance
**`τ²_{mb} = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²(1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(1+ρⱼ)/(1−ρⱼ)`** (`mbLongRunVar_eq`,
symmetrised form
`mbAutoCov_eq_symm`). With `Ŝᵢⱼ = σᵢ²[i=j] + Eᵢⱼ` the excess over exact-gradient ULA is
`∑ᵢⱼ[½λᵢλⱼ(2σᵢ²[i=j]Eᵢⱼ + Eᵢⱼ²)(1+ρⱼ²)/(1−ρⱼ²) + λᵢλⱼm̂ᵢm̂ⱼEᵢⱼ(1+ρⱼ)/(1−ρⱼ)]`
(`mbLongRunVar_sub_ulaLongRunVar`), whose
centred part is termwise nonnegative and whose mean part is the PSD form `zᵀ(h²t²Ĉ)z`, `zᵢ =
λᵢm̂ᵢ/(1−ρᵢ)`, by the resolvent
identity `((1+ρᵢ)/(1−ρᵢ) + (1+ρⱼ)/(1−ρⱼ))/(2(1−ρᵢρⱼ)) = 1/((1−ρᵢ)(1−ρⱼ))`: **minibatch noise
inflates the long-run variance**,
`τ²_{ULA} ≤ τ²_{mb}` (`ulaLongRunVar_le_mbLongRunVar`) — the temporal inflation statement asked for
in tide 104.
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-! ### Frame lemmas -/

omit [DecidableEq ι] in
theorem transpose_conj_frame (U M : Matrix ι ι ℝ) : (U * M * Uᵀ)ᵀ = U * Mᵀ * Uᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem conj_conj_frame (hU : Uᵀ * U = 1) (M : Matrix ι ι ℝ) : Uᵀ * (U * M * Uᵀ) * U = M := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
    Matrix.mul_one]

/-- Frobenius invariance with a diagonal factor: `∑ᵢⱼ (UDUᵀ)ᵢⱼ (UMUᵀ)ᵢⱼ = ∑ᵢ dᵢ Mᵢᵢ`. -/
theorem sum_sum_conj_diagonal_mul_conj (hU : Uᵀ * U = 1) (d : ι → ℝ) (M : Matrix ι ι ℝ) :
    ∑ i, ∑ j, (U * diagonal d * Uᵀ) i j * (U * M * Uᵀ) i j = ∑ i, d i * M i i := by
  have e : ∀ i j, (U * M * Uᵀ) i j = (U * Mᵀ * Uᵀ) j i := by
    intro i j
    rw [← transpose_conj_frame, Matrix.transpose_apply]
  simp_rw [e]
  rw [sum_sum_conj_mul_conj' hU]
  simp only [Matrix.diagonal_apply, Matrix.transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem ulaStep_transpose_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (h : ℝ) :
    (ulaStep P h)ᵀ = ulaStep P h := by
  rw [ulaStep_eq_conj_frame hU hdiag h, conj_diagonal_transpose_frame]

end Frame

/-! ### The k-step law of the minibatch chain from a start -/

/-- The frame matrix of the `k`-step covariance: `Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k)`. -/
noncomputable def mbFrameCov (U : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j => diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j * (1
      - (1 - h * p i) ^ k * (1 - h * p j) ^ k)

/-- The covariance after `k` steps from a point start: `Σ − A^kΣ(Aᵀ)^k`. -/
noncomputable def mbBurnInCov (U P : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ)
    :
    Matrix ι ι ℝ :=
  lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C) - ulaStep P h ^ k * lyapunovVia U
      (fun i => 1 - h * p i) (minibatchNoise h t C) * (ulaStep P h)ᵀ ^ k

/-- The tilt `Σ_k⁻¹ m_k` of the `k`-step law from `x₀`. -/
noncomputable def mbBurnInTilt (U P : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ)
    (m x₀ : ι → ℝ) : ι → ℝ :=
  (mbBurnInCov U P p h t C k)⁻¹ *ᵥ burnInMeanAnch P h k m x₀

/-- The `k`-step conditional mean of the energy from `x₀` under the minibatch chain. -/
noncomputable def mbCondEnergy (U P H : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ)
    (m : ι → ℝ) (k : ℕ) (x₀ : ι → ℝ) : ℝ :=
  if k = 0 then 1 / 2 * (x₀ ⬝ᵥ H *ᵥ x₀) else
    tiltedExpectation (mbBurnInCov U P p h t C k)⁻¹ (mbBurnInTilt U P p h t C k m x₀)
      (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u))

/-- Lag-`ℓ` energy autocovariance of the stationary minibatch chain (kernel-level). -/
noncomputable def mbAutoCov (U P H : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ)
    (m : ι → ℝ) (ℓ : ℕ) : ℝ :=
  tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ ((lyapunovVia U
      (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m)
      (fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * mbCondEnergy U P H p h t C m ℓ u) -
    tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ ((lyapunovVia
        U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (fun u => 1 / 2 * (u ⬝ᵥ H *ᵥ u)) *
      tiltedExpectation (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹
          ((lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹ *ᵥ m) (mbCondEnergy U P
              H p h t C m ℓ)

/-- The long-run variance `τ²_{mb} = c₀ + 2∑_{ℓ≥1} c_ℓ` of the energy along the stationary
minibatch chain. -/
noncomputable def mbLongRunVar (U P H : Matrix ι ι ℝ) (p : ι → ℝ) (h t : ℝ) (C : Matrix ι ι ℝ)
    (m : ι → ℝ) : ℝ :=
  mbAutoCov U P H p h t C m 0 + 2 * ∑' ℓ : ℕ, mbAutoCov U P H p h t C m (ℓ + 1)

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-- `Σ_k` is the `k`-th covariance-step iterate from `0`. -/
theorem mbBurnInCov_eq_iterate (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ) :
    (covStep (ulaStep P h) (minibatchNoise h t C))^[k] 0 = mbBurnInCov U P p h t C k := by
  unfold mbBurnInCov
  exact covStep_iterate_zero _ _ _ ((minibatch_fixed_iff_frame hU hdiag hp hh hev t C _).2 rfl) k

theorem mbBurnInCov_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (h t : ℝ)
    (C : Matrix ι ι ℝ) (k : ℕ) : mbBurnInCov U P p h t C k = U * mbFrameCov U p h t C k * Uᵀ := by
  unfold mbBurnInCov mbFrameCov lyapunovVia
  rw [ulaStep_transpose_frame hU hdiag h, ulaStep_pow_eq_conj_frame hU hdiag h k,
    conj_mul_conj_frame hU, conj_mul_conj_frame hU, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- `Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k) = N̂ᵢⱼ ∑_{r<k} (ρᵢρⱼ)^r`. -/
theorem mbFrameCov_apply_eq_sum (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2)
    (t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ) (i j : ι) :
    mbFrameCov U p h t C k i j =
      (Uᵀ * minibatchNoise h t C * U) i j * ∑ r ∈ Finset.range k, ((1 - h * p i) * (1 - h * p j)) ^
          r := by
  have hlt := one_sub_mul_pos_of_abs_lt_one (abs_one_sub_mul_lt_one hh (hp i) (hev i))
    (abs_one_sub_mul_lt_one hh (hp j) (hev j))
  have h1 : 1 - (1 - h * p i) * (1 - h * p j) ≠ 0 := hlt.ne'
  have h2 : (1 - h * p i) * (1 - h * p j) - 1 ≠ 0 := by intro h0; apply h1; linarith
  unfold mbFrameCov diagLyapunov
  simp only [Matrix.of_apply]
  rw [geom_sum_eq (by linarith : (1 - h * p i) * (1 - h * p j) ≠ 1), mul_pow]
  field_simp
  ring

/-- `xᵀΣ̂_k x = ∑_{r<k} (ρ^r∘x)ᵀ N̂ (ρ^r∘x)`. -/
theorem mbFrameCov_quadForm (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2)
    (t : ℝ) (C : Matrix ι ι ℝ) (k : ℕ) (x : ι → ℝ) :
    x ⬝ᵥ mbFrameCov U p h t C k *ᵥ x =
      ∑ r ∈ Finset.range k, (fun i => (1 - h * p i) ^ r * x i) ⬝ᵥ (Uᵀ * minibatchNoise h t C * U)
          *ᵥ (fun i => (1 - h * p i) ^ r * x i) := by
  have e : ∀ r : ℕ, (fun i => (1 - h * p i) ^ r * x i) ⬝ᵥ (Uᵀ * minibatchNoise h t C * U) *ᵥ (fun i
      => (1 - h * p i) ^ r * x i) =
      ∑ a, ∑ b, (Uᵀ * minibatchNoise h t C * U) a b * ((1 - h * p a) * (1 - h * p b)) ^ r * (x a *
          x b) := by
    intro r
    rw [quadForm_pow_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  rw [dotProduct_mulVec_eq_sum]
  simp_rw [mbFrameCov_apply_eq_sum hp hh hev t C k, Finset.mul_sum, Finset.sum_mul]
  exact (Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm)).symm

theorem mbFrameCov_posDef (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {k : ℕ} (hk : 1 ≤ k) :
    (mbFrameCov U p h t C k).PosDef := by
  have hN : ((Uᵀ * minibatchNoise h t C * U)).PosDef := by
    have := (minibatchNoise_posDef hh t hC).conjTranspose_mul_mul_same (B := U)
      (mulVec_injective_of_transpose_mul hU)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    have hs := (diagLyapunov_isHermitian (fun i => 1 - h * p i) hN.1).apply i j
    rw [star_trivial] at hs
    simp only [Matrix.transpose_apply, mbFrameCov, Matrix.of_apply, hs,
      mul_comm ((1 - h * p j) ^ k) ((1 - h * p i) ^ k)]
  · rw [star_trivial, mbFrameCov_quadForm hp hh hev t C k x]
    have h0 : (fun i => (1 - h * p i) ^ 0 * x i) ⬝ᵥ (Uᵀ * minibatchNoise h t C * U) *ᵥ (fun i => (1
        - h * p i) ^ 0 * x i) =
        x ⬝ᵥ (Uᵀ * minibatchNoise h t C * U) *ᵥ x := by
      simp only [pow_zero, one_mul]
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.1 hN).2 hx
    rw [star_trivial] at hpos
    calc (0 : ℝ) < x ⬝ᵥ (Uᵀ * minibatchNoise h t C * U) *ᵥ x := hpos
      _ = (fun i => (1 - h * p i) ^ 0 * x i) ⬝ᵥ (Uᵀ * minibatchNoise h t C * U) *ᵥ (fun i => (1 - h
          * p i) ^ 0 * x i) := h0.symm
      _ ≤ ∑ r ∈ Finset.range k, (fun i => (1 - h * p i) ^ r * x i) ⬝ᵥ (Uᵀ * minibatchNoise h t C *
          U) *ᵥ (fun i => (1 - h * p i) ^ r * x i) :=
        Finset.single_le_sum (fun r _ => by
          have := hN.posSemidef.dotProduct_mulVec_nonneg (fun i => (1 - h * p i) ^ r * x i)
          rwa [star_trivial] at this) (Finset.mem_range.2 hk)

/-- **`Σ_k ≻ 0` for `k ≥ 1`.** -/
theorem mbBurnInCov_posDef (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {k : ℕ} (hk : 1 ≤ k) : (mbBurnInCov U P p h t C k).PosDef := by
  rw [mbBurnInCov_eq_conj_frame hU hdiag h t C k]
  have := (mbFrameCov_posDef hU hp hh hev t hC hk).conjTranspose_mul_mul_same (B := Uᵀ)
    (mulVec_injective_of_transpose_mul (mul_transpose_eq_one_of hU))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at this

theorem mbBurnInCov_inv_inv (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (t : ℝ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {k : ℕ} (hk : 1 ≤ k) : (mbBurnInCov U P p h t C k)⁻¹⁻¹ = mbBurnInCov U P p h t C k :=
  Matrix.nonsing_inv_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (mbBurnInCov_posDef hU hdiag hp hh hev t hC hk).det_pos.ne')

/-! ### The energy after k steps -/

/-- **The energy of the `k`-step law**: `⟨½uᵀHu⟩_k = ½∑ᵢλᵢŜᵢᵢ(1 − ρᵢ^{2k}) + ½∑ᵢλᵢ(m̂ᵢ + ρᵢ^k(x̂₀ᵢ
− m̂ᵢ))²`. -/
theorem mbBurnIn_energy_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) {k : ℕ} (hk : 1 ≤ k)
    (m x₀ : ι → ℝ) :
    tiltedExpectation (mbBurnInCov U P p h t C k)⁻¹ (mbBurnInTilt U P p h t C k m x₀) (fun u => 1 /
      2 * (u ⬝ᵥ H *ᵥ u)) = 1 / 2 * ∑ i, lam i * (diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i i * (1 - (1 - h * p i) ^ (2 * k))) + 1 / 2 * ∑ i, lam i * ((Uᵀ *ᵥ
      m) i + (1 - h * p i) ^ k * (Uᵀ *ᵥ (x₀ - m)) i) ^ 2 := by
  have hQ := (mbBurnInCov_posDef hU hdiag hp hh hev t hC hk).inv
  unfold mbBurnInTilt
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hQ, tiltMean_mulVec_self hQ,
    mbBurnInCov_inv_inv hU hdiag hp hh hev t hC hk, mbBurnInCov_eq_conj_frame hU hdiag h t C k,
    frame_eq_conj hU hdiagH, sum_sum_conj_diagonal_mul_conj hU, dotProduct_conj_diagonal_mulVec]
  simp only [transpose_mulVec_burnInMeanAnch hU hdiag, mbFrameCov, Matrix.of_apply, mul_add,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `mbCondEnergy k x₀ = ½x₀ᵀB_kx₀ + b_k·x₀ + c_k` for `k ≥ 1`. -/
theorem mbCondEnergy_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (m x₀ : ι → ℝ) :
    mbCondEnergy U P H p h t C m ℓ x₀ = 1 / 2 * (x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i)
      ^ (2 * ℓ)) * Uᵀ) *ᵥ x₀) + x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p i) ^ ℓ * (1 - (1 -
      h * p i) ^ ℓ)) * Uᵀ) *ᵥ m + (1 / 2 * ∑ i, lam i * (diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i i * (1 - (1 - h * p i) ^ (2 * ℓ))) + 1 / 2 * ∑ i, lam i * ((1 - (1
      - h * p i) ^ ℓ) * (Uᵀ *ᵥ m) i) ^ 2) := by
  unfold mbCondEnergy
  rw [if_neg (Nat.one_le_iff_ne_zero.1 hℓ), mbBurnIn_energy_frame hU hdiag hp hh hev hdiagH t hC hℓ
      m x₀,
    dotProduct_conj_diagonal_mulVec, dotProduct_conj_diagonal_mulVec₂]
  simp only [Matrix.mulVec_sub, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The autocovariance -/

theorem mbFrame_symm (hU : Uᵀ * U = 1) {h : ℝ} (hh : 0 < h) (t : ℝ) {C : Matrix ι ι ℝ} (hC :
    C.PosSemidef)
    (i j : ι) : diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) j i =
        diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j := by
  have hN : ((Uᵀ * minibatchNoise h t C * U)).PosDef := by
    have := (minibatchNoise_posDef hh t hC).conjTranspose_mul_mul_same (B := U)
      (mulVec_injective_of_transpose_mul hU)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hs := (diagLyapunov_isHermitian (fun i => 1 - h * p i) hN.1).apply i j
  rwa [star_trivial] at hs

/-- Lag 0: tide 104's variance in terms of `Ŝ`. -/
theorem mbAutoCov_zero_eq (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (m : ι → ℝ) :
    mbAutoCov U P H p h t C m 0 = 1 / 2 * ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 + ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m)
      j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j := by
  have hc0 : mbCondEnergy U P H p h t C m 0 = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ H *ᵥ x₀) := funext fun x₀ =>
      by
    unfold mbCondEnergy
    exact if_pos rfl
  have e1 : (fun u : ι → ℝ => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) * (1 / 2 * (u ⬝ᵥ H *ᵥ u))) =
      fun u => (1 / 2 * (u ⬝ᵥ H *ᵥ u)) ^ 2 := funext fun u => (sq _).symm
  unfold mbAutoCov
  simp only [hc0]
  rw [e1, ← sq, minibatchVar_frame hU hp hh hev hdiagH t hC m]
  simp only [lyapunovVia, conj_conj_frame hU]

/-- Lag `ℓ ≥ 1`. -/
theorem mbAutoCov_eq_of_pos (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (m : ι → ℝ) :
    mbAutoCov U P H p h t C m ℓ = 1 / 2 * ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 * (1 - h * p j) ^ (2 * ℓ) + ∑ i, ∑ j, lam i * lam j
      * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C *
      U) i j * (1 - h * p j) ^ ℓ := by
  have hS := minibatchCov_posDef_frame hU hp hh hev t hC
  have hQ := hS.inv
  have hinv : (lyapunovVia U (fun i => 1 - h * p i) (minibatchNoise h t C))⁻¹⁻¹ = lyapunovVia U
      (fun i => 1 - h * p i) (minibatchNoise h t C) :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hH := isHermitian_of_frame hU hdiagH
  have hSsym := mbFrame_symm (p := p) hU hh t hC
  have hcond : mbCondEnergy U P H p h t C m ℓ = fun x₀ => 1 / 2 * (x₀ ⬝ᵥ (U * diagonal (fun i => lam
      i * (1 - h * p i) ^ (2 * ℓ)) * Uᵀ) *ᵥ x₀) + x₀ ⬝ᵥ (U * diagonal (fun i => lam i * (1 - h * p
      i) ^ ℓ * (1 - (1 - h * p i) ^ ℓ)) * Uᵀ) *ᵥ m + (1 / 2 * ∑ i, lam i * (diagLyapunov (fun i => 1
      - h * p i) (Uᵀ * minibatchNoise h t C * U) i i * (1 - (1 - h * p i) ^ (2 * ℓ))) + 1 / 2 * ∑ i,
      lam i * ((1 - (1 - h * p i) ^ ℓ) * (Uᵀ *ᵥ m) i) ^ 2) := funext fun x₀ => mbCondEnergy_eq hU
      hdiag hp hh hev hdiagH t hC hℓ m x₀
  unfold mbAutoCov
  simp only [hcond]
  rw [tiltedCov_energy_quadProbe_add_const hQ _ hH (isHermitian_conj_diagonal U _) _ _,
    tiltedCov_quadForm_quadProbe hQ _ hH (isHermitian_conj_diagonal U _) _, tiltMean_mulVec_self hQ,
    hinv]
  unfold lyapunovVia
  rw [frame_eq_conj hU hdiagH]
  simp only [conj_mul_conj_frame hU, sum_sum_conj_mul_conj' hU, dotProduct_conj_mulVec_frame]
  simp only [transpose_mulVec_conj_mulVec hU]
  simp only [dotProduct_mulVec_eq_sum, Matrix.diagonal_mul, Matrix.mulVec_diagonal, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hSsym i j]
  ring

/-- **The stationary energy autocovariance of the minibatch chain**, all lags. -/
theorem mbAutoCov_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (ℓ : ℕ) (m : ι → ℝ) :
    mbAutoCov U P H p h t C m ℓ = 1 / 2 * ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 * (1 - h * p j) ^ (2 * ℓ) + ∑ i, ∑ j, lam i * lam j
      * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C *
      U) i j * (1 - h * p j) ^ ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    rw [mbAutoCov_zero_eq hU hp hh hev hdiagH t hC m]
    simp only [mul_zero, pow_zero, mul_one]
  · exact mbAutoCov_eq_of_pos hU hdiag hp hh hev hdiagH t hC hℓ m

/-! ### The long-run variance -/

theorem mbAutoCov_summable (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ι → ℝ) :
    Summable (fun ℓ : ℕ => mbAutoCov U P H p h t C m ℓ) := by
  have hρ := abs_rho_lt_one hp hh hev
  have e : ∀ ℓ : ℕ, mbAutoCov U P H p h t C m ℓ = ∑ i, ∑ j, (1 / 2 * (lam i * lam j * diagLyapunov
      (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j) ^ 2) ^ ℓ +
      lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i j * (1 - h * p j) ^ ℓ) := by
    intro ℓ
    rw [mbAutoCov_eq hU hdiag hp hh hev hdiagH t hC ℓ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← pow_mul]; ring
  simp_rw [e]
  exact summable_sum fun i _ => summable_sum fun j _ =>
    ((summable_geometric_of_abs_lt_one (hρ j).2).mul_left _).add
      ((summable_geometric_of_abs_lt_one (hρ j).1).mul_left _)

/-- **The long-run variance under minibatch noise**
`τ²_{mb} = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²(1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(1+ρⱼ)/(1−ρⱼ)`. -/
theorem mbLongRunVar_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ι → ℝ) :
    mbLongRunVar U P H p h t C m = 1 / 2 * ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h *
      p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 * ((1 + (1 - h * p j) ^ 2) / (1 - (1 - h * p j) ^
      2)) + ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) := by
  have hρ := abs_rho_lt_one hp hh hev
  have hac : ∀ ℓ : ℕ, mbAutoCov U P H p h t C m (ℓ + 1) = ∑ i, ∑ j, (1 / 2 * (lam i * lam j *
      diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j)
      ^ 2) ^ ℓ * (1 - h * p j) ^ 2 + lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i
      => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j * ((1 - h * p j) ^ ℓ * (1 - h * p j))) :=
      by
    intro ℓ
    rw [mbAutoCov_eq hU hdiag hp hh hev hdiagH t hC (ℓ + 1) m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← pow_mul]; ring
  have hs1 : ∀ i j, Summable (fun ℓ : ℕ => 1 / 2 * (lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j) ^ 2) ^ ℓ * (1 - h * p j) ^ 2) :=
      fun i j => ((summable_geometric_of_abs_lt_one (hρ j).2).mul_left _).mul_right _
  have hs2 : ∀ i j, Summable (fun ℓ : ℕ => lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov
      (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j * ((1 - h * p j) ^ ℓ * (1 - h * p
      j))) := fun i j => ((summable_geometric_of_abs_lt_one (hρ j).1).mul_right _).mul_left _
  have hs : ∀ i j, Summable (fun ℓ : ℕ => 1 / 2 * (lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j) ^ 2) ^ ℓ * (1 - h * p j) ^ 2 +
      lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i j * ((1 - h * p j) ^ ℓ * (1 - h * p j))) := fun i j => (hs1 i
      j).add (hs2 i j)
  have hval : ∀ i j, ∑' ℓ : ℕ, (1 / 2 * (lam i * lam j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j) ^ 2) ^ ℓ * (1 - h * p j) ^ 2 + lam i * lam
      j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C
      * U) i j * ((1 - h * p j) ^ ℓ * (1 - h * p j))) = 1 / 2 * (lam i * lam j * diagLyapunov (fun i
      => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * (1 - (1 - h * p j) ^ 2)⁻¹ * (1 - h
      * p j) ^ 2 + lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i)
      (Uᵀ * minibatchNoise h t C * U) i j * ((1 - (1 - h * p j))⁻¹ * (1 - h * p j)) := by
    intro i j
    rw [(hs1 i j).tsum_add (hs2 i j)]
    simp only [tsum_mul_left, tsum_mul_right, tsum_geometric_of_abs_lt_one (hρ j).2,
      tsum_geometric_of_abs_lt_one (hρ j).1]
  have hin : ∀ i, ∑' ℓ : ℕ, ∑ j, (1 / 2 * (lam i * lam j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ *
      minibatchNoise h t C * U) i j ^ 2) * ((1 - h * p j) ^ 2) ^ ℓ * (1 - h * p j) ^ 2 + lam i * lam
      j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C
      * U) i j * ((1 - h * p j) ^ ℓ * (1 - h * p j))) = ∑ j, (1 / 2 * (lam i * lam j * diagLyapunov
      (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2) * (1 - (1 - h * p j) ^ 2)⁻¹ *
      (1 - h * p j) ^ 2 + lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h *
      p i) (Uᵀ * minibatchNoise h t C * U) i j * ((1 - (1 - h * p j))⁻¹ * (1 - h * p j))) := by
    intro i
    rw [Summable.tsum_finsetSum fun j _ => hs i j]
    exact Finset.sum_congr rfl fun j _ => hval i j
  unfold mbLongRunVar
  rw [mbAutoCov_zero_eq hU hp hh hev hdiagH t hC m]
  simp_rw [hac]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  simp only [hin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : 1 - (1 - h * p j) ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ j).1).2).ne'
  have h2 : 1 - (1 - h * p j) ^ 2 ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ j).2).2).ne'
  generalize diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j = s
  field_simp
  ring


/-! ### Symmetrised form, the split `Ŝ = diag(σ²) + E`, and the inflation over exact-gradient ULA -/

/-- The symmetrised autocovariance `¼∑ᵢⱼλᵢλⱼŜᵢⱼ²(ρᵢ^{2ℓ}+ρⱼ^{2ℓ}) + ½∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(ρᵢ^ℓ+ρⱼ^ℓ)`.
-/
theorem mbAutoCov_eq_symm (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (ℓ : ℕ) (m : ι → ℝ) :
    mbAutoCov U P H p h t C m ℓ = 1 / 4 * ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 * ((1 - h * p i) ^ (2 * ℓ) + (1 - h * p j) ^ (2 *
      ℓ)) + 1 / 2 * ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 -
      h * p i) (Uᵀ * minibatchNoise h t C * U) i j * ((1 - h * p i) ^ ℓ + (1 - h * p j) ^ ℓ) := by
  have hSsym := mbFrame_symm (p := p) hU hh t hC
  rw [mbAutoCov_eq hU hdiag hp hh hev hdiagH t hC ℓ m]
  have h1 : ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C
      * U) i j ^ 2 * (1 - h * p j) ^ (2 * ℓ) = ∑ i, ∑ j, lam i * lam j * diagLyapunov (fun i => 1 -
      h * p i) (Uᵀ * minibatchNoise h t C * U) i j ^ 2 * (1 - h * p i) ^ (2 * ℓ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hSsym i j]; ring
  have h2 : ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p
      i) (Uᵀ * minibatchNoise h t C * U) i j * (1 - h * p j) ^ ℓ = ∑ i, ∑ j, lam i * lam j * (Uᵀ *ᵥ
      m) i * (Uᵀ *ᵥ m) j * diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j *
      (1 - h * p i) ^ ℓ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hSsym i j]; ring
  simp only [mul_add, Finset.sum_add_distrib]
  linear_combination (1 / 4 : ℝ) * h1 + (1 / 2 : ℝ) * h2

/-- `Ŝᵢⱼ = σᵢ²[i=j] + Eᵢⱼ`, `Eᵢⱼ = h²t²Ĉᵢⱼ/(1 − ρᵢρⱼ)` (tide 104's split in terms of `Ŝ`). -/
theorem mbFrame_split (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p
    i < 2)
    (t : ℝ) (C : Matrix ι ι ℝ) (i j : ι) :
    diagLyapunov (fun i => 1 - h * p i) (Uᵀ * minibatchNoise h t C * U) i j = (if i = j then 1 / (p
        i * (1 - h * p i / 2)) else 0) + h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1
            - h * p j)) := by
  have := minibatchCov_frame_split hU hp hh hev t C i j
  simpa only [lyapunovVia, conj_conj_frame hU] using this

/-- **`τ²_{mb} − τ²_{ULA}`**: the excess of the minibatch long-run variance over the exact-gradient
one, with
`Eᵢⱼ = h²t²Ĉᵢⱼ/(1 − ρᵢρⱼ)`. -/
theorem mbLongRunVar_sub_ulaLongRunVar (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀
    i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ) {C :
        Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ι → ℝ) :
    mbLongRunVar U P H p h t C m - ulaLongRunVar P H h m = ∑ i, ∑ j, (1 / 2 * (lam i * lam j * (2 *
      (if i = j then 1 / (p i * (1 - h * p i / 2)) else 0) * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1
      - (1 - h * p i) * (1 - h * p j))) + (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) *
      (1 - h * p j))) ^ 2) * ((1 + (1 - h * p j) ^ 2) / (1 - (1 - h * p j) ^ 2))) + lam i * lam j *
      (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h *
      p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j)))) := by
  rw [mbLongRunVar_eq hU hdiag hp hh hev hdiagH t hC m, ulaLongRunVar_eq hU hdiag hp hh hev hdiagH
      m]
  simp only [mbFrame_split hU hp hh hev t C]
  have hsq : ∀ i j, 1 / 2 * (lam i * lam j * ((if i = j then 1 / (p i * (1 - h * p i / 2)) else 0) +
      h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) ^ 2 * ((1 + (1 - h * p
      j) ^ 2) / (1 - (1 - h * p j) ^ 2))) = (if i = j then 1 / 2 * ((lam i * (1 / (p i * (1 - h * p
      i / 2)))) ^ 2 * ((1 + (1 - h * p j) ^ 2) / (1 - (1 - h * p j) ^ 2))) else 0) + 1 / 2 * (lam i
      * lam j * (2 * (if i = j then 1 / (p i * (1 - h * p i / 2)) else 0) * (h ^ 2 * t ^ 2 * (Uᵀ * C
      * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) + (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1
      - h * p i) * (1 - h * p j))) ^ 2) * ((1 + (1 - h * p j) ^ 2) / (1 - (1 - h * p j) ^ 2))) := by
    intro i j
    split_ifs with hij
    · subst hij; ring
    · ring
  have hlin : ∀ i j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * ((if i = j then 1 / (p i * (1 - h *
      p i / 2)) else 0) + h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) *
      ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) = (if i = j then lam i ^ 2 * (1 / (p i * (1 - h *
      p i / 2))) * (Uᵀ *ᵥ m) i ^ 2 * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) else 0) + lam i *
      lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) *
      (1 - h * p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) := by
    intro i j
    split_ifs with hij
    · subst hij; ring
    · ring
  simp only [Finset.mul_sum]
  simp only [hsq, hlin, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in
theorem conj_symm_apply {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (i j : ι) :
    (Uᵀ * C * U) j i = (Uᵀ * C * U) i j := by
  have hs := (isHermitian_conjTranspose_mul_mul U hC.1).apply i j
  rwa [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial] at hs

/-- **Minibatch noise inflates the long-run variance**: `τ²_{ULA} ≤ τ²_{mb}` (same drift, same
mean). The
centred excess is termwise nonnegative and the mean excess is the PSD form `zᵀ(h²t²Ĉ)z`, `zᵢ =
λᵢm̂ᵢ/(1−ρᵢ)`,
by the resolvent identity `((1+ρᵢ)/(1−ρᵢ) + (1+ρⱼ)/(1−ρⱼ))/(2(1−ρᵢρⱼ)) = 1/((1−ρᵢ)(1−ρⱼ))`. -/
theorem ulaLongRunVar_le_mbLongRunVar (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀
    i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (hlam : ∀ i,
        0 < lam i) (t : ℝ) {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (m : ι → ℝ) :
    ulaLongRunVar P H h m ≤ mbLongRunVar U P H p h t C m := by
  rw [← sub_nonneg, mbLongRunVar_sub_ulaLongRunVar hU hdiag hp hh hev hdiagH t hC m]
  simp only [Finset.sum_add_distrib]
  have hρ := abs_rho_lt_one hp hh hev
  have hCU : (Uᵀ * C * U).PosSemidef := by
    have := hC.conjTranspose_mul_mul_same U
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hCs := conj_symm_apply (U := U) hC
  refine add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) ?_
  · have hw : 0 ≤ (1 + (1 - h * p j) ^ 2) / (1 - (1 - h * p j) ^ 2) :=
      div_nonneg (by positivity) (sub_pos.2 (abs_lt.1 (hρ j).2).2).le
    have hE : 0 ≤ 2 * (if i = j then 1 / (p i * (1 - h * p i / 2)) else 0) * (h ^ 2 * t ^ 2 * (Uᵀ *
        C * U) i j / (1 - (1 - h * p i) * (1 - h * p j))) := by
      split_ifs with hij
      · subst hij
        have hd : 0 < 1 - (1 - h * p i) * (1 - h * p i) :=
          one_sub_mul_pos_of_abs_lt_one (hρ i).1 (hρ i).1
        have hσ : 0 ≤ 1 / (p i * (1 - h * p i / 2)) :=
          div_nonneg one_pos.le (mul_pos (hp i) (by linarith [hev i])).le
        exact mul_nonneg (mul_nonneg two_pos.le hσ)
          (div_nonneg (mul_nonneg (by positivity) hCU.diag_nonneg) hd.le)
      · simp
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg (hlam i).le (hlam j).le) (add_nonneg hE (sq_nonneg _)))
          hw)
  · set z : ι → ℝ := fun i => lam i * (Uᵀ *ᵥ m) i / (1 - (1 - h * p i)) with hz
    set Q : Matrix ι ι ℝ := (h ^ 2 * t ^ 2) • (Uᵀ * C * U) with hQ
    have hQpsd : Q.PosSemidef := hCU.smul (by positivity)
    have hzQ := hQpsd.dotProduct_mulVec_nonneg z
    rw [star_trivial] at hzQ
    have h3 : ∀ i j, lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j /
        (1 - (1 - h * p i) * (1 - h * p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) + lam j *
        lam i * (Uᵀ *ᵥ m) j * (Uᵀ *ᵥ m) i * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) j i / (1 - (1 - h * p j) *
        (1 - h * p i))) * ((1 + (1 - h * p i)) / (1 - (1 - h * p i))) = 2 * (Q i j * (z i * z j)) :=
        by
      intro i j
      have hi : 1 - (1 - h * p i) ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ i).1).2).ne'
      have hj : 1 - (1 - h * p j) ≠ 0 := (sub_pos.2 (abs_lt.1 (hρ j).1).2).ne'
      have hij : 1 - (1 - h * p i) * (1 - h * p j) ≠ 0 := (one_sub_mul_pos_of_abs_lt_one (hρ i).1
          (hρ j).1).ne'
      have hji : 1 - (1 - h * p j) * (1 - h * p i) ≠ 0 := by rw [mul_comm]; exact hij
      rw [hCs i j]
      simp only [hz, hQ, Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    have h4 : ∑ i, ∑ j, (lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i
        j / (1 - (1 - h * p i) * (1 - h * p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) + lam
        j * lam i * (Uᵀ *ᵥ m) j * (Uᵀ *ᵥ m) i * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) j i / (1 - (1 - h * p
        j) * (1 - h * p i))) * ((1 + (1 - h * p i)) / (1 - (1 - h * p i)))) = 2 * (z ⬝ᵥ Q *ᵥ z) :=
        by
      rw [dotProduct_mulVec_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => h3 i j
    have h5 : ∑ i, ∑ j, (lam i * lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i
        j / (1 - (1 - h * p i) * (1 - h * p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) + lam
        j * lam i * (Uᵀ *ᵥ m) j * (Uᵀ *ᵥ m) i * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) j i / (1 - (1 - h * p
        j) * (1 - h * p i))) * ((1 + (1 - h * p i)) / (1 - (1 - h * p i)))) = 2 * ∑ i, ∑ j, lam i *
        lam j * (Uᵀ *ᵥ m) i * (Uᵀ *ᵥ m) j * (h ^ 2 * t ^ 2 * (Uᵀ * C * U) i j / (1 - (1 - h * p i) *
        (1 - h * p j))) * ((1 + (1 - h * p j)) / (1 - (1 - h * p j))) := by
      simp only [Finset.sum_add_distrib, two_mul]
      congr 1
      exact Finset.sum_comm
    linarith [h4, h5, hzQ]

end Frame

end Laplace.Sampler
