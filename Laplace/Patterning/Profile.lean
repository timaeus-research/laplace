/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.ULA

/-!
# The short-chain profile of a Gaussian target

Section 13 of the working note *Patterning flow*: the exact finite-chain form of the
estimator `λ̂(k) = nβ (E[L(w_k)] - L*)` under unadjusted Langevin dynamics on a Gaussian
target, and its three readings (slope, plateau, spectrum).

The chain is `x_{k+1} = (1 - (ε/2) Q) x_k + √ε ξ_k` with `Q = nβ H + γ`, i.e. the repo's
`ulaStep Q (ε/2)` with noise `ulaNoise (ε/2) = ε • 1`. In an eigendirection with `Q`-eigenvalue
`q` the variance after `k` steps from `0` solves `s_{k+1} = (1 - εq/2)² s_k + ε`, which is
`modeVar ε q k`.

* `modeVar_eq`: `s_k = (1 - (1 - εq/2)^{2k}) / (q (1 - εq/4))` under `0 < εq < 4`.
* `profile_eq`: `λ̂(k) = ½ ∑ nβλ_i s_i(k)`, the equation *(profile)* of the note.
* `profile_one`: **the first step is the sharpness**, `λ̂(1) = ½ nβ tr(H) ε`.
* `profile_tendsto`: **the plateau**, `λ̂(k) → ½ ∑ nβλ_i / (q_i (1 - εq_i/4))`.
* `plateau_tendsto_effdim`: **the small-step count**, the plateau tends to
  `½ ∑ λ_i / (λ_i + ρ)` as `ε → 0`, with `ρ = γ/nβ` (Proposition 13.1).
* `ula_iterate_zero`: the finite-chain matrix identity
  `S_{ε,k} = S_ε (1 - (1 - (ε/2) Q)^{2k})` (Proposition 3.2).
* `trace_mul_ulaCov_spectral` / `trace_mul_inv_spectral`: the plateau and the effective
  dimension as traces, `½ nβ tr(H S_ε)` and `½ tr(H (H + ρ)⁻¹)`, for `H` diagonalised by an
  orthogonal matrix.
-/

namespace Laplace.Patterning

open Matrix Finset Filter Topology Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-! ### One mode -/

/-- Variance of one ULA mode after `k` steps from `0`: `s_{k+1} = (1 - εq/2)² s_k + ε`. -/
def modeVar (ε q : ℝ) (k : ℕ) : ℝ := (fun s => (1 - ε * q / 2) ^ 2 * s + ε)^[k] 0

lemma abs_one_sub_half_lt_one {ε q : ℝ} (h0 : 0 < ε * q) (h4 : ε * q < 4) :
    |1 - ε * q / 2| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

lemma one_sub_sq_pos {ε q : ℝ} (h0 : 0 < ε * q) (h4 : ε * q < 4) :
    0 < 1 - (1 - ε * q / 2) ^ 2 := by
  nlinarith [mul_pos h0 (sub_pos.mpr h4)]

/-- **The finite-chain mode variance.** -/
theorem modeVar_eq (ε q : ℝ) (h0 : 0 < ε * q) (h4 : ε * q < 4) (k : ℕ) :
    modeVar ε q k = 1 / (q * (1 - ε * q / 4)) * (1 - (1 - ε * q / 2) ^ (2 * k)) := by
  unfold modeVar
  rw [ar1_var_iterate _ _ (abs_one_sub_half_lt_one h0 h4)]
  congr 1
  have hq : q ≠ 0 := by
    rintro rfl
    simp at h0
  have h1 : 1 - (1 - ε * q / 2) ^ 2 ≠ 0 := (one_sub_sq_pos h0 h4).ne'
  have h2 : q * (1 - ε * q / 4) ≠ 0 := mul_ne_zero hq (by linarith)
  rw [div_eq_div_iff h1 h2]
  ring

/-- The first step: `s_1 = ε`, whatever `q`. -/
@[simp] theorem modeVar_one (ε q : ℝ) : modeVar ε q 1 = ε := by
  simp [modeVar]

/-- **The plateau of one mode.** `s_k → 1 / (q (1 - εq/4))`. -/
theorem modeVar_tendsto (ε q : ℝ) (h0 : 0 < ε * q) (h4 : ε * q < 4) :
    Tendsto (modeVar ε q) atTop (𝓝 (1 / (q * (1 - ε * q / 4)))) := by
  have hρ : |(1 - ε * q / 2) ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) (abs_one_sub_half_lt_one h0 h4) two_ne_zero
  have hpow : Tendsto (fun k : ℕ => (1 - ε * q / 2) ^ (2 * k)) atTop (𝓝 0) := by
    simp_rw [pow_mul]
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ
  have h := (hpow.const_sub 1).const_mul (1 / (q * (1 - ε * q / 4)))
  simp only [sub_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards with k
  rw [modeVar_eq ε q h0 h4 k]

/-! ### The profile -/

/-- The Gaussian ULA profile `λ̂(k) = ½ ∑ nβ λ_i s_i(k)`, `q_i = nβ λ_i + γ`. -/
def profile (t γ ε : ℝ) (lam : ι → ℝ) (k : ℕ) : ℝ :=
  (1 / 2) * ∑ i, t * lam i * modeVar ε (t * lam i + γ) k

/-- The plateau value `½ ∑ nβ λ_i / (q_i (1 - εq_i/4))`. -/
def plateau (t γ ε : ℝ) (lam : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, t * lam i * (1 / ((t * lam i + γ) * (1 - ε * (t * lam i + γ) / 4)))

/-- **The finite-chain profile** (equation *(profile)* of the note). -/
theorem profile_eq (t γ ε : ℝ) (lam : ι → ℝ)
    (hstab : ∀ i, 0 < ε * (t * lam i + γ) ∧ ε * (t * lam i + γ) < 4) (k : ℕ) :
    profile t γ ε lam k = (1 / 2) * ∑ i, t * lam i / ((t * lam i + γ) * (1 - ε * (t * lam i + γ) / 4))
      * (1 - (1 - ε * (t * lam i + γ) / 2) ^ (2 * k)) := by
  unfold profile
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [modeVar_eq _ _ (hstab i).1 (hstab i).2]
  ring

/-- **The first step is the sharpness.** `λ̂(1) = ½ nβ tr(H) · ε`. -/
theorem profile_one (t γ ε : ℝ) (lam : ι → ℝ) :
    profile t γ ε lam 1 = (1 / 2) * t * (∑ i, lam i) * ε := by
  unfold profile
  simp only [modeVar_one]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The plateau.** `λ̂(k) → ½ ∑ nβ λ_i / (q_i (1 - εq_i/4))`. -/
theorem profile_tendsto (t γ ε : ℝ) (lam : ι → ℝ)
    (hstab : ∀ i, 0 < ε * (t * lam i + γ) ∧ ε * (t * lam i + γ) < 4) :
    Tendsto (profile t γ ε lam) atTop (𝓝 (plateau t γ ε lam)) := by
  unfold profile plateau
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
  exact (modeVar_tendsto _ _ (hstab i).1 (hstab i).2).const_mul _

/-- **The small-step count is the effective dimension.** As `ε → 0` the plateau tends to
`½ ∑ λ_i / (λ_i + ρ)`, `ρ = γ/nβ` (Proposition 13.1). -/
theorem plateau_tendsto_effdim (t γ : ℝ) (lam : ι → ℝ) (ht : 0 < t)
    (hq : ∀ i, t * lam i + γ ≠ 0) :
    Tendsto (fun ε => plateau t γ ε lam) (𝓝 0) (𝓝 ((1 / 2) * ∑ i, lam i / (lam i + γ / t))) := by
  have hval : (1 / 2) * ∑ i, lam i / (lam i + γ / t) = plateau t γ 0 lam := by
    unfold plateau
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq' := hq i
    have ht' := ht.ne'
    simp only [zero_mul, zero_div, sub_zero, mul_one]
    field_simp
  rw [hval]
  unfold plateau
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
  refine Tendsto.const_mul _ ?_
  have hc : ContinuousAt (fun ε : ℝ => 1 / ((t * lam i + γ) * (1 - ε * (t * lam i + γ) / 4))) 0 := by
    apply ContinuousAt.div continuousAt_const
    · fun_prop
    · simp [hq i]
  exact hc.tendsto

/-! ### Matrix forms -/

/-- **Finite-chain covariance** (Proposition 3.2): from `x_0 = 0`,
`S_{ε,k} = S_ε (1 - (1 - (ε/2) Q)^{2k})`, in the repo's `h = ε/2` convention. -/
theorem ula_iterate_zero (P : Matrix ι ι ℝ) (h : ℝ) (hP : Pᵀ = P)
    (hdet : IsUnit (P - (h / 2) • (P * P)).det) (k : ℕ) :
    (covStep (ulaStep P h) (ulaNoise h))^[k] 0 = ulaCov P h * (1 - (ulaStep P h) ^ (2 * k)) := by
  have hAt : (ulaStep P h)ᵀ = ulaStep P h := by
    simp [ulaStep, Matrix.transpose_sub, Matrix.transpose_smul, hP]
  have hcomm : ulaStep P h * ulaCov P h = ulaCov P h * ulaStep P h := by
    simp only [ulaStep, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, ulaCov_commute P h hdet]
  exact covStep_iterate_zero_of_comm _ _ _ (ulaCov_fixed P h hP hdet) hAt hcomm k

/-- `tr(U diag(b) Uᵀ X) = ∑ b_i (Uᵀ X U)_ii` for orthogonal `U`. -/
theorem trace_spectral_mul (U : Matrix ι ι ℝ) (b : ι → ℝ) (X : Matrix ι ι ℝ) :
    (U * diagonal b * Uᵀ * X).trace = ∑ i, b i * (Uᵀ * X * U) i i := by
  have h1 : U * diagonal b * Uᵀ * X = U * (diagonal b * (Uᵀ * X)) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_assoc]

/-- `a • (U D Uᵀ) = U (a • D) Uᵀ`. -/
theorem smul_spectral (U : Matrix ι ι ℝ) (a : ℝ) (D : Matrix ι ι ℝ) :
    a • (U * D * Uᵀ) = U * (a • D) * Uᵀ := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The inverse of `U diag(a) Uᵀ` is `U diag(a⁻¹) Uᵀ` when all `a_i ≠ 0`. -/
theorem inv_spectral (U : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (ha : ∀ i, a i ≠ 0) :
    (U * diagonal a * Uᵀ)⁻¹ = U * diagonal (fun i => (a i)⁻¹) * Uᵀ := by
  apply Matrix.inv_eq_left_inv
  have hcancel : ∀ Z : Matrix ι ι ℝ, Uᵀ * (U * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hcancel]
  rw [← Matrix.mul_assoc (diagonal _), Matrix.diagonal_mul_diagonal]
  have : (fun i => (a i)⁻¹ * a i) = fun _ => (1 : ℝ) := by
    funext i
    exact inv_mul_cancel₀ (ha i)
  rw [this, Matrix.diagonal_one, Matrix.one_mul, hU']

/-- `(U diag(a) Uᵀ)(U diag(b) Uᵀ) = U diag(ab) Uᵀ`. -/
theorem spectral_mul_spectral (U : Matrix ι ι ℝ) (a b : ι → ℝ) (hU : Uᵀ * U = 1) :
    (U * diagonal a * Uᵀ) * (U * diagonal b * Uᵀ) = U * diagonal (fun i => a i * b i) * Uᵀ := by
  have hcancel : ∀ Z : Matrix ι ι ℝ, Uᵀ * (U * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hcancel]
  rw [← Matrix.mul_assoc (diagonal a), Matrix.diagonal_mul_diagonal]

/-- `tr(U diag(a) Uᵀ) = ∑ a_i`. -/
theorem trace_spectral (U : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1) :
    (U * diagonal a * Uᵀ).trace = ∑ i, a i := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm U, Matrix.mul_assoc, hU, Matrix.mul_one,
    Matrix.trace_diagonal]

/-- `U diag(a) Uᵀ + ρ • 1 = U diag(a + ρ) Uᵀ`. -/
theorem spectral_add_smul_one (U : Matrix ι ι ℝ) (a : ι → ℝ) (ρ : ℝ) (hU' : U * Uᵀ = 1) :
    U * diagonal a * Uᵀ + ρ • (1 : Matrix ι ι ℝ) = U * diagonal (fun i => a i + ρ) * Uᵀ := by
  have hone : ρ • (1 : Matrix ι ι ℝ) = U * diagonal (fun _ => ρ) * Uᵀ := by
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU']
  rw [hone, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]

/-- **The effective dimension as a trace.** For `H = U diag(λ) Uᵀ` and `λ_i + ρ ≠ 0`,
`tr(H (H + ρ)⁻¹) = ∑ λ_i / (λ_i + ρ)`; halved, this is `λ̂_∞` of Proposition 13.1. -/
theorem trace_mul_inv_spectral (U : Matrix ι ι ℝ) (lam : ι → ℝ) (ρ : ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hρ : ∀ i, lam i + ρ ≠ 0) :
    ((U * diagonal lam * Uᵀ) * (U * diagonal lam * Uᵀ + ρ • (1 : Matrix ι ι ℝ))⁻¹).trace
      = ∑ i, lam i / (lam i + ρ) := by
  rw [spectral_add_smul_one U lam ρ hU', inv_spectral U _ hU hU' hρ,
    spectral_mul_spectral U _ _ hU, trace_spectral U _ hU]
  simp only [div_eq_mul_inv]

/-- **The ULA law of a spectrally decomposed precision.** For `Q = U diag(q) Uᵀ`,
`ulaCov Q h = U diag(1/(q_i (1 - h q_i/2))) Uᵀ`. -/
theorem ulaCov_spectral (U : Matrix ι ι ℝ) (q : ι → ℝ) (h : ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hq : ∀ i, q i * (1 - h * q i / 2) ≠ 0) :
    ulaCov (U * diagonal q * Uᵀ) h
      = U * diagonal (fun i => (q i * (1 - h * q i / 2))⁻¹) * Uᵀ := by
  unfold ulaCov
  rw [spectral_mul_spectral U _ _ hU, smul_spectral, ← Matrix.sub_mul, ← Matrix.mul_sub,
    ← Matrix.diagonal_smul]
  have heq : diagonal q - diagonal ((h / 2) • fun i => q i * q i)
      = diagonal fun i => q i * (1 - h * q i / 2) := by
    rw [Matrix.diagonal_sub]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact inv_spectral U _ hU hU' hq

/-- **The plateau as a trace.** For `H = U diag(λ) Uᵀ`, `Q = nβ H + γ` and the ULA law
`S = ulaCov Q h`, `nβ tr(H S) = ∑ nβ λ_i / (q_i (1 - h q_i/2))`; with `h = ε/2` and halved
this is `plateau`. -/
theorem trace_mul_ulaCov_spectral (U : Matrix ι ι ℝ) (lam : ι → ℝ) (t γ h : ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hq : ∀ i, (t * lam i + γ) * (1 - h * (t * lam i + γ) / 2) ≠ 0) :
    t * ((U * diagonal lam * Uᵀ) *
        ulaCov (t • (U * diagonal lam * Uᵀ) + γ • (1 : Matrix ι ι ℝ)) h).trace
      = ∑ i, t * lam i / ((t * lam i + γ) * (1 - h * (t * lam i + γ) / 2)) := by
  have hQ : t • (U * diagonal lam * Uᵀ) + γ • (1 : Matrix ι ι ℝ)
      = U * diagonal (fun i => t * lam i + γ) * Uᵀ := by
    rw [smul_spectral, ← Matrix.diagonal_smul, spectral_add_smul_one U _ γ hU']
    congr 3
  rw [hQ, ulaCov_spectral U _ h hU hU' hq, spectral_mul_spectral U _ _ hU, trace_spectral U _ hU,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- The plateau is `½ nβ tr(H S_ε)` with `h = ε/2`. -/
theorem plateau_eq_trace (U : Matrix ι ι ℝ) (lam : ι → ℝ) (t γ ε : ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hq : ∀ i, (t * lam i + γ) * (1 - ε / 2 * (t * lam i + γ) / 2) ≠ 0) :
    plateau t γ ε lam = (1 / 2) * (t * ((U * diagonal lam * Uᵀ) *
        ulaCov (t • (U * diagonal lam * Uᵀ) + γ • (1 : Matrix ι ι ℝ)) (ε / 2)).trace) := by
  rw [trace_mul_ulaCov_spectral U lam t γ (ε / 2) hU hU' hq]
  unfold plateau
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ε / 2 * (t * lam i + γ) / 2 = ε * (t * lam i + γ) / 4 by ring]
  ring

end

end Laplace.Patterning
