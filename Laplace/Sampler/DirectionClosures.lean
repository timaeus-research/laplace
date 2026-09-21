/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.AR1
import Laplace.Sampler.ULAEigen
import Laplace.Multi.TiltedGaussian

/-!
# Per-direction closures of E1–E3

* **The finite-chain shortfall.** For `C` AR(1) chains (`0 ≤ ρ < 1`, innovation variance `v`,
  stationary variance `σ² = v/(1−ρ²)`), `b` burn-in steps and `N` draws, the expected pooled sample
  variance is at most `σ²` and falls short of it by at most
  `σ² (ρ^{2(b+1)}/(N(1−ρ²)) + (1+ρ)/((1−ρ)CN))` (`stationary_sub_pooled_le`): the second term is
  the note's `τ/(CN)` with `τ = (1+ρ)/(1−ρ)` the integrated autocorrelation time. Along a unit
  eigenvector of the precision with eigenvalue `p` the ULA chain has `ρ = 1 − hp`, so the
  shortfall of the sampled variance from the ULA law is at most
  `σ² ((1−hp)^{2(b+1)}/(N(1−(1−hp)²)) + 2/(h p C N))` — `τ_flat = 2/(h p_min)`
  (`expected_pooled_sample_variance_ula_shortfall`).
* **The localised LLC in the eigenbasis.** `∑ᵢⱼ (tH)ᵢⱼ ((tH+γ)⁻¹)ᵢⱼ = ∑ᵢ tλᵢ/(tλᵢ + γ)`, so the
  centred localised LLC is `½ ∑ᵢ tλᵢ/(tλᵢ + γ)` (`localised_llc_centred_eigen`), and along an
  eigenvector `u` the localised variance is `‖u‖²/(tλ + γ) = (‖u‖²/(tλ))/(1 + γ_rel)` with
  `γ_rel = γ/(tλ)` (`eigen_direction_variance`, `eigen_direction_variance_rel`).
-/

open Finset Matrix

namespace Laplace.Sampler

/-! ### Elementary sums -/

theorem geom_sum_le_one_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ i ∈ range N, x ^ i ≤ 1 / (1 - x) := by
  rw [geom_sum_eq hx1.ne N]
  have h1 : 0 < 1 - x := by linarith
  rw [show (x ^ N - 1) / (x - 1) = (1 - x ^ N) / (1 - x) by
    rw [← neg_sub 1 (x ^ N), ← neg_sub 1 x, neg_div_neg_eq]]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hx0 N]) h1.le

/-- `R₂ = ∑_{i<N} ρ^{2(b+1+i)} ≤ ρ^{2(b+1)}/(1 − ρ²)`. -/
theorem sum_pow_two_mul_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (b N : ℕ) :
    ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) ≤ ρ ^ (2 * (b + 1)) / (1 - ρ ^ 2) := by
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hρ2' : 0 ≤ ρ ^ 2 := by positivity
  have h : ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) =
      ρ ^ (2 * (b + 1)) * ∑ i ∈ range N, (ρ ^ 2) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [h, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_one_div hρ2' hρ2 N) (by positivity)

/-- `T_N = N + 2∑_{m<N}(N − m − 1)ρ^{m+1} ≤ N(1 + ρ)/(1 − ρ)`. -/
theorem toeplitz_sum_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) :
    (N : ℝ) + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) ≤
      N * (1 + ρ) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  have hsum : ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) ≤ N * (ρ / (1 - ρ)) := by
    calc ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)
        ≤ ∑ m ∈ range N, (N : ℝ) * ρ ^ (m + 1) := by
          refine Finset.sum_le_sum fun m _ => ?_
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = N * (ρ * ∑ m ∈ range N, ρ ^ m) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ ≤ N * (ρ * (1 / (1 - ρ))) := by
          gcongr
          exact geom_sum_le_one_div hρ0 hρ1 N
      _ = N * (ρ / (1 - ρ)) := by ring
  calc (N : ℝ) + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)
      ≤ N + 2 * (N * (ρ / (1 - ρ))) := by linarith
    _ = N * (1 + ρ) / (1 - ρ) := by field_simp; ring

/-! ### The shortfall of the finite-chain prediction -/

/-- The closed form of the finite-chain prediction as a function of `(ρ, v, N, C, b)`. -/
noncomputable def finiteChainPrediction (ρ v : ℝ) (N C b : ℕ) : ℝ :=
  v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i))) / N -
    v / (1 - ρ ^ 2) * ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
      (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) / (C * N ^ 2)

/-- The finite-chain prediction never exceeds the stationary variance. -/
theorem finiteChainPrediction_le {ρ v : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v) {N C : ℕ}
    (hN : 0 < N) (hC : 0 < C) (b : ℕ)
    (hT : (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2 ≤
      N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) :
    finiteChainPrediction ρ v N C b ≤ v / (1 - ρ ^ 2) := by
  unfold finiteChainPrediction
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hσ : 0 ≤ v / (1 - ρ ^ 2) := div_nonneg hv (by linarith)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hR2 : 0 ≤ ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) :=
    Finset.sum_nonneg fun i _ => pow_nonneg hρ0 _
  have h1 : v / (1 - ρ ^ 2) * (N - ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i))) / N ≤ v / (1 - ρ ^ 2) := by
    rw [div_le_iff₀ hN']
    nlinarith
  have h2 : 0 ≤ v / (1 - ρ ^ 2) * ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
      (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) / (C * N ^ 2) :=
    div_nonneg (mul_nonneg hσ (by linarith)) (by positivity)
  linarith

/-- **The shortfall bound**: `σ² − prediction ≤ σ² (ρ^{2(b+1)}/(N(1−ρ²)) + (1+ρ)/((1−ρ)CN))`. -/
theorem stationary_sub_finiteChainPrediction_le {ρ v : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v)
    {N C : ℕ} (hN : 0 < N) (hC : 0 < C) (b : ℕ) :
    v / (1 - ρ ^ 2) - finiteChainPrediction ρ v N C b ≤
      v / (1 - ρ ^ 2) * (ρ ^ (2 * (b + 1)) / (N * (1 - ρ ^ 2)) + (1 + ρ) / ((1 - ρ) * C * N)) := by
  unfold finiteChainPrediction
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have h1ρ2 : 0 < 1 - ρ ^ 2 := by linarith
  have hσ : 0 ≤ v / (1 - ρ ^ 2) := div_nonneg hv h1ρ2.le
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  set σ := v / (1 - ρ ^ 2) with hσdef
  set R₂ := ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) with hR₂
  set R₁ := ∑ i ∈ range N, ρ ^ (b + 1 + i) with hR₁
  set T := (N : ℝ) + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) with hT
  have hR2 := sum_pow_two_mul_le hρ0 hρ1 b N
  have hTle := toeplitz_sum_le hρ0 hρ1 N
  have hR1sq : 0 ≤ R₁ ^ 2 := sq_nonneg _
  have hlhs : σ - (σ * (N - R₂) / N - σ * (T - R₁ ^ 2) / (C * N ^ 2)) =
      σ * (R₂ / N) + σ * ((T - R₁ ^ 2) / (C * N ^ 2)) := by
    field_simp
    ring
  rw [hlhs]
  have hb1 : σ * (R₂ / N) ≤ σ * (ρ ^ (2 * (b + 1)) / (N * (1 - ρ ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ hσ
    rw [div_le_div_iff₀ hN' (by positivity)]
    calc R₂ * (N * (1 - ρ ^ 2)) = (R₂ * (1 - ρ ^ 2)) * N := by ring
      _ ≤ ρ ^ (2 * (b + 1)) * N := by
          apply mul_le_mul_of_nonneg_right _ hN'.le
          rwa [← le_div_iff₀ h1ρ2]
  have hb2 : σ * ((T - R₁ ^ 2) / (C * N ^ 2)) ≤ σ * ((1 + ρ) / ((1 - ρ) * C * N)) := by
    apply mul_le_mul_of_nonneg_left _ hσ
    calc (T - R₁ ^ 2) / (C * N ^ 2) ≤ T / (C * N ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
      _ ≤ (N * (1 + ρ) / (1 - ρ)) / (C * N ^ 2) :=
          div_le_div_of_nonneg_right hTle (by positivity)
      _ = (1 + ρ) / ((1 - ρ) * C * N) := by
          field_simp
  linarith

namespace AR1Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ρ v : ℝ}

/-- The pooled sample variance of `C` chains over the draws `b+1, …, b+N` (divisor `CN`). -/
noncomputable def pooledSampleVariance {C : ℕ} (X : Fin C → AR1Chain E ρ v) (N b : ℕ) : ℝ :=
  (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, ‖(X c).x (b + 1 + i)‖ ^ 2 -
    ‖(1 / ((C : ℝ) * N)) • ∑ c, ∑ i ∈ range N, (X c).x (b + 1 + i)‖ ^ 2

theorem pooledSampleVariance_eq {C : ℕ} (X : Fin C → AR1Chain E ρ v)
    (hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0)
    (hρ : ρ ^ 2 ≠ 1) {N : ℕ} (hN : 0 < N) (hC : 0 < C) (b : ℕ) :
    pooledSampleVariance X N b = finiteChainPrediction ρ v N C b :=
  pooled_sample_variance X hcross hρ hN hC b

/-- `T_N − R₁² ≥ 0`: it is `‖∑ x‖²/σ²`. -/
theorem toeplitz_sub_sq_nonneg (X : AR1Chain E ρ v) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 < v)
    (b N : ℕ) :
    (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2 ≤
      N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) := by
  have hρ2 : ρ ^ 2 ≠ 1 := by nlinarith
  have h := X.norm_sum_window_sq hρ2 b N
  rw [sum_sum_pow_dist] at h
  have hσ : 0 < v / (1 - ρ ^ 2) := div_pos hv (by nlinarith)
  have hnn : 0 ≤ v / (1 - ρ ^ 2) *
      ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1)) -
        (∑ i ∈ range N, ρ ^ (b + 1 + i)) ^ 2) := h ▸ sq_nonneg _
  have := nonneg_of_mul_nonneg_right hnn hσ
  linarith

/-- The pooled sample variance never exceeds the stationary variance. -/
theorem pooledSampleVariance_le {C : ℕ} (X : Fin C → AR1Chain E ρ v)
    (hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 < v) {N : ℕ} (hN : 0 < N) (hC : 0 < C) (b : ℕ) :
    pooledSampleVariance X N b ≤ v / (1 - ρ ^ 2) := by
  rw [pooledSampleVariance_eq X hcross (by nlinarith) hN hC b]
  exact finiteChainPrediction_le hρ0 hρ1 hv.le hN hC b
    (toeplitz_sub_sq_nonneg (X ⟨0, hC⟩) hρ0 hρ1 hv b N)

/-- **The shortfall of the pooled sample variance** is at most
`σ² (ρ^{2(b+1)}/(N(1−ρ²)) + τ/(CN))` with `τ = (1+ρ)/(1−ρ)`. -/
theorem stationary_sub_pooledSampleVariance_le {C : ℕ} (X : Fin C → AR1Chain E ρ v)
    (hcross : ∀ c c', c ≠ c' → ∀ j k, inner ℝ ((X c).η j) ((X c').η k) = 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 0 ≤ v) {N : ℕ} (hN : 0 < N) (hC : 0 < C) (b : ℕ) :
    v / (1 - ρ ^ 2) - pooledSampleVariance X N b ≤
      v / (1 - ρ ^ 2) * (ρ ^ (2 * (b + 1)) / (N * (1 - ρ ^ 2)) + (1 + ρ) / ((1 - ρ) * C * N)) := by
  rw [pooledSampleVariance_eq X hcross (by nlinarith) hN hC b]
  exact stationary_sub_finiteChainPrediction_le hρ0 hρ1 hv hN hC b

end AR1Chain

/-! ### The ULA realisation: `τ_flat = 2/(h p)` -/

section ULAShortfall

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

/-- **The finite-chain shortfall along an eigendirection of ULA**: with `ρ = 1 − hp`, the expected
pooled sample variance of the projections on a unit eigenvector falls short of the ULA law
`2h/(1 − (1−hp)²)` by at most `σ² ((1−hp)^{2(b+1)}/(N(1−(1−hp)²)) + 2/(h p C N))`; the last term is
`τ_flat/(CN)` with `τ_flat = 2/(hp)`. -/
theorem expected_pooled_sample_variance_ula_shortfall {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ}
    (hh : 0 < h) {u : EuclideanSpace ℝ ι} {p : ℝ} (hp : 0 < p) (hhp : h * p < 1)
    (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
    (hind : ProbabilityTheory.iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    (2 * h) / (1 - (1 - h * p) ^ 2) -
      ∫ ω, ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2 -
        ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω)) ^ 2) ∂P ≤
      (2 * h) / (1 - (1 - h * p) ^ 2) *
        ((1 - h * p) ^ (2 * (b + 1)) / (N * (1 - (1 - h * p) ^ 2)) + 2 / (h * p * C * N)) := by
  have hhp0 : 0 < h * p := mul_pos hh hp
  have hρ : (1 - h * p) ^ 2 ≠ 1 := by nlinarith
  rw [expected_pooled_sample_variance_ula hsym hh.le hu hunit hρ hC hN b ξ hmeas hlaw hind]
  change (2 * h) / (1 - (1 - h * p) ^ 2) - finiteChainPrediction (1 - h * p) (2 * h) N C b ≤ _
  have hbound := stationary_sub_finiteChainPrediction_le (ρ := 1 - h * p) (v := 2 * h)
    (by linarith) (by linarith) (by positivity) hN hC b
  refine hbound.trans ?_
  have hσ : 0 ≤ (2 * h) / (1 - (1 - h * p) ^ 2) := div_nonneg (by positivity) (by nlinarith)
  apply mul_le_mul_of_nonneg_left _ hσ
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have h2 : (1 + (1 - h * p)) / ((1 - (1 - h * p)) * C * N) ≤ 2 / (h * p * C * N) := by
    rw [show (1 : ℝ) - (1 - h * p) = h * p by ring]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

end ULAShortfall

/-! ### The localised LLC in the eigenbasis -/

section Eigen

open Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem effectivePrecision_eq_conj {H : Matrix ι ι ℝ} (hH : H.PosDef) (t γ : ℝ) :
    t • H + γ • (1 : Matrix ι ι ℝ) =
      orthoOf hH.1 * diagonal (fun i => t * hH.1.eigenvalues i + γ) * (orthoOf hH.1)ᵀ := by
  have hspec := spectral_real hH.1
  have hUU := orthoOf_mul_transpose hH.1
  have hdiag : diagonal (fun i => t * hH.1.eigenvalues i + γ) =
      t • diagonal hH.1.eigenvalues + γ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hUU, ← hspec]

theorem effectivePrecision_inv_eq {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) :
    (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ =
      orthoOf hH.1 * diagonal (fun i => (t * hH.1.eigenvalues i + γ)⁻¹) * (orthoOf hH.1)ᵀ := by
  apply Matrix.inv_eq_right_inv
  rw [effectivePrecision_eq_conj hH t γ]
  have hUtU := orthoOf_transpose_mul hH.1
  have hUU := orthoOf_mul_transpose hH.1
  have hne : ∀ i, t * hH.1.eigenvalues i + γ ≠ 0 := fun i => by
    have := hH.eigenvalues_pos i
    positivity
  calc orthoOf hH.1 * diagonal (fun i => t * hH.1.eigenvalues i + γ) * (orthoOf hH.1)ᵀ *
        (orthoOf hH.1 * diagonal (fun i => (t * hH.1.eigenvalues i + γ)⁻¹) * (orthoOf hH.1)ᵀ)
      = orthoOf hH.1 * (diagonal (fun i => t * hH.1.eigenvalues i + γ) *
          diagonal (fun i => (t * hH.1.eigenvalues i + γ)⁻¹)) * (orthoOf hH.1)ᵀ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (orthoOf hH.1)ᵀ (orthoOf hH.1), hUtU, Matrix.one_mul]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have : (fun i => (t * hH.1.eigenvalues i + γ) * (t * hH.1.eigenvalues i + γ)⁻¹) =
            fun _ => (1 : ℝ) := by
          funext i
          exact mul_inv_cancel₀ (hne i)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hUU]

/-- `∑ᵢⱼ (tH)ᵢⱼ ((tH+γ)⁻¹)ᵢⱼ = ∑ᵢ tλᵢ/(tλᵢ + γ)`. -/
theorem sum_mul_effectivePrecision_inv_eq {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ}
    (ht : 0 < t) (hγ : 0 ≤ γ) :
    ∑ i, ∑ j, (t • H) i j * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ i j =
      ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) := by
  set X := (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ with hX
  have hUU := orthoOf_mul_transpose hH.1
  have hUtU := orthoOf_transpose_mul hH.1
  have hXsymm : Xᵀ = X := by
    rw [hX, effectivePrecision_inv_eq hH ht hγ, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hXij : ∀ i j, X j i = X i j := fun i j => by
    rw [← Matrix.transpose_apply X i j, hXsymm]
  have h1 : ∑ i, ∑ j, (t • H) i j * X i j = ((t • H) * X).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hXij]
  have hconjH : (orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1 = t • diagonal hH.1.eigenvalues := by
    rw [Matrix.mul_smul, Matrix.smul_mul, orthoOf_transpose_mul_mul hH.1]
  have hconjX : (orthoOf hH.1)ᵀ * X * orthoOf hH.1 =
      diagonal (fun i => (t * hH.1.eigenvalues i + γ)⁻¹) := by
    rw [hX, effectivePrecision_inv_eq hH ht hγ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (orthoOf hH.1)ᵀ (orthoOf hH.1), hUtU, Matrix.one_mul, Matrix.mul_one]
  have h2 : ((t • H) * X).trace = ((orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1 *
      ((orthoOf hH.1)ᵀ * X * orthoOf hH.1)).trace := by
    have : (orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1 * ((orthoOf hH.1)ᵀ * X * orthoOf hH.1) =
        (orthoOf hH.1)ᵀ * ((t • H) * X) * orthoOf hH.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (orthoOf hH.1) (orthoOf hH.1)ᵀ, hUU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  rw [h1, h2, hconjH, hconjX, Matrix.smul_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_smul,
    Matrix.trace_diagonal, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : t * hH.1.eigenvalues i + γ ≠ 0 := by
    have := hH.eigenvalues_pos i
    positivity
  rw [smul_eq_mul]
  field_simp

/-- **The centred localised LLC in the eigenbasis**: `t⟨½wᵀHw⟩ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)`. -/
theorem localised_llc_centred_eigen {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) :
    t * tiltedExpectation (t • H + γ • 1) 0 (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      (1 / 2) * ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) := by
  have h := localised_llc hH ht hγ (0 : ι → ℝ)
  rw [tiltMean_zero, zero_dotProduct, mul_zero, add_zero, smul_zero] at h
  rw [h, sum_mul_effectivePrecision_inv_eq hH ht hγ]

/-- Along an eigenvector `u` of `H` with eigenvalue `λ`, the localised variance is
`‖u‖²/(tλ + γ)`. -/
theorem eigen_direction_variance {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) {u : ι → ℝ} {lam : ℝ} (hu : H *ᵥ u = lam • u) (hlam : 0 < lam) :
    u ⬝ᵥ (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ u = (u ⬝ᵥ u) / (t * lam + γ) := by
  have hP := effectivePrecision_posDef hH ht hγ
  have hne : t * lam + γ ≠ 0 := by positivity
  have hPu : (t • H + γ • (1 : Matrix ι ι ℝ)) *ᵥ u = (t * lam + γ) • u := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hu,
      smul_smul, add_smul]
  have hinv : (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ u = (t * lam + γ)⁻¹ • u := by
    have h1 : (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ ((t • H + γ • 1) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP.det_pos.ne'), Matrix.one_mulVec]
    rw [hPu, Matrix.mulVec_smul] at h1
    calc (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ u
        = (t * lam + γ)⁻¹ • ((t * lam + γ) • ((t • H + γ • 1)⁻¹ *ᵥ u)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (t * lam + γ)⁻¹ • u := by rw [h1]
  rw [hinv, dotProduct_smul, smul_eq_mul, div_eq_inv_mul]

/-- The same in the note's relative form: `(‖u‖²/(tλ)) / (1 + γ_rel)`, `γ_rel = γ/(tλ)`. -/
theorem eigen_direction_variance_rel {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) {u : ι → ℝ} {lam : ℝ} (hu : H *ᵥ u = lam • u) (hlam : 0 < lam) :
    u ⬝ᵥ (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ u =
      ((u ⬝ᵥ u) / (t * lam)) / (1 + γ / (t * lam)) := by
  rw [eigen_direction_variance hH ht hγ hu hlam]
  have h1 : t * lam ≠ 0 := by positivity
  have h2 : t * lam + γ ≠ 0 := by positivity
  field_simp

end Eigen

end Laplace.Sampler
