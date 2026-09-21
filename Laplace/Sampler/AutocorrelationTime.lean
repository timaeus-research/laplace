/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FrobeniusLaw
import Laplace.Sampler.LLCClosures

/-!
# The integrated autocorrelation time of the AR(1) eigen-chain (Setup, E1)

The Sanity on Sampling note: "Along direction `i` the chain is an AR(1) process with coefficient
`ρᵢ = 1 − lr pᵢ`, so its integrated autocorrelation time is `τᵢ = (1 + ρᵢ)/(1 − ρᵢ) ≈ 2/(lr pᵢ)`:
stiff directions decorrelate in a few steps, the flattest in `τ_flat = 2/(lr pmin)` steps, which
for a condition number `κ` and `lr pmax = 0.1` is `20κ` steps."

* `toeplitz_sum_eq`: `∑_{k,l<N} ρ^{|k−l|} = N(1+ρ)/(1−ρ) − 2ρ(1−ρ^N)/(1−ρ)²` (closed form of the
  Toeplitz sum, refining `toeplitz_sum_le`);
* `variance_running_mean_realChain`: for the zero-start AR(1) chain with white mean-zero
  innovations of variance `v`, the running mean `x̄_N = (1/N) ∑_{k<N} x_{b+1+k}` has
  `Var x̄_N = (v/(1−ρ²))/N² (∑_{k,l<N} ρ^{|k−l|} − (∑_{k<N} ρ^{b+1+k})²)`;
* `tendsto_toeplitz_div`, `iat_realChain`: `N · Var x̄_N / s₂ → (1+ρ)/(1−ρ)`: the variance of the
  sample mean is `s₂ τ/N` asymptotically, `τ = (1+ρ)/(1−ρ)` the integrated autocorrelation time
  (the zero-start transient `(∑ ρ^{b+1+k})²/N` vanishes in the limit);
* `iat_eq`, `iat_flat_twenty_kappa`: `(1+ρ)/(1−ρ) = 2/(hp) − 1` for `ρ = 1 − hp`, and
  `τ_flat = 2/(h pmin) − 1 = 20κ − 1` at `h pmax = 1/10`;
* `variance_running_mean_ulaChain`, `iat_ulaChain`: the instance for the eigen-projection of the
  ULA chain with Gaussian noise (`v = 2h`, `ρ = 1 − hp`, `s₂ = 1/(p(1 − hp/2))`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Matrix

namespace Laplace.Sampler

/-! ### The Toeplitz sum in closed form -/

section Toeplitz

/-- `∑_{m<N} (N − m − 1) ρ^{m+1} = ρ (N(1−ρ) − (1 − ρ^N))/(1−ρ)²`. -/
theorem sum_range_sub_mul_pow_eq {ρ : ℝ} (hρ : ρ ≠ 1) (N : ℕ) :
    ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * ρ ^ (m + 1) =
      ρ * (N * (1 - ρ) - (1 - ρ ^ N)) / (1 - ρ) ^ 2 := by
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hsplit : ∀ m ∈ range n, (((n + 1 : ℕ) : ℝ) - (m + 1)) * ρ ^ (m + 1) =
        ((n : ℝ) - (m + 1)) * ρ ^ (m + 1) + ρ ^ (m + 1) := fun m _ => by
      push_cast
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ih]
    have hgeom : ∑ m ∈ range n, ρ ^ (m + 1) = ρ * ((ρ ^ n - 1) / (ρ - 1)) := by
      simp_rw [pow_succ]
      rw [← Finset.sum_mul, geom_sum_eq hρ n]
      ring
    rw [hgeom]
    push_cast
    field_simp
    ring

/-- **The Toeplitz sum in closed form**:
`∑_{k,l<N} ρ^{|k−l|} = N(1+ρ)/(1−ρ) − 2ρ(1−ρ^N)/(1−ρ)²`. -/
theorem toeplitz_sum_eq {ρ : ℝ} (hρ : ρ ≠ 1) (N : ℕ) :
    ∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l =
      N * (1 + ρ) / (1 - ρ) - 2 * ρ * (1 - ρ ^ N) / (1 - ρ) ^ 2 := by
  rw [sum_sum_pow_dist, sum_range_sub_mul_pow_eq hρ]
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  field_simp
  ring

/-- `(∑_{k,l<N} ρ^{|k−l|})/N → (1+ρ)/(1−ρ)`: the integrated autocorrelation time of a stationary
AR(1) sequence with coefficient `0 ≤ ρ < 1`. -/
theorem tendsto_toeplitz_div {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l) / N) atTop
      (𝓝 ((1 + ρ) / (1 - ρ))) := by
  have hρ : ρ ≠ 1 := hρ1.ne
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have heq : ∀ N : ℕ, N ≠ 0 → (∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l) / N =
      (1 + ρ) / (1 - ρ) - 2 * ρ / (1 - ρ) ^ 2 * ((1 - ρ ^ N) / N) := by
    intro N hN
    rw [toeplitz_sum_eq hρ]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
  have h2 : Tendsto (fun N : ℕ => (1 - ρ ^ N) / (N : ℝ)) atTop (𝓝 0) := by
    have ha : Tendsto (fun N : ℕ => 1 - ρ ^ N) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
    have hb : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using ha.mul hb
  have hlim : Tendsto (fun N : ℕ => (1 + ρ) / (1 - ρ) - 2 * ρ / (1 - ρ) ^ 2 * ((1 - ρ ^ N) / N))
      atTop (𝓝 ((1 + ρ) / (1 - ρ))) := by
    simpa using
      (tendsto_const_nhds (x := (1 + ρ) / (1 - ρ))).sub (h2.const_mul (2 * ρ / (1 - ρ) ^ 2))
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun N hN => (heq N (by omega)).symm⟩)

/-- `τ = (1+ρ)/(1−ρ) = 2/(hp) − 1` for `ρ = 1 − hp`: the note's "`≈ 2/(lr p)`" is exact up to
`−1`. -/
theorem iat_eq {h p : ℝ} (hhp : h * p ≠ 0) :
    (1 + (1 - h * p)) / (1 - (1 - h * p)) = 2 / (h * p) - 1 := by
  have hh : h ≠ 0 := left_ne_zero_of_mul hhp
  have hp : p ≠ 0 := right_ne_zero_of_mul hhp
  field_simp
  ring

/-- `τ_flat = 2/(h pmin) − 1 = 20κ − 1` at `h pmax = 1/10`, `κ = pmax/pmin`. -/
theorem iat_flat_twenty_kappa {h pmax κ pmin : ℝ} (hh : h * pmax = 1 / 10) (hκ : pmin = pmax / κ)
    (hpmax : pmax ≠ 0) :
    2 / (h * pmin) - 1 = 20 * κ - 1 := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hh
  subst hκ
  have : h = 1 / (10 * pmax) := by field_simp; linarith
  subst this
  field_simp
  ring

/-- **E1's flattest direction**: at `κ = 1000` and `h pmax = 1/100`,
`τ_flat = 2/(h pmin) − 1 = 199 999` (the note's "`2 × 10⁵` steps against 50 000 draws"). -/
theorem iat_flat_e1 {h pmax pmin : ℝ} (hh : h * pmax = 1 / 100) (hκ : pmin = pmax / 1000)
    (hpmax : pmax ≠ 0) :
    2 / (h * pmin) - 1 = 199999 := by
  subst hκ
  have : h = 1 / (100 * pmax) := by field_simp; linarith
  subst this
  field_simp
  ring

end Toeplitz

/-! ### The running mean of the zero-start chain -/

section RealChain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The zero-start chain has mean zero when its innovations do. -/
theorem integral_realChain_eq_zero (ρ : ℝ) {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P)
    (hmean : ∀ k, ∫ ω, η k ω ∂P = 0) (k : ℕ) : ∫ ω, realChain ρ η k ω ∂P = 0 := by
  induction k with
  | zero => simp [realChain_zero]
  | succ k ih =>
    rw [realChain_succ, integral_add (((memLp_realChain ρ hη k).integrable one_le_two).const_mul ρ)
      ((hη (k + 1)).integrable one_le_two), integral_const_mul, ih, hmean, mul_zero, add_zero]

/-- **The variance of the running mean of the zero-start AR(1) chain** over the draws
`b+1, …, b+N`, for white mean-zero innovations of variance `v`:
`Var x̄_N = (v/(1−ρ²))/N² (∑_{k,l<N} ρ^{|k−l|} − (∑_{k<N} ρ^{b+1+k})²)`. -/
theorem variance_running_mean_realChain (ρ : ℝ) (hρ : ρ ^ 2 ≠ 1) {v : ℝ} {η : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hmean : ∀ k, ∫ ω, η k ω ∂P = 0)
    (hwhite : ∀ j k, ∫ ω, η j ω * η k ω ∂P = if j = k then v else 0) (N b : ℕ) :
    ∫ ω, ((1 / (N : ℝ)) * ∑ k ∈ range N, realChain ρ η (b + 1 + k) ω) ^ 2 ∂P -
        (∫ ω, (1 / (N : ℝ)) * ∑ k ∈ range N, realChain ρ η (b + 1 + k) ω ∂P) ^ 2 =
      v / (1 - ρ ^ 2) / N ^ 2 *
        (∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l -
          (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2) := by
  have hgram : ∀ k l, ∫ ω, realChain ρ η k ω * realChain ρ η l ω ∂P =
      v / (1 - ρ ^ 2) * (ρ ^ Nat.dist k l - ρ ^ (k + l)) := by
    intro k l
    have hw : ∀ c c' : Fin 1, ∀ j k,
        ∫ ω, (fun _ : Fin 1 => η) c j ω * (fun _ : Fin 1 => η) c' k ω ∂P =
          if c = c' ∧ j = k then v else 0 := by
      intro c c' j k
      have hcc : c = c' := Subsingleton.elim c c'
      subst hcc
      simp [hwhite j k]
    have := integral_realChain_mul_realChain (C := 1) ρ hρ (fun _ => η) (fun _ k => hη k) hw
      0 0 k l
    simpa using this
  rw [variance_sum_eq_sum_cov (range N) (fun k ω => realChain ρ η (b + 1 + k) ω)
    (fun k _ => (memLp_realChain ρ hη _).integrable one_le_two)
    (fun k _ l _ => (memLp_realChain ρ hη _).integrable_mul (memLp_realChain ρ hη _)) (1 / N)]
  simp_rw [integral_realChain_eq_zero ρ hη hmean, mul_zero, sub_zero, hgram]
  have hdist : ∀ k l, Nat.dist (b + 1 + k) (b + 1 + l) = Nat.dist k l := fun k l => by
    unfold Nat.dist
    omega
  rw [show (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2 =
      ∑ k ∈ range N, ∑ l ∈ range N, ρ ^ (b + 1 + k) * ρ ^ (b + 1 + l) by
    rw [sq, Finset.sum_mul_sum]]
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hdist, pow_add ρ (b + 1 + k) (b + 1 + l)]
  ring

/-- **The integrated autocorrelation time of the zero-start AR(1) chain**:
`N · Var x̄_N / s₂ → (1+ρ)/(1−ρ)`, `s₂ = v/(1−ρ²)`, for `0 ≤ ρ < 1`, `v > 0`. -/
theorem iat_realChain {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v : ℝ} (hv : 0 < v) {η : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hmean : ∀ k, ∫ ω, η k ω ∂P = 0)
    (hwhite : ∀ j k, ∫ ω, η j ω * η k ω ∂P = if j = k then v else 0) (b : ℕ) :
    Tendsto (fun N : ℕ => N *
        (∫ ω, ((1 / (N : ℝ)) * ∑ k ∈ range N, realChain ρ η (b + 1 + k) ω) ^ 2 ∂P -
        (∫ ω, (1 / (N : ℝ)) * ∑ k ∈ range N, realChain ρ η (b + 1 + k) ω ∂P) ^ 2) /
        (v / (1 - ρ ^ 2))) atTop (𝓝 ((1 + ρ) / (1 - ρ))) := by
  have hρ2 : ρ ^ 2 ≠ 1 := by nlinarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hs₂ : 0 < v / (1 - ρ ^ 2) := div_pos hv (by nlinarith)
  simp_rw [variance_running_mean_realChain ρ hρ2 hη hmean hwhite]
  have heq : ∀ N : ℕ, N ≠ 0 →
      (N : ℝ) * (v / (1 - ρ ^ 2) / N ^ 2 *
        (∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l - (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2)) /
        (v / (1 - ρ ^ 2)) =
      (∑ k ∈ range N, ∑ l ∈ range N, ρ ^ Nat.dist k l) / N -
        (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2 / N := by
    intro N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
  have hG : ∀ N : ℕ, (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2 / N ≤
      (ρ ^ (b + 1) / (1 - ρ)) ^ 2 / N := by
    intro N
    have hsum : ∑ k ∈ range N, ρ ^ (b + 1 + k) ≤ ρ ^ (b + 1) / (1 - ρ) := by
      simp_rw [pow_add ρ (b + 1), ← Finset.mul_sum]
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (geom_sum_le_one_div hρ0 hρ1 N) (pow_nonneg hρ0 _)
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hρ0 _) hsum 2) (Nat.cast_nonneg N)
  have hG0 : ∀ N : ℕ, 0 ≤ (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2 / N := fun N => by positivity
  have hG2 : Tendsto (fun N : ℕ => (∑ k ∈ range N, ρ ^ (b + 1 + k)) ^ 2 / (N : ℝ)) atTop (𝓝 0) :=
    squeeze_zero hG0 hG (tendsto_const_div_atTop_nhds_zero_nat _)
  have hlim := (tendsto_toeplitz_div hρ0 hρ1).sub hG2
  rw [sub_zero] at hlim
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun N hN => (heq N (by omega)).symm⟩)

end RealChain

/-! ### The ULA eigen-chain -/

section ULA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The variance of the running mean of an eigen-projection of the ULA chain** with Gaussian
noise: `v = 2h`, `ρ = 1 − hp`. -/
theorem variance_running_mean_ulaChain {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 ≤ h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u = p • u) (hnorm : ‖u‖ = 1)
    (hρ : (1 - h * p) ^ 2 ≠ 1) (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (hind : iIndepFun ξ P) (N b : ℕ) :
    ∫ ω, ((1 / (N : ℝ)) * ∑ k ∈ range N, inner ℝ u (ulaChain Q h ξ (b + 1 + k) ω)) ^ 2 ∂P -
        (∫ ω, (1 / (N : ℝ)) * ∑ k ∈ range N, inner ℝ u (ulaChain Q h ξ (b + 1 + k) ω) ∂P) ^ 2 =
      2 * h / (1 - (1 - h * p) ^ 2) / N ^ 2 *
        (∑ k ∈ range N, ∑ l ∈ range N, (1 - h * p) ^ Nat.dist k l -
          (∑ k ∈ range N, (1 - h * p) ^ (b + 1 + k)) ^ 2) := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu ξ]
  exact variance_running_mean_realChain (1 - h * p) hρ (memLp_projNoise h u ξ hmeas hlaw)
    (integral_projNoise h u ξ hmeas hlaw)
    (fun j k => by rw [integral_projNoise_mul hh u ξ hmeas hlaw hind j k, hnorm, one_pow, mul_one])
    N b

/-- **The integrated autocorrelation time of the ULA eigen-chain**: for `0 < hp ≤ 1`,
`N · Var(⟨u, x̄_N⟩) / (2h/(1 − (1−hp)²)) → (1 + (1−hp))/(1 − (1−hp)) = 2/(hp) − 1`. -/
theorem iat_ulaChain {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 < h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u = p • u) (hnorm : ‖u‖ = 1) (hp : 0 < p)
    (hstab : h * p ≤ 1) (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (hind : iIndepFun ξ P) (b : ℕ) :
    Tendsto (fun N : ℕ => N *
        (∫ ω, ((1 / (N : ℝ)) * ∑ k ∈ range N, inner ℝ u (ulaChain Q h ξ (b + 1 + k) ω)) ^ 2 ∂P -
          (∫ ω, (1 / (N : ℝ)) * ∑ k ∈ range N, inner ℝ u (ulaChain Q h ξ (b + 1 + k) ω) ∂P) ^ 2) /
        (2 * h / (1 - (1 - h * p) ^ 2))) atTop (𝓝 (2 / (h * p) - 1)) := by
  have hρ0 : 0 ≤ 1 - h * p := by linarith
  have hρ1 : 1 - h * p < 1 := by linarith [mul_pos hh hp]
  rw [← iat_eq (mul_pos hh hp).ne']
  simp_rw [inner_ulaChain_eq_realChain hsym h hu ξ]
  exact iat_realChain hρ0 hρ1 (by positivity) (memLp_projNoise h u ξ hmeas hlaw)
    (integral_projNoise h u ξ hmeas hlaw)
    (fun j k => by
      rw [integral_projNoise_mul hh.le u ξ hmeas hlaw hind j k, hnorm, one_pow, mul_one])
    b

end ULA

end Laplace.Sampler
