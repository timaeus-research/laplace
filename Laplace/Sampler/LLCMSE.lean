/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.LLCVariance

/-!
# The mean-square error of the pooled LLC estimator (E4)

E4 of the Sanity on Sampling note: the LLC "is within 2% of `d/2` for every budget above `10⁴`
draws in every dimension, the residual being the ULA inflation", and "only very short single
chains miss it, because they have not spread along the flat directions". This file assembles the
three error sources into the mean-square error of the pooled LLC statistic
`LLĈ = t (1/(CN)) ∑_c ∑_{k<N} ½⟨x_c(b+1+k), H x_c(b+1+k)⟩` on the ULA chain for `P = tH`:

* `integral_sub_const_sq_eq`: the bias–variance decomposition `E(X - a)² = Var X + (E X - a)²`;
* `pooledLLC` and its mean `integral_pooledLLC = Λ_h - shortfall`, with `Λ_h = ½ ∑ᵢ 1/(1 - h pᵢ/2)`
  the ULA LLC and `shortfall = ½ ∑ᵢ (R₂ᵢ/N)/(1 - h pᵢ/2)` the burn-in shortfall
  (`R₂ᵢ = ∑_{k<N} ρᵢ^{2(b+1+k)}`, `ρᵢ = 1 - h pᵢ`);
* `llc_mse_ula`, `llc_mse_ula_le`: `E(LLĈ - Λ_h)² = Var + shortfall² ≤ envelope + shortfall_bd²`;
* `llc_mse_half_dim`, `llc_mse_half_dim_le`: `E(LLĈ - d/2)² = Var + (inflation - shortfall)²`,
  `inflation = Λ_h - d/2 = ½ ∑ᵢ (h pᵢ/2)/(1 - h pᵢ/2)`;
* `llc_rms_le`, `llc_rel_rms_le`: **the three error sources**,
  `√E(LLĈ - d/2)² ≤ √envelope + inflation + shortfall_bd`: Monte Carlo `O(√(d/(CN)))`,
  discretisation `O(h pmax)`, burn-in `O(ρ_max^{2(b+1)}/N)`; and the same divided by `d/2`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Laplace.Sampler

section Scalar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Bias–variance decomposition**: `∫ (X - a)² = (∫ X² - (∫ X)²) + (∫ X - a)²`. -/
theorem integral_sub_const_sq_eq {X : Ω → ℝ} (h1 : Integrable X P)
    (h2 : Integrable (fun ω => X ω ^ 2) P) (a : ℝ) :
    ∫ ω, (X ω - a) ^ 2 ∂P =
      (∫ ω, X ω ^ 2 ∂P - (∫ ω, X ω ∂P) ^ 2) + (∫ ω, X ω ∂P - a) ^ 2 := by
  have hexp : ∀ ω, (X ω - a) ^ 2 = X ω ^ 2 - 2 * a * X ω + a ^ 2 := fun ω => by ring
  simp_rw [hexp]
  have hA : Integrable (fun ω => X ω ^ 2 - 2 * a * X ω) P := h2.sub (h1.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub h2 (h1.const_mul _), integral_const_mul,
    integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

/-- `√(a + b²) ≤ √a + b` for `a, b ≥ 0`. -/
theorem sqrt_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b ^ 2) ≤ Real.sqrt a + b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg a) hb]

end Scalar

section Chain

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Joint independence of the noise across chains and times gives independence along each
chain. -/
theorem iIndepFun_chain {C : ℕ} {ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι}
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (c : Fin C) : iIndepFun (ξ c) P := by
  have h := iIndepFun.precomp (Prod.mk_right_injective c) hind
  exact h

end Chain

section Statistic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}

/-- The pooled loss-based LLC statistic of `C` ULA chains from the mode, draws `b+1, …, b+N`:
`t (1/(CN)) ∑_c ∑_{k<N} ½⟨x_c(b+1+k), H x_c(b+1+k)⟩`. -/
noncomputable def pooledLLC (H : Matrix ι ι ℝ) (t h : ℝ) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) (ω : Ω) : ℝ :=
  t * ((1 / ((C : ℝ) * N)) * ∑ c, ∑ k ∈ range N, 1 / 2 *
    inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)
      (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + k) ω)))

/-- `pooledLLC` as the weighted diagonal statistic `∑ᵢ (pᵢ/2) Σ̂ᵢᵢ` of the eigen-projections. -/
theorem pooledLLC_eq {H : Matrix ι ι ℝ} {t : ℝ} (h : ℝ) (ht : 0 < t) (hP : (t • H).PosDef) {C : ℕ}
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (N b : ℕ) :
    pooledLLC H t h ξ N b = fun ω => ∑ i, hP.1.eigenvalues i / 2 *
      pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hP.1 i) (ulaChain (t • H) h (ξ c) k ω))
        N b i i ω :=
  funext fun ω =>
    llc_statistic_eq_weighted_diag ht hP N b (fun c k => ulaChain (t • H) h (ξ c) k) ω

end Statistic

section Integrability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The eigen-projections of the ULA chain are in `L⁴`. -/
theorem memLp_four_inner_ulaChain {H : Matrix ι ι ℝ} {t h : ℝ} (hh : 0 ≤ h)
    (hP : (t • H).PosDef) {C : ℕ} (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (c : Fin C) (i : ι) (k : ℕ) :
    MemLp (fun ω => inner ℝ (orthoCol hP.1 i) (ulaChain (t • H) h (ξ c) k ω)) 4 P := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hx : (fun ω => inner ℝ (orthoCol hP.1 i) (ulaChain (t • H) h (ξ c) k ω)) =
      realChain (1 - h * hP.1.eigenvalues i)
        (fun m => projNoise h (orthoCol hP.1 i) (ξ c) m) k := by
    funext ω
    exact inner_ulaChain_eq_realChain hPt h (mulVec_orthoCol hP.1 i) (ξ c) k ω
  rw [hx]
  exact memLp_of_isLinComb
    (fourthMomentTable_projNoise_dir hh (orthonormal_orthoCol hP.1) ξ hmeas hlaw hind).memLp
    (isLinComb_realChain_dir _ (fun c k i => projNoise h (orthoCol hP.1 i) (ξ c) k) c i k k le_rfl)

omit [DecidableEq ι] [IsProbabilityMeasure P] in
theorem integrable_weighted_diag_sq {C : ℕ} {x : Fin C → ι → ℕ → Ω → ℝ} {N b : ℕ}
    (hL4 : ∀ c i k, k ∈ range N → MemLp (x c i (b + 1 + k)) 4 P) (w : ι → ℝ) :
    Integrable (fun ω => (∑ i, w i * pooledSecondMoment x N b i i ω) ^ 2) P := by
  have hsq : ∀ ω, (∑ i, w i * pooledSecondMoment x N b i i ω) ^ 2 =
      ∑ i, ∑ j, (w i * w j) *
        (pooledSecondMoment x N b i i ω * pooledSecondMoment x N b j j ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hsq]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_pooledSecondMoment_mul hL4 i i j j).const_mul _

theorem integrable_pooledLLC {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h)
    (hP : (t • H).PosDef) {C : ℕ} (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (N b : ℕ) :
    Integrable (pooledLLC H t h ξ N b) P := by
  rw [pooledLLC_eq h ht hP ξ N b]
  exact integrable_finsetSum _ fun i _ => (integrable_pooledSecondMoment
    (fun c i k _ => memLp_four_inner_ulaChain hh hP ξ hmeas hlaw hind c i (b + 1 + k))
    i i).const_mul _

omit [IsProbabilityMeasure P] in
theorem integrable_pooledLLC_sq {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h)
    (hP : (t • H).PosDef) {C : ℕ} (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) (N b : ℕ) :
    Integrable (fun ω => pooledLLC H t h ξ N b ω ^ 2) P := by
  rw [pooledLLC_eq h ht hP ξ N b]
  exact integrable_weighted_diag_sq
    (fun c i k _ => memLp_four_inner_ulaChain hh hP ξ hmeas hlaw hind c i (b + 1 + k)) _

end Integrability

section Algebra

variable {ι : Type*} [Fintype ι]

/-- **The burn-in shortfall is nonnegative and bounded**:
`0 ≤ ½ ∑ᵢ (R₂ᵢ/N)/(1 - h pᵢ/2) ≤ ½ ∑ᵢ ρᵢ^{2(b+1)}/(N(1 - ρᵢ²)(1 - h pᵢ/2))` for `0 < h pᵢ ≤ 1`. -/
theorem shortfall_bounds {p : ι → ℝ} {h : ℝ} (hh : 0 < h) (hp : ∀ i, 0 < p i)
    (hstab : ∀ i, h * p i ≤ 1) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    (0 : ℝ) ≤ 1 / 2 * ∑ i, (∑ k ∈ range N, (1 - h * p i) ^ (2 * (b + 1 + k))) / (N : ℝ) /
        (1 - h * p i / 2) ∧
      1 / 2 * ∑ i, (∑ k ∈ range N, (1 - h * p i) ^ (2 * (b + 1 + k))) / (N : ℝ) /
          (1 - h * p i / 2) ≤
        1 / 2 * ∑ i, (1 - h * p i) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    have hρ0 : 0 ≤ 1 - h * p i := by linarith [hstab i]
    have hq : 0 < 1 - h * p i / 2 := by linarith [hstab i]
    exact div_nonneg (div_nonneg (Finset.sum_nonneg fun k _ => pow_nonneg hρ0 _) hN'.le) hq.le
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
    have hρ0 : 0 ≤ 1 - h * p i := by linarith [hstab i]
    have hρ1 : 1 - h * p i < 1 := by linarith [mul_pos hh (hp i)]
    have hρ2 : (1 - h * p i) ^ 2 < 1 := by nlinarith
    have hq : 0 < 1 - h * p i / 2 := by linarith [hstab i]
    have h1ρ : 0 < 1 - (1 - h * p i) ^ 2 := by linarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hs := sum_pow_two_mul_le' hρ2 b N
    have hkey : (∑ k ∈ range N, (1 - h * p i) ^ (2 * (b + 1 + k))) * (1 - (1 - h * p i) ^ 2) ≤
        (1 - h * p i) ^ (2 * (b + 1)) := by
      rwa [le_div_iff₀ h1ρ] at hs
    nlinarith [mul_le_mul_of_nonneg_right hkey (mul_nonneg hN'.le hq.le)]

/-- **The ULA inflation**: `Λ_h - d/2 = ½ ∑ᵢ (h pᵢ/2)/(1 - h pᵢ/2)`, nonnegative for
`0 ≤ h pᵢ < 2`. -/
theorem ula_inflation {p : ι → ℝ} {h : ℝ} (hh : 0 ≤ h) (hp : ∀ i, 0 ≤ p i)
    (hev : ∀ i, h * p i < 2) :
    1 / 2 * ∑ i, 1 / (1 - h * p i / 2) - Fintype.card ι / 2 =
        1 / 2 * ∑ i, (h * p i / 2) / (1 - h * p i / 2) ∧
      0 ≤ 1 / 2 * ∑ i, (h * p i / 2) / (1 - h * p i / 2) := by
  refine ⟨?_, ?_⟩
  · rw [sum_one_div_one_sub_eq (fun i => h * p i / 2) (fun i => by have := hev i; linarith)]
    ring
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => div_nonneg ?_ ?_)
    · exact div_nonneg (mul_nonneg hh (hp i)) (by norm_num)
    · linarith [hev i]

end Algebra

section ULA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The mean of the pooled LLC** is the ULA LLC minus the burn-in shortfall:
`E LLĈ = ½ ∑ᵢ 1/(1 - h pᵢ/2) - ½ ∑ᵢ (R₂ᵢ/N)/(1 - h pᵢ/2)`. -/
theorem integral_pooledLLC {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, pooledLLC H t h ξ N b ω ∂P =
      1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) -
        1 / 2 * ∑ i, (∑ k ∈ range N, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1 + k))) / N /
          (1 - h * hP.1.eigenvalues i / 2) := by
  unfold pooledLLC
  rw [integral_const_mul,
    integral_llc_running_mean ht hh hP hev hC hN b ξ hmeas hlaw (iIndepFun_chain hind),
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : 1 - h * hP.1.eigenvalues i / 2 ≠ 0 := by have := hev i; linarith
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **MSE against the ULA LLC, exact**: `E(LLĈ - Λ_h)² = Var LLĈ + shortfall²`. -/
theorem llc_mse_ula {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, (pooledLLC H t h ξ N b ω - 1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) ^ 2 ∂P =
      (∫ ω, pooledLLC H t h ξ N b ω ^ 2 ∂P - (∫ ω, pooledLLC H t h ξ N b ω ∂P) ^ 2) +
        (1 / 2 * ∑ i, (∑ k ∈ range N, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1 + k))) / N /
          (1 - h * hP.1.eigenvalues i / 2)) ^ 2 := by
  rw [integral_sub_const_sq_eq (integrable_pooledLLC ht hh.le hP ξ hmeas hlaw hind N b)
    (integrable_pooledLLC_sq ht hh.le hP ξ hmeas hlaw hind N b)]
  congr 1
  rw [integral_pooledLLC ht hh hP hev hC hN b ξ hmeas hlaw hind]
  ring

/-- **MSE against the ULA LLC, bounded**: for `0 < h pᵢ ≤ 1`,
`E(LLĈ - Λ_h)² ≤ 1/(2CN) ∑ᵢ (1 + ρᵢ²)/((1 - ρᵢ²)(1 - h pᵢ/2)²)
  + (½ ∑ᵢ ρᵢ^{2(b+1)}/(N(1 - ρᵢ²)(1 - h pᵢ/2)))²`. -/
theorem llc_mse_ula_le {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hstab : ∀ i, h * hP.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ((pooledLLC H t h ξ N b ω - 1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) ^ 2 : ℝ)
        ∂P ≤
      1 / (2 * C * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
          ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2) +
        (1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2))) ^ 2 := by
  have hev : ∀ i, h * hP.1.eigenvalues i < 2 := fun i => by linarith [hstab i]
  obtain ⟨hs0, hs1⟩ := shortfall_bounds hh hP.eigenvalues_pos hstab hN (p := hP.1.eigenvalues) b
  refine (llc_mse_ula ht hh hP hev hC hN b ξ hmeas hlaw hind).trans_le ?_
  exact add_le_add (variance_llc_ula_le ht hh hP hstab hC hN b ξ hmeas hlaw hind)
    (pow_le_pow_left₀ hs0 hs1 2)

/-- **MSE against the true LLC `d/2`, exact**:
`E(LLĈ - d/2)² = Var LLĈ + (inflation - shortfall)²`. -/
theorem llc_mse_half_dim {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, (pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 ∂P =
      (∫ ω, pooledLLC H t h ξ N b ω ^ 2 ∂P - (∫ ω, pooledLLC H t h ξ N b ω ∂P) ^ 2) +
        (1 / 2 * ∑ i, (h * hP.1.eigenvalues i / 2) / (1 - h * hP.1.eigenvalues i / 2) -
          1 / 2 * ∑ i, (∑ k ∈ range N, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1 + k))) / N /
            (1 - h * hP.1.eigenvalues i / 2)) ^ 2 := by
  rw [integral_sub_const_sq_eq (integrable_pooledLLC ht hh.le hP ξ hmeas hlaw hind N b)
    (integrable_pooledLLC_sq ht hh.le hP ξ hmeas hlaw hind N b)]
  congr 1
  rw [integral_pooledLLC ht hh hP hev hC hN b ξ hmeas hlaw hind,
    ← (ula_inflation hh.le (fun i => (hP.eigenvalues_pos i).le) hev).1]
  ring

/-- **MSE against `d/2`, bounded**: for `0 < h pᵢ ≤ 1`,
`E(LLĈ - d/2)² ≤ envelope + (inflation + shortfall_bd)²`. -/
theorem llc_mse_half_dim_le {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hstab : ∀ i, h * hP.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ((pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 : ℝ) ∂P ≤
      1 / (2 * C * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
          ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2) +
        (1 / 2 * ∑ i, (h * hP.1.eigenvalues i / 2) / (1 - h * hP.1.eigenvalues i / 2) +
          1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
            (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)))
          ^ 2 := by
  have hev : ∀ i, h * hP.1.eigenvalues i < 2 := fun i => by linarith [hstab i]
  obtain ⟨hs0, hs1⟩ := shortfall_bounds hh hP.eigenvalues_pos hstab hN (p := hP.1.eigenvalues) b
  have hinfl := (ula_inflation hh.le (fun i => (hP.eigenvalues_pos i).le) hev).2
  refine (llc_mse_half_dim ht hh hP hev hC hN b ξ hmeas hlaw hind).trans_le ?_
  refine add_le_add (variance_llc_ula_le ht hh hP hstab hC hN b ξ hmeas hlaw hind) ?_
  exact sq_le_sq' (by linarith) (by linarith)

/-- **The three error sources of the LLC** (RMS form): for `0 < h pᵢ ≤ 1`,
`√E(LLĈ - d/2)² ≤ √(1/(2CN) ∑ᵢ (1+ρᵢ²)/((1-ρᵢ²)(1-h pᵢ/2)²))
  + ½ ∑ᵢ (h pᵢ/2)/(1-h pᵢ/2) + ½ ∑ᵢ ρᵢ^{2(b+1)}/(N(1-ρᵢ²)(1-h pᵢ/2))`:
Monte Carlo `O(√(d/(CN)))`, ULA inflation `O(h pmax)`, burn-in shortfall `O(ρ_max^{2(b+1)}/N)`. -/
theorem llc_rms_le {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hstab : ∀ i, h * hP.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Real.sqrt (∫ ω, ((pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 : ℝ) ∂P) ≤
      Real.sqrt (1 / (2 * C * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
          ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2)) +
        1 / 2 * ∑ i, (h * hP.1.eigenvalues i / 2) / (1 - h * hP.1.eigenvalues i / 2) +
        1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)) := by
  have hev : ∀ i, h * hP.1.eigenvalues i < 2 := fun i => by linarith [hstab i]
  obtain ⟨hs0, hs1⟩ := shortfall_bounds hh hP.eigenvalues_pos hstab hN (p := hP.1.eigenvalues) b
  have hinfl := (ula_inflation hh.le (fun i => (hP.eigenvalues_pos i).le) hev).2
  have henv : 0 ≤ 1 / (2 * (C : ℝ) * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
      ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    have hρ0 : 0 ≤ 1 - h * hP.1.eigenvalues i := by linarith [hstab i]
    have hρ1 : 1 - h * hP.1.eigenvalues i < 1 := by
      linarith [mul_pos hh (hP.eigenvalues_pos i)]
    have h1ρ : 0 < 1 - (1 - h * hP.1.eigenvalues i) ^ 2 := by nlinarith
    positivity
  rw [add_assoc]
  refine le_trans (Real.sqrt_le_sqrt (llc_mse_half_dim_le ht hh hP hstab hC hN b ξ hmeas hlaw hind))
    (sqrt_add_sq_le henv (by linarith))

/-- **The relative RMS error of the LLC**: for `0 < h pᵢ ≤ 1` and `d = |ι| > 0`,
`√E(LLĈ - d/2)² / (d/2) ≤ 2√envelope/d + (1/d) ∑ᵢ (h pᵢ/2)/(1-h pᵢ/2)
  + (1/(dN)) ∑ᵢ ρᵢ^{2(b+1)}/((1-ρᵢ²)(1-h pᵢ/2))`. -/
theorem llc_rel_rms_le [Nonempty ι] {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hstab : ∀ i, h * hP.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Real.sqrt (∫ ω, ((pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 : ℝ) ∂P) /
        (Fintype.card ι / 2) ≤
      2 * Real.sqrt (1 / (2 * C * N) * ∑ i, (1 + (1 - h * hP.1.eigenvalues i) ^ 2) /
          ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2) ^ 2)) /
          Fintype.card ι +
        (1 / Fintype.card ι) *
          ∑ i, (h * hP.1.eigenvalues i / 2) / (1 - h * hP.1.eigenvalues i / 2) +
        (1 / (Fintype.card ι * N)) * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
          ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hrms := llc_rms_le ht hh hP hstab hC hN b ξ hmeas hlaw hind
  rw [div_le_iff₀ (by positivity)]
  refine le_trans hrms (le_of_eq ?_)
  have hsum : ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
      (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)) =
      (1 / (N : ℝ)) * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
        ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div_mul_eq_div, div_div]
    congr 1
    ring
  rw [hsum]
  field_simp

end ULA

end Laplace.Sampler
