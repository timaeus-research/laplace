/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.ULA
import Laplace.Sampler.ULAEigen
import Laplace.Sampler.DirectionClosures

/-!
# LLC-side closures: minibatch inflation, the running mean from the mode, and `20κ`

Three statements of the Sanity on Sampling note about the sampler's local learning coefficient
`t ⟨½ wᵀ H w⟩` on a Gaussian target with precision `P = t H`:

* **E8 / conclusion 2** ("the LLC is inflated by about `lr t² tr(C_g)/(2d)`"): with minibatch
  noise `2h • 1 + h² t² • C` the stationary covariance is the Lyapunov solution `minibatchCov`,
  and in the eigenbasis of `P` the LLC is `½ ∑ᵢ (1 + h t² c̃ᵢ/2)/(1 - h pᵢ/2)`, `c̃ᵢ = (Uᵀ C U)ᵢᵢ`
  (`minibatch_llc`). The increment over the ULA LLC is `(h t²/4) ∑ᵢ c̃ᵢ/(1 - h pᵢ/2)`
  (`minibatch_llc_sub_ula_llc`), which for `C` positive semidefinite lies between
  `(h t²/4) tr C` and `(h t²/4) tr C/(1 - h pmax/2)` (`minibatch_inflation_bounds`); the
  remainder over `(h t²/4) tr C` is at most that times `(h pmax/2)/(1 - h pmax/2)`
  (`minibatch_inflation_remainder`). Normalised by the continuous-target LLC `d/2` this is the
  note's `h t² tr C/(2d)` (`minibatch_inflation_normalised`).
* **E4** ("the LLC is far cheaper than the covariance"): for the ULA chain from the mode, the
  expected loss-based LLC at draw `k` is `½ ∑ᵢ (1 - ρᵢ^{2k})/(1 - h pᵢ/2)`
  (`integral_llc_ulaChain`), and the expected pooled running mean over `C` chains and draws
  `b+1, …, b+N` falls short of the ULA LLC by
  `½ ∑ᵢ (∑_{i<N} ρᵢ^{2(b+1+i)})/(N (1 - h pᵢ/2)) ≤ ½ ∑ᵢ ρᵢ^{2(b+1)}/(N (1 - ρᵢ²)(1 - h pᵢ/2))`
  (`llc_running_mean_shortfall`): burn-in only, no `1/(CN)` autocorrelation term, because no
  sample mean is subtracted.
* **`20κ`**: with `h pmax = 1/10` and `pmin = pmax/κ`, the autocorrelation term `2/(h pmin C N)` of
  the finite-chain shortfall bound is `20κ/(CN)` (`two_div_eq_twenty_kappa`,
  `expected_pooled_sample_variance_ula_shortfall_kappa`).
-/

open Matrix Finset MeasureTheory ProbabilityTheory

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### A. The minibatch LLC in the eigenbasis -/

section Minibatch

/-- The stationary covariance of SGLD with minibatch gradient noise `C`: the Lyapunov solution of
`minibatch_fixed_iff`. -/
noncomputable def minibatchCov {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (h t : ℝ)
    (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  lyapunovVia (orthoOf hP) (fun i => 1 - h * hP.eigenvalues i) (minibatchNoise h t C)

/-- **Minibatch trace.** `tr(P Σ_mb) = ∑ᵢ (1 + h t² c̃ᵢ/2)/(1 - h pᵢ/2)` with `c̃ᵢ = (Uᵀ C U)ᵢᵢ`. -/
theorem trace_mul_minibatchCov {P : Matrix ι ι ℝ} (hP : P.PosDef) (h t : ℝ) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (C : Matrix ι ι ℝ) :
    (P * minibatchCov hP.1 h t C).trace =
      ∑ i, (1 + h * t ^ 2 * ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i / 2) /
        (1 - h * hP.1.eigenvalues i / 2) := by
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  have hU' := orthoOf_mul_transpose hP.1
  have h1 : (P * minibatchCov hP.1 h t C).trace =
      (((orthoOf hP.1)ᵀ * P * orthoOf hP.1) *
        ((orthoOf hP.1)ᵀ * minibatchCov hP.1 h t C * orthoOf hP.1)).trace := by
    have : ((orthoOf hP.1)ᵀ * P * orthoOf hP.1) *
        ((orthoOf hP.1)ᵀ * minibatchCov hP.1 h t C * orthoOf hP.1) =
        (orthoOf hP.1)ᵀ * (P * minibatchCov hP.1 h t C) * orthoOf hP.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (orthoOf hP.1) (orthoOf hP.1)ᵀ, hU', Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  rw [h1, orthoOf_transpose_mul_mul hP.1]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [minibatchCov, minibatchCov_conj_diag hP.1 h t hh hev' C i]
  have hp := hP.eigenvalues_pos i
  have hne : 1 - h * hP.1.eigenvalues i / 2 ≠ 0 := by have := hev i; linarith
  field_simp

/-- **The minibatch LLC.** For `P = t • H`,
`t/2 tr(H Σ_mb) = ½ ∑ᵢ (1 + h t² c̃ᵢ/2)/(1 - h pᵢ/2)`. -/
theorem minibatch_llc {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (C : Matrix ι ι ℝ) :
    t / 2 * (H * minibatchCov hP.1 h t C).trace =
      1 / 2 * ∑ i, (1 + h * t ^ 2 * ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i / 2) /
        (1 - h * hP.1.eigenvalues i / 2) := by
  rw [← trace_mul_minibatchCov hP h t hh hev C, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- **The minibatch inflation of the LLC over ULA** is `(h t²/4) ∑ᵢ c̃ᵢ/(1 - h pᵢ/2)`. -/
theorem minibatch_llc_sub_ula_llc {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (C : Matrix ι ι ℝ) :
    t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace =
      h * t ^ 2 / 4 * ∑ i, ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i /
        (1 - h * hP.1.eigenvalues i / 2) := by
  rw [minibatch_llc t h hP hh hev C, ula_llc t h hP hh hev, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : 1 - h * hP.1.eigenvalues i / 2 ≠ 0 := by have := hev i; linarith
  field_simp
  ring

omit [DecidableEq ι] in
/-- The diagonal of `Uᵀ C U` is nonnegative for `C` positive semidefinite. -/
theorem conj_diag_nonneg {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (U : Matrix ι ι ℝ) (i : ι) :
    0 ≤ (Uᵀ * C * U) i i := by
  have := hC.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.diag_nonneg

/-- `∑ᵢ (Uᵀ C U)ᵢᵢ = tr C` for orthogonal `U`. -/
theorem sum_conj_diag (C : Matrix ι ι ℝ) {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1) :
    ∑ i, (Uᵀ * C * U) i i = C.trace := by
  change (Uᵀ * C * U).trace = C.trace
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- **Two-sided bounds on the minibatch inflation**: for `C` positive semidefinite, `pᵢ ≤ pmax` and
`h pmax < 2`, `(h t²/4) tr C ≤ LLC_mb - LLC_ULA ≤ (h t²/4) tr C/(1 - h pmax/2)`. -/
theorem minibatch_inflation_bounds {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h)
    {pmax : ℝ} (hpmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax < 2)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    h * t ^ 2 / 4 * C.trace ≤
        t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace ∧
      t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace ≤
        h * t ^ 2 / 4 * C.trace / (1 - h * pmax / 2) := by
  have hev : ∀ i, h * hP.1.eigenvalues i < 2 := fun i => by
    have := mul_le_mul_of_nonneg_left (hpmax i) hh.le; linarith
  rw [minibatch_llc_sub_ula_llc t h hP hh hev C, ← sum_conj_diag C (orthoOf_mul_transpose hP.1)]
  have hden : ∀ i, 0 < 1 - h * hP.1.eigenvalues i / 2 := fun i => by have := hev i; linarith
  have hdenmax : 0 < 1 - h * pmax / 2 := by linarith
  have hc : ∀ i, 0 ≤ ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i := fun i => conj_diag_nonneg hC _ i
  have hcoef : 0 ≤ h * t ^ 2 / 4 := by positivity
  constructor
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hcoef
    rw [le_div_iff₀ (hden i)]
    have := hc i
    have := mul_pos hh (hP.eigenvalues_pos i)
    nlinarith
  · calc _ ≤ h * t ^ 2 / 4 *
          ∑ i, ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i / (1 - h * pmax / 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hcoef
          refine div_le_div_of_nonneg_left (hc i) hdenmax ?_
          have := mul_le_mul_of_nonneg_left (hpmax i) hh.le
          linarith
      _ = h * t ^ 2 / 4 * (∑ i, ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i) / (1 - h * pmax / 2) := by
          rw [mul_div_assoc (h * t ^ 2 / 4), Finset.sum_div]

/-- **The remainder over the first-order inflation** `L₀ = (h t²/4) tr C`:
`0 ≤ Δ - L₀ ≤ L₀ (h pmax/2)/(1 - h pmax/2)`. -/
theorem minibatch_inflation_remainder {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef)
    (hh : 0 < h) {pmax : ℝ} (hpmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax < 2)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    0 ≤ (t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace) -
        h * t ^ 2 / 4 * C.trace ∧
      (t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace) -
        h * t ^ 2 / 4 * C.trace ≤
        h * t ^ 2 / 4 * C.trace * (h * pmax / 2) / (1 - h * pmax / 2) := by
  obtain ⟨h1, h2⟩ := minibatch_inflation_bounds t h hP hh hpmax hstab hC
  have hdenmax : 0 < 1 - h * pmax / 2 := by linarith
  have hne : 1 - h * pmax / 2 ≠ 0 := hdenmax.ne'
  have hne2 : 2 - h * pmax ≠ 0 := by linarith
  have hsplit : h * t ^ 2 / 4 * C.trace / (1 - h * pmax / 2) =
      h * t ^ 2 / 4 * C.trace + h * t ^ 2 / 4 * C.trace * (h * pmax / 2) / (1 - h * pmax / 2) := by
    field_simp
    ring
  constructor
  · linarith
  · linarith

/-- **The inflation normalised by the continuous-target LLC `d/2`** lies between `h t² tr C/(2d)`
and `h t² tr C/(2d (1 - h pmax/2))`: the note's "inflated by about `lr t² tr(C_g)/(2d)`". -/
theorem minibatch_inflation_normalised {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef)
    (hh : 0 < h) {pmax : ℝ} (hpmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax < 2)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hd : 0 < Fintype.card ι) :
    h * t ^ 2 * C.trace / (2 * Fintype.card ι) ≤
        (t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace) /
          (Fintype.card ι / 2) ∧
      (t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace) /
          (Fintype.card ι / 2) ≤
        h * t ^ 2 * C.trace / (2 * Fintype.card ι * (1 - h * pmax / 2)) := by
  obtain ⟨h1, h2⟩ := minibatch_inflation_bounds t h hP hh hpmax hstab hC
  have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hdenmax : 0 < 1 - h * pmax / 2 := by linarith
  constructor
  · calc h * t ^ 2 * C.trace / (2 * Fintype.card ι)
        = h * t ^ 2 / 4 * C.trace / (Fintype.card ι / 2) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right h1 (by positivity)
  · calc _ ≤ h * t ^ 2 / 4 * C.trace / (1 - h * pmax / 2) / (Fintype.card ι / 2) :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = h * t ^ 2 * C.trace / (2 * Fintype.card ι * (1 - h * pmax / 2)) := by
          field_simp
          ring

end Minibatch

/-! ### B. The loss-based LLC running mean of the ULA chain from the mode -/

section Quadratic

/-- `x ⬝ᵥ P x = ∑ᵢ pᵢ ((Uᵀ x)ᵢ)²` for `P = U diag(p) Uᵀ`. -/
theorem dotProduct_mulVec_eq_sum_eigen {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ P *ᵥ x = ∑ i, hP.eigenvalues i * ((orthoOf hP)ᵀ *ᵥ x) i ^ 2 := by
  have hspec : x ⬝ᵥ P *ᵥ x =
      x ⬝ᵥ (orthoOf hP * diagonal hP.eigenvalues * (orthoOf hP)ᵀ) *ᵥ x := by
    rw [← spectral_real hP]
  rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The quadratic form in the eigenbasis**: `⟨x, P x⟩ = ∑ᵢ pᵢ ⟨uᵢ, x⟩²`, `uᵢ = orthoCol hP i`. -/
theorem inner_euclid_eq_sum_eigen {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (x : EuclideanSpace ℝ ι) :
    inner ℝ x (euclid P x) = ∑ i, hP.eigenvalues i * inner ℝ (orthoCol hP i) x ^ 2 := by
  rw [inner_toEuclideanCLM, dotProduct_mulVec_eq_sum_eigen hP]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, orthoCol, mulVec, dotProduct,
    transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem inner_euclid_smul (t : ℝ) (H : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    inner ℝ x (euclid (t • H) x) = t * inner ℝ x (euclid H x) := by
  rw [inner_toEuclideanCLM, inner_toEuclideanCLM, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The loss `½ ⟨x, H x⟩` in the eigenbasis of `P = t • H`. -/
theorem half_inner_euclid_eq_sum_eigen {H : Matrix ι ι ℝ} {t : ℝ} (ht : 0 < t) (hP : (t • H).PosDef)
    (x : EuclideanSpace ℝ ι) :
    1 / 2 * inner ℝ x (euclid H x) =
      ∑ i, 1 / (2 * t) * hP.1.eigenvalues i * inner ℝ (orthoCol hP.1 i) x ^ 2 := by
  have h1 := inner_euclid_smul t H x
  rw [inner_euclid_eq_sum_eigen hP.1 x] at h1
  have h2 : ∑ i, 1 / (2 * t) * hP.1.eigenvalues i * inner ℝ (orthoCol hP.1 i) x ^ 2 =
      1 / (2 * t) * ∑ i, hP.1.eigenvalues i * inner ℝ (orthoCol hP.1 i) x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, h1]
  field_simp

/-- `∑_{i<N} ρ^{2(b+1+i)} ≤ ρ^{2(b+1)}/(1 - ρ²)` for `ρ² < 1` (any sign of `ρ`). -/
theorem sum_pow_two_mul_le' {ρ : ℝ} (hρ2 : ρ ^ 2 < 1) (b N : ℕ) :
    ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) ≤ ρ ^ (2 * (b + 1)) / (1 - ρ ^ 2) := by
  have hρ2' : 0 ≤ ρ ^ 2 := by positivity
  have h : ∑ i ∈ range N, ρ ^ (2 * (b + 1 + i)) =
      ρ ^ (2 * (b + 1)) * ∑ i ∈ range N, (ρ ^ 2) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hpos : 0 ≤ ρ ^ (2 * (b + 1)) := by rw [pow_mul]; positivity
  rw [h, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_one_div hρ2' hρ2 N) hpos

end Quadratic

section RunningMean

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem memLp_inner_ulaChain {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) (h : ℝ) {u : EuclideanSpace ℝ ι}
    {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp) (ξ : ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ k, Measurable (ξ k)) (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι))
    (k : ℕ) : MemLp (fun ω => inner ℝ u (ulaChain Q h ξ k ω)) 2 P := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu]
  exact memLp_realChain _ (memLp_projNoise h u ξ hmeas hlaw) k

omit [IsProbabilityMeasure P] in
theorem integrable_inner_ulaChain_sq {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) (h : ℝ)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (k : ℕ) :
    Integrable (fun ω => inner ℝ u (ulaChain Q h ξ k ω) ^ 2) P := by
  have h2 := memLp_inner_ulaChain hsym h hu ξ hmeas hlaw k
  have := h2.integrable_mul h2
  simp only [sq]
  exact this

/-- **The second moment of the projected ULA chain from the mode**: `E ⟨u, x_k⟩² = s₂ (1 - ρ^{2k})`
with `ρ = 1 - hp`, `s₂ = 2h/(1-ρ²)`, for a unit eigenvector `u`. -/
theorem integral_inner_ulaChain_sq {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 ≤ h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1)
    (hρ : (1 - h * p) ^ 2 ≠ 1) (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (hind : iIndepFun ξ P) (k : ℕ) :
    ∫ ω, inner ℝ u (ulaChain Q h ξ k ω) ^ 2 ∂P =
      (2 * h) / (1 - (1 - h * p) ^ 2) * (1 - (1 - h * p) ^ (2 * k)) := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu]
  have hη := memLp_projNoise h u ξ hmeas hlaw
  have hwhite : ∀ j k, ∫ ω, projNoise h u ξ j ω * projNoise h u ξ k ω ∂P =
      if j = k then 2 * h else 0 := fun j k => by
    rw [integral_projNoise_mul hh u ξ hmeas hlaw hind j k, hunit, one_pow, mul_one]
  rw [← norm_toLp_sq_eq_integral (memLp_realChain (1 - h * p) hη k)]
  exact (toAR1Chain (1 - h * p) hη hwhite).norm_x_sq hρ k

/-- **The expected loss-based LLC at draw `k`** of the ULA chain from the mode, `P = t • H`:
`E[½ ⟨x_k, H x_k⟩] = (1/(2t)) ∑ᵢ (1 - ρᵢ^{2k})/(1 - h pᵢ/2)`. -/
theorem integral_llc_ulaChain {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (hind : iIndepFun ξ P) (k : ℕ) :
    ∫ ω, 1 / 2 * inner ℝ (ulaChain (t • H) h ξ k ω) (euclid H (ulaChain (t • H) h ξ k ω)) ∂P =
      1 / (2 * t) * ∑ i, (1 - (1 - h * hP.1.eigenvalues i) ^ (2 * k)) /
        (1 - h * hP.1.eigenvalues i / 2) := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  simp_rw [half_inner_euclid_eq_sum_eigen ht hP]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_inner_ulaChain_sq hPt h (mulVec_orthoCol hP.1 i) ξ hmeas hlaw k).const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := hP.eigenvalues_pos i
  have hhp := hev i
  have hρ : (1 - h * hP.1.eigenvalues i) ^ 2 ≠ 1 := by
    intro heq
    nlinarith [mul_pos hh hp]
  rw [integral_inner_ulaChain_sq hPt hh.le (mulVec_orthoCol hP.1 i) (norm_orthoCol hP.1 i) hρ ξ
    hmeas hlaw hind k]
  have hne1 : 1 - (1 - h * hP.1.eigenvalues i) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hne1' : 1 - (1 - hP.1.eigenvalues i * h) ^ 2 ≠ 0 := by rwa [mul_comm]
  have hne2 : 1 - h * hP.1.eigenvalues i / 2 ≠ 0 := by linarith
  have hne3 : 2 - h * hP.1.eigenvalues i ≠ 0 := by linarith
  have hne3' : 2 - hP.1.eigenvalues i * h ≠ 0 := by linarith
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  ring

/-- **The expected pooled running mean of the loss-based LLC** over `C` chains from the mode and
draws `b+1, …, b+N`: `t E[…] = ½ ∑ᵢ (1 - R₂ᵢ/N)/(1 - h pᵢ/2)`, `R₂ᵢ = ∑_{i<N} ρᵢ^{2(b+1+i)}`. -/
theorem integral_llc_running_mean {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : ∀ c, iIndepFun (ξ c) P) :
    t * ∫ ω, (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, 1 / 2 *
        inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + i) ω)
          (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + i) ω)) ∂P =
      1 / 2 * ∑ j, (1 - (∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) / N) /
        (1 - h * hP.1.eigenvalues j / 2) := by
  have hPt : (t • H)ᵀ = t • H := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hint : ∀ c k, Integrable (fun ω => 1 / 2 *
      inner ℝ (ulaChain (t • H) h (ξ c) k ω) (euclid H (ulaChain (t • H) h (ξ c) k ω))) P := by
    intro c k
    simp_rw [half_inner_euclid_eq_sum_eigen ht hP]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_inner_ulaChain_sq hPt h (mulVec_orthoCol hP.1 i) (ξ c) (hmeas c) (hlaw c)
        k).const_mul _
  rw [integral_const_mul,
    integral_finsetSum _ fun c _ => integrable_finsetSum _ fun i _ => hint c (b + 1 + i),
    Finset.sum_congr rfl fun c _ => integral_finsetSum _ fun i _ => hint c (b + 1 + i),
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ =>
      integral_llc_ulaChain ht hh hP hev (ξ c) (hmeas c) (hlaw c) (hind c) (b + 1 + i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_comm]
  have hterm : ∀ j, ∑ i ∈ range N, (1 - (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) /
      (1 - h * hP.1.eigenvalues j / 2) =
      (N - ∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) /
        (1 - h * hP.1.eigenvalues j / 2) := by
    intro j
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm' : ∀ j, (1 - (∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) / N) /
      (1 - h * hP.1.eigenvalues j / 2) =
      1 / N * ((N - ∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) /
        (1 - h * hP.1.eigenvalues j / 2)) := by
    intro j
    have hne : 1 - h * hP.1.eigenvalues j / 2 ≠ 0 := by have := hev j; linarith
    field_simp
  simp_rw [hterm, hterm']
  rw [← Finset.mul_sum]
  field_simp

/-- **Burn-in only.** The shortfall of the expected pooled LLC running mean from the ULA LLC is
`½ ∑ᵢ (R₂ᵢ/N)/(1 - h pᵢ/2) ≤ ½ ∑ᵢ ρᵢ^{2(b+1)}/(N (1 - ρᵢ²)(1 - h pᵢ/2))`: no `1/(CN)` term. -/
theorem llc_running_mean_shortfall {H : Matrix ι ι ℝ} {t h : ℝ} (ht : 0 < t) (hh : 0 < h)
    (hP : (t • H).PosDef) (hev : ∀ i, h * hP.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : ∀ c, iIndepFun (ξ c) P) :
    1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) -
        t * ∫ ω, (1 / ((C : ℝ) * N)) * ∑ c, ∑ i ∈ range N, 1 / 2 *
          inner ℝ (ulaChain (t • H) h (ξ c) (b + 1 + i) ω)
            (euclid H (ulaChain (t • H) h (ξ c) (b + 1 + i) ω)) ∂P =
        1 / 2 * ∑ j, (∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) / N /
          (1 - h * hP.1.eigenvalues j / 2) ∧
      1 / 2 * ∑ j, (∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) / N /
          (1 - h * hP.1.eigenvalues j / 2) ≤
        1 / 2 * ∑ j, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * hP.1.eigenvalues j) ^ 2) * (1 - h * hP.1.eigenvalues j / 2)) := by
  rw [integral_llc_running_mean ht hh hP hev hC hN b ξ hmeas hlaw hind]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hne : 1 - h * hP.1.eigenvalues j / 2 ≠ 0 := by have := hev j; linarith
    field_simp
    ring
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by norm_num)
    have hp := hP.eigenvalues_pos j
    have hhp := hev j
    have hρ2 : (1 - h * hP.1.eigenvalues j) ^ 2 < 1 := by nlinarith [mul_pos hh hp]
    have hden : 0 < 1 - h * hP.1.eigenvalues j / 2 := by linarith
    have h1ρ : 0 < 1 - (1 - h * hP.1.eigenvalues j) ^ 2 := by linarith
    have hR := sum_pow_two_mul_le' hρ2 b N
    rw [le_div_iff₀ h1ρ] at hR
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) *
          (N * (1 - (1 - h * hP.1.eigenvalues j) ^ 2) * (1 - h * hP.1.eigenvalues j / 2))
        = ((∑ i ∈ range N, (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1 + i))) *
            (1 - (1 - h * hP.1.eigenvalues j) ^ 2)) *
          (N * (1 - h * hP.1.eigenvalues j / 2)) := by ring
      _ ≤ (1 - h * hP.1.eigenvalues j) ^ (2 * (b + 1)) * (N * (1 - h * hP.1.eigenvalues j / 2)) :=
          mul_le_mul_of_nonneg_right hR (by positivity)

end RunningMean

/-! ### C. The `20κ` recipe -/

section Kappa

omit [Fintype ι] [DecidableEq ι] in
/-- With `h pmax = 1/10` and `pmin = pmax/κ`, `2/(h pmin C N) = 20κ/(C N)`. -/
theorem two_div_eq_twenty_kappa {h pmax κ pmin : ℝ} (hh : h * pmax = 1 / 10) (hκ : pmin = pmax / κ)
    (hκ0 : κ ≠ 0) (hpmax : pmax ≠ 0) {C N : ℝ} (hC : C ≠ 0) (hN : N ≠ 0) :
    2 / (h * pmin * C * N) = 20 * κ / (C * N) := by
  have hh0 : h ≠ 0 := by rintro rfl; simp at hh
  subst hκ
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  nlinarith [hh]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The `20κ` recipe as a theorem.** Along the flattest direction `pmin = pmax/κ` with
`h pmax = 1/10`, the finite-chain shortfall of the pooled sample variance from the ULA law is at
most `σ² (ρ^{2(b+1)}/(N(1-ρ²)) + 20κ/(C N))`: `CN ≥ 20κ M` pooled draws make the autocorrelation
term of the relative shortfall at most `1/M` (the burn-in term is separate). -/
theorem expected_pooled_sample_variance_ula_shortfall_kappa {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q)
    {h : ℝ} (hh : 0 < h) {u : EuclideanSpace ℝ ι} {p pmax κ : ℝ} (hp : 0 < p)
    (hhmax : h * pmax = 1 / 10) (hκ : p = pmax / κ) (hκ1 : 1 ≤ κ)
    (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    (2 * h) / (1 - (1 - h * p) ^ 2) -
      ∫ ω, ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2 -
        ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω)) ^ 2) ∂P ≤
      (2 * h) / (1 - (1 - h * p) ^ 2) *
        ((1 - h * p) ^ (2 * (b + 1)) / (N * (1 - (1 - h * p) ^ 2)) + 20 * κ / (C * N)) := by
  have hκ0 : κ ≠ 0 := by linarith
  have hpmax : pmax ≠ 0 := by
    rintro rfl
    simp at hhmax
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hhp : h * p < 1 := by
    rw [hκ, ← mul_div_assoc, hhmax]
    rw [div_lt_one (by linarith)]
    linarith
  rw [← two_div_eq_twenty_kappa hhmax hκ hκ0 hpmax hC' hN']
  exact expected_pooled_sample_variance_ula_shortfall hsym hh hp hhp hu hunit hC hN b ξ hmeas hlaw
    hind

end Kappa

end Laplace.Sampler
