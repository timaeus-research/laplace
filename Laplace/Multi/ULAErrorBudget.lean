/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.BurnInStart

/-!
# The E2–E4 error budget: exact localised LLC versus the ULA-sampled anchored estimate

Three sources of error separate the exact localised LLC `t⟨L∘A⟩_loc` (E2) from what ULA on the
anchored
Gaussian model returns after `k` steps from a start `x₀` (E3 + E4):
**`t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k = C₁′/t − (th/4)∑ᵢλᵢ/κᵢ + Burn_k + O(t⁻²)`** (`ulaAnchored_llc_budget`),
with the
anharmonic gap `C₁′/t` of `AnchoredEnergyGap`, the ULA step-size bias `−(th/4)∑ᵢλᵢ/κᵢ` (`κᵢ = 1 −
hpᵢ/2`,
`pᵢ = tλᵢ + g`; the sampler sits *above* the Gaussian prediction), and the burn-in transient
`Burn_k = (t/2)∑ᵢλᵢρᵢ^{2k}/(pᵢκᵢ) − (t/2)∑ᵢλᵢ[((Qᵀm_k)ᵢ)² − (aᵢ/pᵢ)²]`, `m_k = m + (1 − hP)^k(x₀ −
m)`. The
last two are exact identities of the quadratic model; only the first carries a remainder.

To get there the burn-in algebra of `BurnInGammaLaw` is restated for an arbitrary orthogonal frame
(`ulaStep_eq_conj_frame`, `ulaCov_eq_conj_frame`, `burnInCov_eq_conj_frame`,
`burnInCov_inv_posDef_frame`), and
ULA on the target `N(m, P⁻¹)` from `x₀` is formalised as the tilted Gaussian `N(m_k, Σ_k)`
(`burnInMeanAnch`, `burnInTiltAnch`) with the energy of any `H` sharing the frame
(`burnInAnch_energy_frame`: `⟨½uᵀHu⟩_k = ½∑ᵢλᵢfᵢ/(pᵢκᵢ) + ½∑ᵢλᵢ((Uᵀm_k)ᵢ)²`). With the β-scaled step
`h = η/t` the step-size bias tends to `(η/4)∑ᵢλᵢ/(1 − ηλᵢ/2)`, an `O(1)` error that does not vanish
as
`t → ∞`, while the anharmonic error is `O(1/t)` (prose; see the tide log).
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Frame algebra -/

section FrameAlgebra

variable {U : Matrix ι ι ℝ}

theorem conj_mul_conj_frame (hU : Uᵀ * U = 1) (D₁ D₂ : Matrix ι ι ℝ) :
    (U * D₁ * Uᵀ) * (U * D₂ * Uᵀ) = U * (D₁ * D₂) * Uᵀ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]

theorem conj_pow_frame (hU : Uᵀ * U = 1) (D : Matrix ι ι ℝ) (n : ℕ) :
    (U * D * Uᵀ) ^ n = U * D ^ n * Uᵀ := by
  induction n with
  | zero => simp [mul_transpose_eq_one_of hU]
  | succ n ih => rw [pow_succ, ih, conj_mul_conj_frame hU, pow_succ]

theorem one_sub_conj_frame (hU : Uᵀ * U = 1) (D : Matrix ι ι ℝ) :
    (1 : Matrix ι ι ℝ) - U * D * Uᵀ = U * (1 - D) * Uᵀ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_transpose_eq_one_of hU]

theorem inv_conj_diagonal_frame (hU : Uᵀ * U = 1) {d : ι → ℝ} (hd : ∀ i, d i ≠ 0) :
    (U * diagonal d * Uᵀ)⁻¹ = U * diagonal (fun i => (d i)⁻¹) * Uᵀ := by
  apply Matrix.inv_eq_left_inv
  rw [conj_mul_conj_frame hU, diagonal_mul_diagonal]
  have e : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) := funext fun i => by
    simp [inv_mul_cancel₀ (hd i)]
  rw [e, Matrix.diagonal_one, Matrix.mul_one, mul_transpose_eq_one_of hU]

omit [DecidableEq ι] in
theorem conj_diagonal_entry' [DecidableEq ι] (U : Matrix ι ι ℝ) (d : ι → ℝ) (i j : ι) :
    (U * diagonal d * Uᵀ) i j = ∑ l, U i l * d l * U j l := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem conj_diagonal_symm (U : Matrix ι ι ℝ) (d : ι → ℝ) (i j : ι) :
    (U * diagonal d * Uᵀ) j i = (U * diagonal d * Uᵀ) i j := by
  rw [conj_diagonal_entry', conj_diagonal_entry']
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `∑ᵢⱼ Hᵢⱼ (U diag(d) Uᵀ)ᵢⱼ = ∑ᵢ λᵢdᵢ` when `UᵀHU = diag(λ)`. -/
theorem sum_sum_mul_conj_eq (hU : Uᵀ * U = 1) {H : Matrix ι ι ℝ} {lam : ι → ℝ}
    (hdiag : Uᵀ * H * U = diagonal lam) (d : ι → ℝ) :
    ∑ i, ∑ j, H i j * (U * diagonal d * Uᵀ) i j = ∑ i, lam i * d i := by
  have e1 : ∑ i, ∑ j, H i j * (U * diagonal d * Uᵀ) i j =
      ∑ i, (H * (U * diagonal d * Uᵀ)) i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply (M := H) (N := U * diagonal d * Uᵀ)]
    exact Finset.sum_congr rfl fun j _ => by rw [conj_diagonal_symm U d i j]
  have e2 : Matrix.trace (H * (U * diagonal d * Uᵀ)) = ∑ i, (H * (U * diagonal d * Uᵀ)) i i := rfl
  rw [e1, ← e2, frame_eq_conj hU hdiag, conj_mul_conj_frame hU, Matrix.trace_mul_cycle, hU,
      Matrix.one_mul,
    diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- `xᵀ(U diag(d) Uᵀ)x = ∑ᵢ dᵢ(Uᵀx)ᵢ²`. -/
theorem dotProduct_conj_diagonal_mulVec (U : Matrix ι ι ℝ) (d : ι → ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (U * diagonal d * Uᵀ) *ᵥ x = ∑ i, d i * (Uᵀ *ᵥ x) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

end FrameAlgebra

/-! ### ULA on a Gaussian target, in an arbitrary orthogonal frame -/

section ULAFrame

variable {U P : Matrix ι ι ℝ} {p : ι → ℝ}

theorem ulaStep_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (h : ℝ) :
    ulaStep P h = U * diagonal (fun i => 1 - h * p i) * Uᵀ := by
  have hP' := frame_eq_conj hU hdiag
  have e : diagonal (fun i => 1 - h * p i) = 1 - h • diagonal p := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  unfold ulaStep
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_transpose_eq_one_of hU,
      Matrix.mul_smul,
    Matrix.smul_mul, ← hP']

theorem ulaStep_pow_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (h : ℝ) (k :
    ℕ) :
    ulaStep P h ^ k = U * diagonal (fun i => (1 - h * p i) ^ k) * Uᵀ := by
  rw [ulaStep_eq_conj_frame hU hdiag h, conj_pow_frame hU, diagonal_pow]
  rfl

theorem ulaCov_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p
    i) {h : ℝ} (hev : ∀ i, h * p i < 2) :
    ulaCov P h = U * diagonal (fun i => 1 / (p i * (1 - h * p i / 2))) * Uᵀ := by
  have hP' := frame_eq_conj hU hdiag
  have e2 : diagonal (fun i => p i * (1 - h * p i / 2)) =
      diagonal p - (h / 2) • (diagonal p * diagonal p) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
      ring
    · simp [hij]
  have e : P - (h / 2) • (P * P) = U * diagonal (fun i => p i * (1 - h * p i / 2)) * Uᵀ := by
    rw [e2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← conj_mul_conj_frame
        hU,
      ← hP']
  unfold ulaCov
  rw [e, inv_conj_diagonal_frame hU fun i => (mul_pos (hp i) (by linarith [hev i])).ne']
  simp only [one_div]

theorem burnInCov_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i) {h : ℝ} (hev : ∀ i, h * p i < 2) (k : ℕ) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k))) = U * diagonal (fun i => 1 / (p i * (1 - h * p i /
        2)) * (1 - (1 - h * p i) ^ (2 * k))) * Uᵀ := by
  rw [ulaCov_eq_conj_frame hU hdiag hp hev, ulaStep_pow_eq_conj_frame hU hdiag, one_sub_conj_frame
      hU,
    conj_mul_conj_frame hU]
  congr 2
  rw [← Matrix.diagonal_one, diagonal_sub, diagonal_mul_diagonal]

omit [Fintype ι] [DecidableEq ι] in
theorem burnInVar_pos_frame (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {k :
    ℕ} (hk : 1 ≤ k) (i : ι) : 0 < 1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k)) :=
        by
  have hpi := hp i
  have h2 := hev i
  have ha : 0 < 1 - h * p i / 2 := by linarith
  have hρ : (1 - h * p i) ^ 2 < 1 := by nlinarith [mul_pos hh hpi]
  have hf : (1 - h * p i) ^ (2 * k) < 1 := by
    rw [pow_mul]
    exact pow_lt_one₀ (sq_nonneg _) hρ (by omega)
  have : 0 < 1 - (1 - h * p i) ^ (2 * k) := by linarith
  positivity

theorem burnInCov_inv_eq_conj_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i,
    0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {k : ℕ} (hk : 1 ≤ k) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ = U * diagonal (fun i => (1 / (p i * (1 - h * p i
        / 2)) * (1 - (1 - h * p i) ^ (2 * k)))⁻¹) * Uᵀ := by
  rw [burnInCov_eq_conj_frame hU hdiag hp hev k]
  exact inv_conj_diagonal_frame hU fun i => (burnInVar_pos_frame hp hh hev hk i).ne'

theorem burnInCov_inv_posDef_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0
    < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {k : ℕ} (hk : 1 ≤ k) : (ulaCov P h * (1 -
        ulaStep P h ^ (2 * k)))⁻¹.PosDef := by
  rw [burnInCov_inv_eq_conj_frame hU hdiag hp hh hev hk]
  exact posDef_conj_diagonal hU fun i => inv_pos.mpr (burnInVar_pos_frame hp hh hev hk i)

theorem burnInCov_inv_inv_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {k : ℕ} (hk : 1 ≤ k) :
    (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹⁻¹ = U * diagonal (fun i => 1 / (p i * (1 - h * p i
        / 2)) * (1 - (1 - h * p i) ^ (2 * k))) * Uᵀ := by
  rw [burnInCov_inv_eq_conj_frame hU hdiag hp hh hev hk,
    inv_conj_diagonal_frame hU fun i => inv_ne_zero (burnInVar_pos_frame hp hh hev hk i).ne']
  simp only [inv_inv]

/-! ### ULA on the anchored Gaussian `N(m, P⁻¹)` from a start `x₀` -/

/-- The `k`-step ULA mean on the target `N(m, P⁻¹)` from `x₀`: `m + (1 − hP)^k(x₀ − m)`. -/
noncomputable def burnInMeanAnch (P : Matrix ι ι ℝ) (h : ℝ) (k : ℕ) (m x₀ : ι → ℝ) : ι → ℝ :=
  m + ulaStep P h ^ k *ᵥ (x₀ - m)

/-- The tilt of the `k`-step law: `Σ_k⁻¹ m_k`. -/
noncomputable def burnInTiltAnch (P : Matrix ι ι ℝ) (h : ℝ) (k : ℕ) (m x₀ : ι → ℝ) : ι → ℝ :=
  (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ *ᵥ burnInMeanAnch P h k m x₀

theorem transpose_mulVec_burnInMeanAnch (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (h : ℝ)
    (k : ℕ) (m x₀ : ι → ℝ) (i : ι) :
    (Uᵀ *ᵥ burnInMeanAnch P h k m x₀) i =
      (Uᵀ *ᵥ m) i + (1 - h * p i) ^ k * (Uᵀ *ᵥ (x₀ - m)) i := by
  unfold burnInMeanAnch
  rw [Matrix.mulVec_add, ulaStep_pow_eq_conj_frame hU hdiag, Matrix.mulVec_mulVec, ←
      Matrix.mul_assoc,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  simp only [Pi.add_apply, Matrix.mulVec_diagonal]

/-- **The burn-in energy of a second matrix `H` in the same frame** (`UᵀHU = diag(λ)`), for ULA on
`N(m, P⁻¹)` from `x₀`: `⟨½uᵀHu⟩_k = ½∑ᵢλᵢfᵢ/(pᵢκᵢ) + ½∑ᵢλᵢ((Uᵀm)ᵢ + ρᵢ^k(Uᵀ(x₀ − m))ᵢ)²`. -/
theorem burnInAnch_energy_frame (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {H : Matrix ι ι ℝ} {lam : ι → ℝ}
    (hdiagH : Uᵀ * H * U = diagonal lam) {k : ℕ} (hk : 1 ≤ k) (m x₀ : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTiltAnch P h k m x₀) (fun
        u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      1 / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k))) +
        1 / 2 * ∑ i, lam i * ((Uᵀ *ᵥ m) i + (1 - h * p i) ^ k * (Uᵀ *ᵥ (x₀ - m)) i) ^ 2 := by
  have hQ := burnInCov_inv_posDef_frame hU hdiag hp hh hev hk
  unfold burnInTiltAnch
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hQ, tiltMean_mulVec_self hQ,
    burnInCov_inv_inv_frame hU hdiag hp hh hev hk, sum_sum_mul_conj_eq hU hdiagH,
    frame_eq_conj hU hdiagH, dotProduct_conj_diagonal_mulVec]
  simp only [transpose_mulVec_burnInMeanAnch hU hdiag]
  ring

/-- **The cold start**: from `x₀ = m` the mean transient vanishes and only the covariance builds
up. -/
theorem burnInAnch_energy_frame_modeStart (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp :
    ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {H : Matrix ι ι ℝ} {lam : ι → ℝ}
    (hdiagH : Uᵀ * H * U = diagonal lam) {k : ℕ} (hk : 1 ≤ k) (m : ι → ℝ) :
    tiltedExpectation (ulaCov P h * (1 - ulaStep P h ^ (2 * k)))⁻¹ (burnInTiltAnch P h k m m) (fun
        u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      1 / 2 * ∑ i, lam i * (1 / (p i * (1 - h * p i / 2)) * (1 - (1 - h * p i) ^ (2 * k))) + 1 / 2
          * ∑ i, lam i * (Uᵀ *ᵥ m) i ^ 2 := by
  rw [burnInAnch_energy_frame hU hdiag hp hh hev hdiagH hk m m]
  simp

end ULAFrame

end Laplace.Sampler

namespace Laplace.Multi

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}

theorem transpose_localisedPrecision_conj (hQ : Qᵀ * Q = 1) (t g : ℝ) :
    Qᵀ * (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) * Q =
      diagonal (fun i => t * lam i + g) := by
  have e : diagonal (fun i => t * lam i + g) =
      t • diagonal lam + g • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul,
    conj_conj hQ, Matrix.mul_one, hQ]

/-- The mean part of the burn-in transient, expanded: `(t/2)∑λᵢ(μᵢ² − bᵢ²) = t∑λᵢbᵢρᵢ^k(zᵢ − bᵢ) +
(t/2)∑λᵢρᵢ^{2k}(zᵢ − bᵢ)²`, `μᵢ = bᵢ + ρᵢ^k(zᵢ − bᵢ)`. -/
theorem burnIn_meanTerm_expand (t : ℝ) (lam b z ρ : Fin d → ℝ) (k : ℕ) :
    t / 2 * ∑ i, lam i * ((b i + ρ i ^ k * (z i - b i)) ^ 2 - b i ^ 2) =
      t * ∑ i, lam i * b i * (ρ i ^ k * (z i - b i)) +
        t / 2 * ∑ i, lam i * (ρ i ^ (2 * k) * (z i - b i) ^ 2) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The β-scaled step leaves an `O(1)` bias**: with `h = η/t` and `ηλᵢ < 2`, the ULA step-size
bias
`(th/4)∑ᵢλᵢ/κᵢ` tends to `(η/4)∑ᵢλᵢ/(1 − ηλᵢ/2)` as `t → ∞`. -/
theorem ulaScaledStep_bias_tendsto {η : ℝ} (hηl : ∀ i, η * lam i < 2) :
    Tendsto (fun t : ℝ => t * (η / t) / 4 * ∑ i, lam i / (1 - η / t * (t * lam i + g) / 2)) atTop
      (𝓝 (η / 4 * ∑ i, lam i / (1 - η * lam i / 2))) := by
  have h1 : Tendsto (fun t : ℝ => t * (η / t) / 4) atTop (𝓝 (η / 4)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  have h2 : ∀ i, Tendsto (fun t : ℝ => lam i / (1 - η / t * (t * lam i + g) / 2)) atTop
      (𝓝 (lam i / (1 - η * lam i / 2))) := fun i => by
    have e : (fun t : ℝ => 1 - (η * lam i + η * g / t) / 2) =ᶠ[atTop]
        fun t => 1 - η / t * (t * lam i + g) / 2 := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
      field_simp
    have hz : Tendsto (fun t : ℝ => η * g / t) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := η * g)).div_atTop tendsto_id
    have hden : Tendsto (fun t : ℝ => 1 - (η * lam i + η * g / t) / 2) atTop
        (𝓝 (1 - η * lam i / 2)) := by
      simpa using (((tendsto_const_nhds (x := η * lam i)).add hz).div_const 2).const_sub 1
    exact tendsto_const_nhds.div (hden.congr' e) (by have := hηl i; intro h0; linarith)
  simpa using h1.mul (tendsto_finsetSum Finset.univ fun i _ => h2 i)

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The E2–E4 error budget**: for the exact localised LLC and the ULA-sampled anchored estimate
after
`k ≥ 1` steps from `x₀` (any stable step `h`),
`t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k = C₁′/t − (th/4)∑ᵢλᵢ/κᵢ + Burn_k + O(t⁻²)`. -/
theorem ulaAnchored_llc_budget (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t → ∀ {h : ℝ}, 0 < h → (∀ i, h * (t * lam i + g) < 2)
        →
      ∀ {k : ℕ}, 1 ≤ k → ∀ x₀ : Fin d → ℝ,
      |t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
        (rotatedAnharmonic Q c lam alpha gamma) - t * tiltedExpectation (Laplace.Sampler.ulaCov (t •
        (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) h * (1 -
        Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) h
        ^ (2 * k)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix
        (Fin d) (Fin d) ℝ)) h k ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
        ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) - (∑
        i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) -
        (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t + t * h / 4 * ∑ i, lam i / (1 - h * (t *
        lam i + g) / 2) - (t / 2 * ∑ i, lam i * (1 - h * (t * lam i + g)) ^ (2 * k) / ((t * lam i +
        g) * (1 - h * (t * lam i + g) / 2)) - t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i / (t *
        lam i + g) + (1 - h * (t * lam i + g)) ^ k * ((Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t *
        lam i + g))) ^ 2 - (g * affineFrame Q c w₀ i / (t * lam i + g)) ^ 2))| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    localisedEnergy_anchoredGap (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  refine ⟨K₁, T₁, hK₁, hT₁, fun {t} ht {h} hh hev {k} hk x₀ => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdiagH : Qᵀ * (Q * diagonal lam * Qᵀ) * Q = diagonal lam := conj_conj hQ _
  have hdiagP := transpose_localisedPrecision_conj (lam := lam) hQ t g
  have hp : ∀ i, 0 < t * lam i + g := fun i => by have := hlam i; positivity
  have hE := Laplace.Sampler.burnInAnch_energy_frame hQ hdiagP hp hh hev hdiagH hk ((t • (Q *
    diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀
  have hm : ∀ i, (Qᵀ *ᵥ ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g
      • (w₀ - c)))) i = g * affineFrame Q c w₀ i / (t * lam i + g) := by
    intro i
    rw [Laplace.Sampler.inv_localisedPrecision_eq_conj_frame hQ hdiagH hlam ht0 hg, ←
        Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qᵀ Q, hQ, Matrix.one_mulVec,
          Matrix.mulVec_diagonal,
      Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    unfold affineFrame
    ring
  have hx : ∀ i, (Qᵀ *ᵥ (x₀ - ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
      *ᵥ (g • (w₀ - c))))) i = (Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g) := by
    intro i
    rw [Matrix.mulVec_sub, Pi.sub_apply, hm i]
  simp only [hm, hx] at hE
  rw [hE]
  have e₁ := h₁ ht
  have hκ : ∀ i, (1 - h * (t * lam i + g) / 2) ≠ 0 := fun i => by have := hev i; intro h0; linarith
  have key : t * (1 / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) * (1 -
      (1 - h * (t * lam i + g)) ^ (2 * k))) + 1 / 2 * ∑ i, lam i * (g * affineFrame Q c w₀ i / (t *
      lam i + g) + (1 - h * (t * lam i + g)) ^ k * ((Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t *
      lam i + g))) ^ 2) - t * h / 4 * ∑ i, lam i / (1 - h * (t * lam i + g) / 2) + (t / 2 * ∑ i, lam
      i * (1 - h * (t * lam i + g)) ^ (2 * k) / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) -
      t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i / (t * lam i + g) + (1 - h * (t * lam i + g))
      ^ k * ((Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g))) ^ 2 - (g * affineFrame Q c
      w₀ i / (t * lam i + g)) ^ 2)) = 1 / 2 * ∑ i, t * lam i / (t * lam i + g) + t / 2 * ∑ i, lam i
      * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2 := by
    rw [mul_add, ← mul_assoc, ← mul_assoc]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    set pp := t * lam i + g with hpp
    have hpp0 : pp ≠ 0 := (hp i).ne'
    have hκ' : 1 - h * pp / 2 ≠ 0 := hκ i
    have h2 : 2 - h * pp ≠ 0 := by
      have := hev i
      rw [← hpp] at this
      intro h0
      linarith
    have h2' : 2 - pp * h ≠ 0 := by
      rw [mul_comm]
      exact h2
    field_simp
    ring
  have e : t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) - t * (1 / 2 * ∑ i, lam i * (1 / ((t * lam i + g) * (1
      - h * (t * lam i + g) / 2)) * (1 - (1 - h * (t * lam i + g)) ^ (2 * k))) + 1 / 2 * ∑ i, lam i
      * (g * affineFrame Q c w₀ i / (t * lam i + g) + (1 - h * (t * lam i + g)) ^ k * ((Qᵀ *ᵥ x₀) i
      - g * affineFrame Q c w₀ i / (t * lam i + g))) ^ 2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i)
      (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 *
      lam i))) / t + t * h / 4 * ∑ i, lam i / (1 - h * (t * lam i + g) / 2) - (t / 2 * ∑ i, lam i *
      (1 - h * (t * lam i + g)) ^ (2 * k) / ((t * lam i + g) * (1 - h * (t * lam i + g) / 2)) - t /
      2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i / (t * lam i + g) + (1 - h * (t * lam i + g)) ^ k
      * ((Qᵀ *ᵥ x₀) i - g * affineFrame Q c w₀ i / (t * lam i + g))) ^ 2 - (g * affineFrame Q c w₀ i
      / (t * lam i + g)) ^ 2)) = t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, t * lam i / (t * lam i
      + g) + t / 2 * ∑ i, lam i * ((g * affineFrame Q c w₀ i) / (t * lam i + g)) ^ 2) - (∑ i,
      (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g *
      affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t := by
    rw [← key]
    ring
  rw [e]
  exact e₁

end Multi

end Laplace.Multi
