/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltedGaussian
import Laplace.Sampler.ULA

/-!
# The localised LLC as a function of the localisation strength (E3, E6)

The Sanity on Sampling note's E3 says "the LLC shrinks as `½ t tr(H(tH + γI)⁻¹)`" (predicted
`4.20, 2.50, 0.80` at `γ_rel = 1, 10, 100` for its `d = 10`, `κ = 100` quadratic) and E6 that "a
localised LLC is the Hessian quantity `½ t tr(H(tH + γI)⁻¹)`, not `d/2`". The seabed's
`localised_llc` gives this quantity in matrix-entry form; here it is put in the eigenbasis of `H`
and studied as a function of `γ`.

* `orthoOf_transpose_localised_inv_mul`: `Uᵀ (tH + γI)⁻¹ U = diag(1/(tλᵢ + γ))`;
* `localisedLLC` and `localised_llc_matrix_eq_eigen`:
  `½ ∑ᵢⱼ (tH)ᵢⱼ ((tH + γI)⁻¹)ᵢⱼ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)`; on the Gibbs side, for the centred
  anchor, `t ⟨½ wᵀHw⟩ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)` (`localised_llc_centred`); the covariance trace
  `tr((tH + γI)⁻¹) = ∑ᵢ 1/(tλᵢ + γ)` (`trace_localised_inv`);
* `localisedLLC_zero` (`= d/2`), `localisedLLC_antitone`, `localisedLLC_lt_half_dim` (strictly
  below `d/2` for `γ > 0`), `localisedLLC_pos`, `localisedLLC_tendsto_zero`;
* `localisedLLC_bounds`: with `0 < λ_min ≤ λᵢ ≤ λ_max`,
  `d/(2(1 + γ/(tλ_min))) ≤ Λ(γ) ≤ d/(2(1 + γ/(tλ_max)))`, i.e. in the note's parameters
  `γ_rel = γ/(tλ_min)`, `κ = λ_max/λ_min`: `d/(2(1 + γ_rel)) ≤ Λ ≤ d/(2(1 + γ_rel/κ))`
  (`localisedLLC_bounds_kappa`); the per-direction variance ratio `(tλᵢ + γ)/(tλᵢ) = 1 + γ/(tλᵢ)`
  between `1 + γ_rel/κ` and `1 + γ_rel` (`localised_variance_ratio_bounds`).
-/

open Matrix Filter Topology Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spectral form -/

omit [DecidableEq ι] in
/-- `∑ᵢⱼ Aᵢⱼ Bᵢⱼ = trace (Aᵀ B)`. -/
theorem sum_mul_apply_eq_trace (A B : Matrix ι ι ℝ) :
    ∑ i, ∑ j, A i j * B i j = (Aᵀ * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- `Uᵀ (tH + γI) U = diag(tλᵢ + γ)`. -/
theorem orthoOf_transpose_localised_mul {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (t γ : ℝ) :
    (orthoOf hH)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH =
      diagonal (fun i => t * hH.eigenvalues i + γ) := by
  have h1 : (orthoOf hH)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH =
      t • diagonal hH.eigenvalues + γ • (1 : Matrix ι ι ℝ) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      orthoOf_transpose_mul_mul hH, orthoOf_transpose_mul hH]
  rw [h1]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- `Uᵀ (tH + γI)⁻¹ U = diag(1/(tλᵢ + γ))` for `H` positive definite, `t > 0`, `γ ≥ 0`. -/
theorem orthoOf_transpose_localised_inv_mul {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ}
    (ht : 0 < t) (hγ : 0 ≤ γ) :
    (orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ * orthoOf hH.1 =
      diagonal (fun i => 1 / (t * hH.1.eigenvalues i + γ)) := by
  have ha0 : ∀ i, t * hH.1.eigenvalues i + γ ≠ 0 := fun i => by
    have := hH.eigenvalues_pos i
    positivity
  have hconj := orthoOf_transpose_localised_mul hH.1 t γ
  have hUU : (orthoOf hH.1)ᵀ * orthoOf hH.1 = 1 := orthoOf_transpose_mul hH.1
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  have hinv : (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ =
      orthoOf hH.1 * diagonal (fun i => 1 / (t * hH.1.eigenvalues i + γ)) * (orthoOf hH.1)ᵀ := by
    apply Matrix.inv_eq_left_inv
    have hre : orthoOf hH.1 * diagonal (fun i => 1 / (t * hH.1.eigenvalues i + γ)) *
        (orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) =
        orthoOf hH.1 * diagonal (fun i => 1 / (t * hH.1.eigenvalues i + γ)) *
          ((orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ)) * orthoOf hH.1) *
            (orthoOf hH.1)ᵀ := by
      simp only [Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [hre, hconj, Matrix.mul_assoc (orthoOf hH.1), diagonal_mul_diagonal]
    have hd : (fun i => 1 / (t * hH.1.eigenvalues i + γ) * (t * hH.1.eigenvalues i + γ)) =
        fun _ => (1 : ℝ) := funext fun i => one_div_mul_cancel (ha0 i)
    rw [hd, diagonal_one, Matrix.mul_one, hUU']
  rw [hinv]
  simp only [← Matrix.mul_assoc]
  rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- The localised LLC in the eigenbasis: `Λ(γ) = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)`. -/
noncomputable def localisedLLC {H : Matrix ι ι ℝ} (hH : H.PosDef) (t γ : ℝ) : ℝ :=
  1 / 2 * ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ)

/-- **The localised LLC in the eigenbasis**:
`½ ∑ᵢⱼ (tH)ᵢⱼ ((tH + γI)⁻¹)ᵢⱼ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)`. -/
theorem localised_llc_matrix_eq_eigen {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) :
    1 / 2 * ∑ i, ∑ j, (t • H) i j * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ i j =
      localisedLLC hH t γ := by
  have hHt : Hᵀ = H := by
    have := hH.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  rw [sum_mul_apply_eq_trace, transpose_smul, hHt]
  have h1 : ((t • H) * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹).trace =
      (((orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1) *
        ((orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ * orthoOf hH.1)).trace := by
    have : ((orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1) *
        ((orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ * orthoOf hH.1) =
        (orthoOf hH.1)ᵀ * ((t • H) * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹) * orthoOf hH.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (orthoOf hH.1) (orthoOf hH.1)ᵀ, hUU', Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
  have h2 : (orthoOf hH.1)ᵀ * (t • H) * orthoOf hH.1 =
      diagonal (fun i => t * hH.1.eigenvalues i) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, orthoOf_transpose_mul_mul hH.1, ← diagonal_smul]
    rfl
  rw [h1, h2, orthoOf_transpose_localised_inv_mul hH ht hγ, diagonal_mul_diagonal, trace_diagonal,
    localisedLLC]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_one_div]

/-- **E3/E6, the centred localised LLC in the eigenbasis**: for the anchor at the minimiser,
`t ⟨½ wᵀHw⟩ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)` under the localised target `exp(−t·½wᵀHw − (γ/2)|w|²)`. -/
theorem localised_llc_centred {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) :
    t * tiltedExpectation (t • H + γ • 1) (γ • (0 : ι → ℝ)) (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      localisedLLC hH t γ := by
  rw [localised_llc hH ht hγ 0, tiltMean_zero, zero_dotProduct, mul_zero, add_zero,
    localised_llc_matrix_eq_eigen hH ht hγ]

/-- **The localised covariance trace**: `tr((tH + γI)⁻¹) = ∑ᵢ 1/(tλᵢ + γ)`. -/
theorem trace_localised_inv {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) :
    (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹.trace = ∑ i, 1 / (t * hH.1.eigenvalues i + γ) := by
  have hUU' : orthoOf hH.1 * (orthoOf hH.1)ᵀ = 1 := orthoOf_mul_transpose hH.1
  have h1 : (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹.trace =
      ((orthoOf hH.1)ᵀ * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ * orthoOf hH.1).trace := by
    rw [Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
  rw [h1, orthoOf_transpose_localised_inv_mul hH ht hγ, trace_diagonal]

/-! ### Behaviour in `γ` -/

/-- `Λ(0) = d/2`: without localisation the Gaussian LLC is `d/2`. -/
theorem localisedLLC_zero {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 < t) :
    localisedLLC hH t 0 = Fintype.card ι / 2 := by
  unfold localisedLLC
  have hterm : ∀ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + 0) = 1 := fun i => by
    have := hH.eigenvalues_pos i
    rw [add_zero]
    exact div_self (by positivity)
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **The localised LLC decreases with the localisation strength.** -/
theorem localisedLLC_antitone {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 < t)
    {γ γ' : ℝ} (hγ : 0 ≤ γ) (hγγ' : γ ≤ γ') :
    localisedLLC hH t γ' ≤ localisedLLC hH t γ := by
  unfold localisedLLC
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
  have hp := hH.eigenvalues_pos i
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **A localised LLC is strictly below `d/2`** for `γ > 0` (E6: "not `d/2` even for a
quadratic"). -/
theorem localisedLLC_lt_half_dim [Nonempty ι] {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ}
    (ht : 0 < t) (hγ : 0 < γ) :
    localisedLLC hH t γ < Fintype.card ι / 2 := by
  unfold localisedLLC
  have h : ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) < ∑ _i : ι, (1 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => by
      have hp := hH.eigenvalues_pos i
      rw [div_lt_one (by positivity)]
      linarith
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  linarith

/-- The localised LLC is positive. -/
theorem localisedLLC_pos [Nonempty ι] {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) : 0 < localisedLLC hH t γ := by
  unfold localisedLLC
  refine mul_pos (by norm_num) (Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty)
  have hp := hH.eigenvalues_pos i
  positivity

/-- **Strong localisation kills the LLC**: `Λ(γ) → 0` as `γ → ∞`. -/
theorem localisedLLC_tendsto_zero {H : Matrix ι ι ℝ} (hH : H.PosDef) (t : ℝ) :
    Tendsto (fun γ => localisedLLC hH t γ) atTop (𝓝 0) := by
  unfold localisedLLC
  have hterm : ∀ i, Tendsto (fun γ : ℝ => t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ))
      atTop (𝓝 0) := fun i => by
    have hden : Tendsto (fun γ : ℝ => t * hH.1.eigenvalues i + γ) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    have h := (tendsto_inv_atTop_zero.comp hden).const_mul (t * hH.1.eigenvalues i)
    simpa [div_eq_mul_inv, Function.comp_def] using h
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => hterm i
  simpa using hsum.const_mul (1 / 2 : ℝ)

/-! ### Bounds in terms of the condition number -/

/-- **The `γ_rel`/`κ` bounds.** With `0 < λ_min ≤ λᵢ ≤ λ_max`,
`d/(2(1 + γ/(tλ_min))) ≤ Λ(γ) ≤ d/(2(1 + γ/(tλ_max)))`. -/
theorem localisedLLC_bounds {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    {pmin pmax : ℝ} (hpmin : 0 < pmin) (hpmax : 0 < pmax) (hmin : ∀ i, pmin ≤ hH.1.eigenvalues i)
    (hmax : ∀ i, hH.1.eigenvalues i ≤ pmax) :
    Fintype.card ι / (2 * (1 + γ / (t * pmin))) ≤ localisedLLC hH t γ ∧
      localisedLLC hH t γ ≤ Fintype.card ι / (2 * (1 + γ / (t * pmax))) := by
  unfold localisedLLC
  have hterm : ∀ i, t * pmin / (t * pmin + γ) ≤
      t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) ∧
      t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) ≤ t * pmax / (t * pmax + γ) := by
    intro i
    have hp := hH.eigenvalues_pos i
    have htγ : 0 ≤ t * γ := mul_nonneg ht.le hγ
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (hmin i) htγ]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (hmax i) htγ]
  have hlo : (Fintype.card ι : ℝ) * (t * pmin / (t * pmin + γ)) ≤
      ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hterm i).1
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hhi : ∑ i, t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + γ) ≤
      (Fintype.card ι : ℝ) * (t * pmax / (t * pmax + γ)) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hterm i).2
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have e1 : (Fintype.card ι : ℝ) / (2 * (1 + γ / (t * pmin))) =
      1 / 2 * (Fintype.card ι * (t * pmin / (t * pmin + γ))) := by
    have : t * pmin + γ ≠ 0 := by positivity
    field_simp
  have e2 : (Fintype.card ι : ℝ) / (2 * (1 + γ / (t * pmax))) =
      1 / 2 * (Fintype.card ι * (t * pmax / (t * pmax + γ))) := by
    have : t * pmax + γ ≠ 0 := by positivity
    field_simp
  exact ⟨e1 ▸ mul_le_mul_of_nonneg_left hlo (by norm_num),
    e2 ▸ mul_le_mul_of_nonneg_left hhi (by norm_num)⟩

/-- **The note's parameters**: with `γ_rel = γ/(tλ_min)` and `κ = λ_max/λ_min`,
`d/(2(1 + γ_rel)) ≤ Λ(γ) ≤ d/(2(1 + γ_rel/κ))`. -/
theorem localisedLLC_bounds_kappa {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) {pmin pmax : ℝ} (hpmin : 0 < pmin) (hpmax : 0 < pmax)
    (hmin : ∀ i, pmin ≤ hH.1.eigenvalues i) (hmax : ∀ i, hH.1.eigenvalues i ≤ pmax) :
    Fintype.card ι / (2 * (1 + γ / (t * pmin))) ≤ localisedLLC hH t γ ∧
      localisedLLC hH t γ ≤ Fintype.card ι / (2 * (1 + γ / (t * pmin) / (pmax / pmin))) := by
  have h := localisedLLC_bounds hH ht hγ hpmin hpmax hmin hmax
  have e : γ / (t * pmin) / (pmax / pmin) = γ / (t * pmax) := by
    field_simp
  rw [e]
  exact h

/-- **Per-direction variance ratio** `(tλᵢ + γ)/(tλᵢ) = 1 + γ/(tλᵢ)` of the unlocalised to the
localised Laplace variance, between `1 + γ/(tλ_max)` and `1 + γ/(tλ_min)`. -/
theorem localised_variance_ratio_bounds {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) {pmin pmax : ℝ} (hpmin : 0 < pmin) (hmin : ∀ i, pmin ≤ hH.1.eigenvalues i)
    (hmax : ∀ i, hH.1.eigenvalues i ≤ pmax) (i : ι) :
    (t * hH.1.eigenvalues i + γ) / (t * hH.1.eigenvalues i) = 1 + γ / (t * hH.1.eigenvalues i) ∧
      1 + γ / (t * pmax) ≤ 1 + γ / (t * hH.1.eigenvalues i) ∧
      1 + γ / (t * hH.1.eigenvalues i) ≤ 1 + γ / (t * pmin) := by
  have hp := hH.eigenvalues_pos i
  have hpmax : 0 < pmax := lt_of_lt_of_le hp (hmax i)
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · have := div_le_div_of_nonneg_left hγ (by positivity : 0 < t * hH.1.eigenvalues i)
      (mul_le_mul_of_nonneg_left (hmax i) ht.le)
    linarith
  · have := div_le_div_of_nonneg_left hγ (by positivity : 0 < t * pmin)
      (mul_le_mul_of_nonneg_left (hmin i) ht.le)
    linarith

end Laplace.Sampler
