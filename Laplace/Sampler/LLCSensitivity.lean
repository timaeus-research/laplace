/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.LLCClosures

/-!
# The LLC is the sensitive diagnostic (E1, E5, E8)

The Sanity on Sampling note observes three times that a per-direction inflation of the sampled
covariance shows up in the LLC much more than in the whole-covariance trace: E1 ("the LLC inherits
this bias direction by direction"), E5 ("within 0.2% of `P⁻¹` in Frobenius norm while the LLC is
44% high"), E8 ("the whole-covariance trace inflates much less … because the noise lands on the
stiff directions: … the LLC is the sensitive diagnostic and the Frobenius norm is not"). The
mechanism is a re-weighting: the LLC averages the per-direction inflation with weights that grow
with the stiffness `pᵢ`, the trace with weights `∝ 1/pᵢ`.

* `sum_mul_sum_le_of_monovary`, `weighted_mean_le_of_monovary`: **weighted Chebyshev** — for
  weights `v ≥ 0` and `f` monovarying with `r`, `(∑ v f)/(∑ v) ≤ (∑ v r f)/(∑ v r)`;
* `trace_inv_eq_sum`, `trace_ulaCov`, `trace_minibatchCov`: the traces in the eigenbasis;
* `ula_llc_inflation_ge_trace_inflation`: `tr Σ_ULA / tr P⁻¹ ≤ LLC_ULA / (d/2)` for every spectrum
  and stable step (E1, E5);
* `minibatch_llc_inflation_ge_trace_inflation`: `tr Σ_mb / tr Σ_ULA ≤ LLC_mb / LLC_ULA` when the
  gradient-noise variances `c̃ᵢ` along the eigendirections are monovarying with `pᵢ` ("the noise
  lands on the stiff directions", E8); `minibatch_trace_inflation_ge_llc_inflation` is the
  reverse under antivarying noise.
-/

open Matrix Finset

namespace Laplace.Sampler

/-! ### Weighted Chebyshev -/

section Chebyshev

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Each pair contributes nonnegatively when `f` monovaries with `r`. -/
theorem mul_sub_mul_sub_nonneg_of_monovary {r f : ι → ℝ} (hfr : Monovary f r) (i j : ι) :
    0 ≤ (r i - r j) * (f i - f j) := by
  rcases lt_trichotomy (r i) (r j) with h | h | h
  · have := hfr h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · rw [h, sub_self, zero_mul]
  · have := hfr h
    exact mul_nonneg (by linarith) (by linarith)

/-- **The weighted Chebyshev identity**:
`∑ᵢⱼ vᵢ vⱼ (rᵢ − rⱼ)(fᵢ − fⱼ) = 2((∑ v r f)(∑ v) − (∑ v r)(∑ v f))`. -/
theorem sum_sum_mul_sub_mul_sub (v r f : ι → ℝ) :
    ∑ i, ∑ j, v i * v j * ((r i - r j) * (f i - f j)) =
      2 * ((∑ i, v i * r i * f i) * (∑ i, v i) - (∑ i, v i * r i) * (∑ i, v i * f i)) := by
  have hterm : ∀ i j, v i * v j * ((r i - r j) * (f i - f j)) =
      v i * r i * f i * v j - v i * r i * (v j * f j) - v i * f i * (v j * r j) +
        v i * (v j * r j * f j) := fun i j => by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

/-- **Weighted Chebyshev under the covariance condition**: if
`∑ᵢⱼ vᵢ vⱼ (rᵢ − rⱼ)(fᵢ − fⱼ) ≥ 0` then `(∑ v r)(∑ v f) ≤ (∑ v r f)(∑ v)`. -/
theorem sum_mul_sum_le_of_cov_nonneg (v r f : ι → ℝ)
    (hcov : 0 ≤ ∑ i, ∑ j, v i * v j * ((r i - r j) * (f i - f j))) :
    (∑ i, v i * r i) * (∑ i, v i * f i) ≤ (∑ i, v i * r i * f i) * (∑ i, v i) := by
  rw [sum_sum_mul_sub_mul_sub] at hcov
  linarith

/-- **Weighted Chebyshev**: `(∑ v r)(∑ v f) ≤ (∑ v r f)(∑ v)` for `v ≥ 0` and `f` monovarying
with `r`. -/
theorem sum_mul_sum_le_of_monovary (v r f : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (hfr : Monovary f r) :
    (∑ i, v i * r i) * (∑ i, v i * f i) ≤ (∑ i, v i * r i * f i) * (∑ i, v i) := by
  have hsum : 0 ≤ ∑ i, ∑ j, v i * v j * ((r i - r j) * (f i - f j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hv i) (hv j)) (mul_sub_mul_sub_nonneg_of_monovary hfr i j)
  exact sum_mul_sum_le_of_cov_nonneg v r f hsum

/-- The reversed inequality for `f` antivarying with `r`. -/
theorem sum_mul_sum_ge_of_antivary (v r f : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (hfr : Antivary f r) :
    (∑ i, v i * r i * f i) * (∑ i, v i) ≤ (∑ i, v i * r i) * (∑ i, v i * f i) := by
  have hmono : Monovary (fun i => -f i) r := fun i j hij => by
    have := hfr hij
    linarith
  have := sum_mul_sum_le_of_monovary v r (fun i => -f i) hv hmono
  simp only [mul_neg, Finset.sum_neg_distrib, neg_mul] at this
  linarith


/-- **Re-weighting an average by a factor comonotone with `f` can only increase it**:
`(∑ v f)/(∑ v) ≤ (∑ v r f)/(∑ v r)` for `v, r > 0` and `f` monovarying with `r`. -/
theorem weighted_mean_le_of_monovary [Nonempty ι] (v r f : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hr : ∀ i, 0 < r i) (hfr : Monovary f r) :
    (∑ i, v i * f i) / (∑ i, v i) ≤ (∑ i, v i * r i * f i) / (∑ i, v i * r i) := by
  have h1 : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  have h2 : 0 < ∑ i, v i * r i :=
    Finset.sum_pos (fun i _ => mul_pos (hv i) (hr i)) Finset.univ_nonempty
  rw [div_le_div_iff₀ h1 h2]
  have := sum_mul_sum_le_of_monovary v r f (fun i => (hv i).le) hfr
  linarith

/-- The reversed mean inequality for `f` antivarying with `r`. -/
theorem weighted_mean_ge_of_antivary [Nonempty ι] (v r f : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hr : ∀ i, 0 < r i) (hfr : Antivary f r) :
    (∑ i, v i * r i * f i) / (∑ i, v i * r i) ≤ (∑ i, v i * f i) / (∑ i, v i) := by
  have h1 : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  have h2 : 0 < ∑ i, v i * r i :=
    Finset.sum_pos (fun i _ => mul_pos (hv i) (hr i)) Finset.univ_nonempty
  rw [div_le_div_iff₀ h2 h1]
  have := sum_mul_sum_ge_of_antivary v r f (fun i => (hv i).le) hfr
  linarith

/-- **The Laplace instance**: a per-direction inflation `f` comonotone with the stiffness `p` has
a larger uniform average (the LLC's weighting, `½ ∑ fᵢ` against `d/2`) than its `1/p`-weighted
average (the covariance trace's weighting, `∑ fᵢ/pᵢ` against `∑ 1/pᵢ`). -/
theorem inv_weighted_mean_le_uniform_mean [Nonempty ι] (p f : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hfp : Monovary f p) :
    (∑ i, 1 / p i * f i) / (∑ i, 1 / p i) ≤ (∑ i, f i) / Fintype.card ι := by
  have key := weighted_mean_le_of_monovary (fun i => 1 / p i) p f
    (fun i => by have := hp i; positivity) hp hfp
  have e : ∀ i, 1 / p i * p i = (1 : ℝ) := fun i => one_div_mul_cancel (hp i).ne'
  simp only [e, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at key
  exact key

end Chebyshev

/-! ### Traces in the eigenbasis -/

section Traces

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Uᵀ P⁻¹ U = diag(1/pᵢ)` for `P` positive definite. -/
theorem orthoOf_transpose_inv_mul {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (orthoOf hP.1)ᵀ * P⁻¹ * orthoOf hP.1 = diagonal (fun i => 1 / hP.1.eigenvalues i) := by
  have hconj := orthoOf_transpose_mul_mul hP.1
  have hUU : (orthoOf hP.1)ᵀ * orthoOf hP.1 = 1 := orthoOf_transpose_mul hP.1
  have hUU' : orthoOf hP.1 * (orthoOf hP.1)ᵀ = 1 := orthoOf_mul_transpose hP.1
  have hinv : P⁻¹ =
      orthoOf hP.1 * diagonal (fun i => 1 / hP.1.eigenvalues i) * (orthoOf hP.1)ᵀ := by
    apply Matrix.inv_eq_left_inv
    have hre : orthoOf hP.1 * diagonal (fun i => 1 / hP.1.eigenvalues i) * (orthoOf hP.1)ᵀ * P =
        orthoOf hP.1 * diagonal (fun i => 1 / hP.1.eigenvalues i) *
          ((orthoOf hP.1)ᵀ * P * orthoOf hP.1) * (orthoOf hP.1)ᵀ := by
      simp only [Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [hre, hconj, Matrix.mul_assoc (orthoOf hP.1), diagonal_mul_diagonal]
    have hd : (fun i => 1 / hP.1.eigenvalues i * hP.1.eigenvalues i) = fun _ => (1 : ℝ) :=
      funext fun i => one_div_mul_cancel (hP.eigenvalues_pos i).ne'
    rw [hd, diagonal_one, Matrix.mul_one, hUU']
  rw [hinv]
  simp only [← Matrix.mul_assoc]
  rw [hUU, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- `tr P⁻¹ = ∑ᵢ 1/pᵢ`. -/
theorem trace_inv_eq_sum {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    P⁻¹.trace = ∑ i, 1 / hP.1.eigenvalues i := by
  have hUU' : orthoOf hP.1 * (orthoOf hP.1)ᵀ = 1 := orthoOf_mul_transpose hP.1
  rw [← trace_diagonal (fun i => 1 / hP.1.eigenvalues i), ← orthoOf_transpose_inv_mul hP,
    Matrix.trace_mul_cycle, hUU', Matrix.one_mul]

/-- `tr Σ_ULA = ∑ᵢ 1/(pᵢ(1 − h pᵢ/2))`. -/
theorem trace_ulaCov {P : Matrix ι ι ℝ} (hP : P.PosDef) (h : ℝ) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) :
    (ulaCov P h).trace = ∑ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := by
  have hUU' : orthoOf hP.1 * (orthoOf hP.1)ᵀ = 1 := orthoOf_mul_transpose hP.1
  rw [← trace_diagonal (fun i => 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))),
    ← ulaCov_conj_eq_diagonal hP.1 h hh (fun i => ⟨hP.eigenvalues_pos i, hev i⟩),
    Matrix.trace_mul_cycle, hUU', Matrix.one_mul]

/-- `tr Σ_mb = ∑ᵢ (1 + h t² c̃ᵢ/2)/(pᵢ(1 − h pᵢ/2))`, `c̃ᵢ = (UᵀCU)ᵢᵢ`. -/
theorem trace_minibatchCov {P : Matrix ι ι ℝ} (hP : P.PosDef) (h t : ℝ) (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (C : Matrix ι ι ℝ) :
    (minibatchCov hP.1 h t C).trace =
      ∑ i, (1 + h * t ^ 2 * ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i / 2) /
        (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := by
  have hUU' : orthoOf hP.1 * (orthoOf hP.1)ᵀ = 1 := orthoOf_mul_transpose hP.1
  have h1 : (minibatchCov hP.1 h t C).trace =
      ((orthoOf hP.1)ᵀ * minibatchCov hP.1 h t C * orthoOf hP.1).trace := by
    rw [Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
  rw [h1]
  unfold Matrix.trace Matrix.diag
  refine Finset.sum_congr rfl fun i _ => ?_
  exact minibatchCov_conj_diag hP.1 h t hh (fun i => ⟨hP.eigenvalues_pos i, hev i⟩) C i

end Traces

/-! ### The instances -/

section Instances

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **E1/E5: the relative inflation of the covariance trace is at most that of the LLC**, for every
spectrum and stable step: `tr Σ_ULA / tr P⁻¹ ≤ (½ ∑ 1/(1 − h pᵢ/2)) / (d/2)`. -/
theorem ula_llc_inflation_ge_trace_inflation [Nonempty ι] {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * hP.1.eigenvalues i < 2) :
    (ulaCov P h).trace / P⁻¹.trace ≤
      (1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) / (Fintype.card ι / 2) := by
  rw [trace_ulaCov hP h hh hev, trace_inv_eq_sum hP]
  have hq : ∀ i, 0 < 1 - h * hP.1.eigenvalues i / 2 := fun i => by have := hev i; linarith
  have hfr : Monovary (fun i => 1 / (1 - h * hP.1.eigenvalues i / 2)) hP.1.eigenvalues := by
    intro i j hij
    exact one_div_le_one_div_of_le (hq j) (by nlinarith)
  have key := weighted_mean_le_of_monovary (fun i => 1 / hP.1.eigenvalues i) hP.1.eigenvalues
    (fun i => 1 / (1 - h * hP.1.eigenvalues i / 2))
    (fun i => by have := hP.eigenvalues_pos i; positivity) hP.eigenvalues_pos hfr
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have e1 : ∀ i, 1 / hP.1.eigenvalues i * (1 / (1 - h * hP.1.eigenvalues i / 2)) =
      1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := fun i => by
    rw [one_div_mul_one_div]
  have e3 : ∀ i, 1 / hP.1.eigenvalues i * hP.1.eigenvalues i = (1 : ℝ) := fun i =>
    one_div_mul_cancel (hP.eigenvalues_pos i).ne'
  simp only [e1, e3, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at key
  calc (∑ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) /
        ∑ i, 1 / hP.1.eigenvalues i
      ≤ (∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) / Fintype.card ι := key
    _ = (1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) / (Fintype.card ι / 2) := by
        field_simp

/-- **E8: with the gradient noise on the stiff directions, the LLC inflates more than the trace**:
if the noise variances `c̃ᵢ = (UᵀCU)ᵢᵢ` along the eigendirections monovary with the eigenvalues,
`tr Σ_mb / tr Σ_ULA ≤ LLC_mb / LLC_ULA`. -/
theorem minibatch_llc_inflation_ge_trace_inflation [Nonempty ι] {H : Matrix ι ι ℝ} (t h : ℝ)
    (hP : (t • H).PosDef) (hh : 0 < h) (hev : ∀ i, h * hP.1.eigenvalues i < 2)
    (C : Matrix ι ι ℝ)
    (hmono : Monovary (fun i => ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i) hP.1.eigenvalues) :
    (minibatchCov hP.1 h t C).trace / (ulaCov (t • H) h).trace ≤
      (t / 2 * (H * minibatchCov hP.1 h t C).trace) / (t / 2 * (H * ulaCov (t • H) h).trace) := by
  rw [trace_minibatchCov hP h t hh hev, trace_ulaCov hP h hh hev, minibatch_llc t h hP hh hev,
    ula_llc t h hP hh hev]
  set c : ι → ℝ := fun i => ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i with hc
  have hq : ∀ i, 0 < 1 - h * hP.1.eigenvalues i / 2 := fun i => by have := hev i; linarith
  have hfr : Monovary (fun i => 1 + h * t ^ 2 * c i / 2) hP.1.eigenvalues := by
    intro i j hij
    have := hmono hij
    have ht2 : 0 ≤ h * t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this ht2]
  have key := weighted_mean_le_of_monovary
    (fun i => 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) hP.1.eigenvalues
    (fun i => 1 + h * t ^ 2 * c i / 2)
    (fun i => by have := hP.eigenvalues_pos i; have := hq i; positivity) hP.eigenvalues_pos hfr
  have e1 : ∀ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      (1 + h * t ^ 2 * c i / 2) =
      (1 + h * t ^ 2 * c i / 2) / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) :=
    fun i => by rw [one_div_mul_eq_div]
  have e3 : ∀ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      hP.1.eigenvalues i = 1 / (1 - h * hP.1.eigenvalues i / 2) := fun i => by
    have := (hP.eigenvalues_pos i).ne'
    have := (hq i).ne'
    field_simp
  simp only [e1, e3, one_div_mul_eq_div] at key
  have hpos : 0 < ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) :=
    Finset.sum_pos (fun i _ => by have := hq i; positivity) Finset.univ_nonempty
  calc (∑ i, (1 + h * t ^ 2 * c i / 2) / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) /
        ∑ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))
      ≤ (∑ i, (1 + h * t ^ 2 * c i / 2) / (1 - h * hP.1.eigenvalues i / 2)) /
        ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) := key
    _ = (1 / 2 * ∑ i, (1 + h * t ^ 2 * c i / 2) / (1 - h * hP.1.eigenvalues i / 2)) /
        (1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2)) := by
        rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]

/-- **The reverse under noise on the flat directions**: if the noise variances antivary with the
eigenvalues, the trace inflates at least as much as the LLC. -/
theorem minibatch_trace_inflation_ge_llc_inflation [Nonempty ι] {H : Matrix ι ι ℝ} (t h : ℝ)
    (hP : (t • H).PosDef) (hh : 0 < h) (hev : ∀ i, h * hP.1.eigenvalues i < 2)
    (C : Matrix ι ι ℝ)
    (hanti : Antivary (fun i => ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i) hP.1.eigenvalues) :
    (t / 2 * (H * minibatchCov hP.1 h t C).trace) / (t / 2 * (H * ulaCov (t • H) h).trace) ≤
      (minibatchCov hP.1 h t C).trace / (ulaCov (t • H) h).trace := by
  rw [trace_minibatchCov hP h t hh hev, trace_ulaCov hP h hh hev, minibatch_llc t h hP hh hev,
    ula_llc t h hP hh hev]
  set c : ι → ℝ := fun i => ((orthoOf hP.1)ᵀ * C * orthoOf hP.1) i i with hc
  have hq : ∀ i, 0 < 1 - h * hP.1.eigenvalues i / 2 := fun i => by have := hev i; linarith
  have hfr : Antivary (fun i => 1 + h * t ^ 2 * c i / 2) hP.1.eigenvalues := by
    intro i j hij
    have := hanti hij
    have ht2 : 0 ≤ h * t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this ht2]
  have key := weighted_mean_ge_of_antivary
    (fun i => 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) hP.1.eigenvalues
    (fun i => 1 + h * t ^ 2 * c i / 2)
    (fun i => by have := hP.eigenvalues_pos i; have := hq i; positivity) hP.eigenvalues_pos hfr
  have e1 : ∀ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      (1 + h * t ^ 2 * c i / 2) =
      (1 + h * t ^ 2 * c i / 2) / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) :=
    fun i => by rw [one_div_mul_eq_div]
  have e3 : ∀ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) *
      hP.1.eigenvalues i = 1 / (1 - h * hP.1.eigenvalues i / 2) := fun i => by
    have := (hP.eigenvalues_pos i).ne'
    have := (hq i).ne'
    field_simp
  simp only [e1, e3, one_div_mul_eq_div] at key
  calc (1 / 2 * ∑ i, (1 + h * t ^ 2 * c i / 2) / (1 - h * hP.1.eigenvalues i / 2)) /
        (1 / 2 * ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2))
      = (∑ i, (1 + h * t ^ 2 * c i / 2) / (1 - h * hP.1.eigenvalues i / 2)) /
        ∑ i, 1 / (1 - h * hP.1.eigenvalues i / 2) := by
        rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    _ ≤ (∑ i, (1 + h * t ^ 2 * c i / 2) / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2))) /
        ∑ i, 1 / (hP.1.eigenvalues i * (1 - h * hP.1.eigenvalues i / 2)) := key

end Instances

end Laplace.Sampler
