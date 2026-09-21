/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.LLCMSE

/-!
# The spectrum-free E4 error budget for the LLC

Tide `llc-mse` bounds the relative RMS error of the pooled LLC against `d/2` by three spectral sums
(`llc_rel_rms_le`). Here each per-direction term is bounded by its value on the extreme directions,
giving the Sanity on Sampling note's recipe in closed form: with `r = 1 − h pmin` (the flattest
direction's AR(1) coefficient), `pmin ≤ pᵢ ≤ pmax`, `0 < h pmin`, `h pmax ≤ 1`,

  `√E(LLĈ − d/2)²/(d/2) ≤ 2√(d/(2CN) · τ(r²)/(1 − h pmax/2)²)/d + (h pmax/2)/(1 − h pmax/2)
                              + r^{2(b+1)}/(N(1 − r²)(1 − h pmin/2))`,

`τ(r²) = (1 + r²)/(1 − r²)` the autocorrelation time of the squared flattest coordinate.

* `tau_mono`, `excess_mono`, `burnin_term_eq`, `burnin_term_mono`: the per-direction terms are
  monotone in `ρ`; the burn-in term is `2ρ^{2b}/(1 − ρ) · (ρ/(1 + ρ))²`, a product of increasing
  factors (its denominator alone is not monotone);
* `inflation_sum_le_free`, `shortfall_bd_sum_le_free`, `envelope_sum_le_free`: the three sums
  bounded by `d` times the extreme-direction value;
* `llc_rel_rms_le_free`: the spectrum-free three-term bound on the ULA chain with Gaussian noise.
-/

open Finset

namespace Laplace.Sampler

/-! ### Per-direction monotonicity -/

section Monotone

/-- `(1 + ρ²)/(1 − ρ²)` is increasing on `[0, 1)`. -/
theorem tau_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') (h1 : ρ' < 1) :
    (1 + ρ ^ 2) / (1 - ρ ^ 2) ≤ (1 + ρ' ^ 2) / (1 - ρ' ^ 2) := by
  have hρ1 : ρ < 1 := lt_of_le_of_lt h h1
  have hd : 0 < 1 - ρ ^ 2 := by nlinarith
  have hd' : 0 < 1 - ρ' ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hd hd']
  nlinarith [mul_le_mul h h h0 (by linarith)]

/-- `x/(1 − x)` is increasing on `[0, 1)`. -/
theorem excess_mono {x x' : ℝ} (h : x ≤ x') (h1 : x' < 1) :
    x / (1 - x) ≤ x' / (1 - x') := by
  have hx1 : x < 1 := lt_of_le_of_lt h h1
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The burn-in term factorises:
`ρ^{2(b+1)}/((1 − ρ²)(1 + ρ)/2) = 2ρ^{2b}/(1 − ρ) · (ρ/(1 + ρ))²`. -/
theorem burnin_term_eq {ρ : ℝ} (h0 : -1 < ρ) (h1 : ρ < 1) (b : ℕ) :
    ρ ^ (2 * (b + 1)) / ((1 - ρ ^ 2) * ((1 + ρ) / 2)) =
      2 * ρ ^ (2 * b) / (1 - ρ) * (ρ / (1 + ρ)) ^ 2 := by
  have hne : 1 - ρ ≠ 0 := (sub_pos.mpr h1).ne'
  have hne' : 1 + ρ ≠ 0 := by
    rw [add_comm]
    exact (neg_lt_iff_pos_add.mp h0).ne'
  have hd : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
  rw [hd]
  field_simp
  ring

/-- `ρ/(1 + ρ)` is increasing on `[0, ∞)`. -/
theorem div_one_add_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') :
    ρ / (1 + ρ) ≤ ρ' / (1 + ρ') := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The burn-in term is increasing in `ρ` on `[0, 1)`** (coupled monotonicity of the three
factors of `burnin_term_eq`). -/
theorem burnin_term_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') (h1 : ρ' < 1) (b : ℕ) :
    ρ ^ (2 * (b + 1)) / ((1 - ρ ^ 2) * ((1 + ρ) / 2)) ≤
      ρ' ^ (2 * (b + 1)) / ((1 - ρ' ^ 2) * ((1 + ρ') / 2)) := by
  have hρ1 : ρ < 1 := lt_of_le_of_lt h h1
  have h0' : 0 ≤ ρ' := le_trans h0 h
  rw [burnin_term_eq (by linarith) hρ1 b, burnin_term_eq (by linarith) h1 b]
  have f1 : ρ ^ (2 * b) ≤ ρ' ^ (2 * b) := pow_le_pow_left₀ h0 h _
  have f2 : 2 * ρ ^ (2 * b) / (1 - ρ) ≤ 2 * ρ' ^ (2 * b) / (1 - ρ') := by
    have hA : 2 * ρ ^ (2 * b) / (1 - ρ) ≤ 2 * ρ' ^ (2 * b) / (1 - ρ) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hB : 2 * ρ' ^ (2 * b) / (1 - ρ) ≤ 2 * ρ' ^ (2 * b) / (1 - ρ') :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    exact le_trans hA hB
  have f3 : (ρ / (1 + ρ)) ^ 2 ≤ (ρ' / (1 + ρ')) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (div_one_add_mono h0 h) 2
  exact mul_le_mul f2 f3 (by positivity) (by positivity)

end Monotone

/-! ### The three sums, spectrum-free -/

section Sums

variable {ι : Type*} [Fintype ι]

/-- **The ULA inflation is at most its stiffest-direction value.** -/
theorem inflation_sum_le_free {p : ι → ℝ} {h pmax : ℝ} (hh : 0 ≤ h) (hmax : ∀ i, p i ≤ pmax)
    (hstab : h * pmax ≤ 1) :
    1 / 2 * ∑ i, (h * p i / 2) / (1 - h * p i / 2) ≤
      Fintype.card ι / 2 * ((h * pmax / 2) / (1 - h * pmax / 2)) := by
  have hterm : ∀ i, (h * p i / 2) / (1 - h * p i / 2) ≤ (h * pmax / 2) / (1 - h * pmax / 2) :=
    fun i => excess_mono (by linarith [mul_le_mul_of_nonneg_left (hmax i) hh]) (by linarith)
  calc 1 / 2 * ∑ i, (h * p i / 2) / (1 - h * p i / 2)
      ≤ 1 / 2 * ∑ _i : ι, (h * pmax / 2) / (1 - h * pmax / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)
    _ = Fintype.card ι / 2 * ((h * pmax / 2) / (1 - h * pmax / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The burn-in shortfall bound is at most its flattest-direction value**, `r = 1 − h pmin`. -/
theorem shortfall_bd_sum_le_free {p : ι → ℝ} {h pmin pmax : ℝ} (hh : 0 < h) (hpmin : 0 < pmin)
    (hmin : ∀ i, pmin ≤ p i) (hmax : ∀ i, p i ≤ pmax) (hstab : h * pmax ≤ 1) {N : ℕ}
    (hN : 0 < N) (b : ℕ) :
    1 / 2 * ∑ i, (1 - h * p i) ^ (2 * (b + 1)) /
        (N * (1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2)) ≤
      Fintype.card ι / 2 * ((1 - h * pmin) ^ (2 * (b + 1)) /
        (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr1 : 1 - h * pmin < 1 := by linarith [mul_pos hh hpmin]
  have hterm : ∀ i, (1 - h * p i) ^ (2 * (b + 1)) /
      (N * (1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2)) ≤
      (1 - h * pmin) ^ (2 * (b + 1)) / (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)) := by
    intro i
    have hρ0 : 0 ≤ 1 - h * p i := by linarith [mul_le_mul_of_nonneg_left (hmax i) hh.le]
    have hρr : 1 - h * p i ≤ 1 - h * pmin := by linarith [mul_le_mul_of_nonneg_left (hmin i) hh.le]
    have e : ∀ ρ : ℝ, ρ ^ (2 * (b + 1)) / (N * (1 - ρ ^ 2) * ((1 + ρ) / 2)) =
        1 / N * (ρ ^ (2 * (b + 1)) / ((1 - ρ ^ 2) * ((1 + ρ) / 2))) := fun ρ => by
      rw [one_div_mul_eq_div, div_div]
      congr 1
      ring
    have e1 : 1 - h * p i / 2 = (1 + (1 - h * p i)) / 2 := by ring
    have e2 : 1 - h * pmin / 2 = (1 + (1 - h * pmin)) / 2 := by ring
    rw [e1, e2, e, e]
    exact mul_le_mul_of_nonneg_left (burnin_term_mono hρ0 hρr hr1 b) (by positivity)
  calc 1 / 2 * ∑ i, (1 - h * p i) ^ (2 * (b + 1)) /
        (N * (1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2))
      ≤ 1 / 2 * ∑ _i : ι, (1 - h * pmin) ^ (2 * (b + 1)) /
        (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)
    _ = Fintype.card ι / 2 * ((1 - h * pmin) ^ (2 * (b + 1)) /
        (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The variance envelope is at most `d` times the product of the two extreme factors**: the
autocorrelation factor of the flattest direction and the step factor of the stiffest. -/
theorem envelope_sum_le_free {p : ι → ℝ} {h pmin pmax : ℝ} (hh : 0 < h) (hpmin : 0 < pmin)
    (hpp : pmin ≤ pmax) (hmin : ∀ i, pmin ≤ p i) (hmax : ∀ i, p i ≤ pmax) (hstab : h * pmax ≤ 1)
    {C N : ℝ} (hC : 0 < C) (hN : 0 < N) :
    1 / (2 * C * N) * ∑ i, (1 + (1 - h * p i) ^ 2) /
        ((1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2) ^ 2) ≤
      Fintype.card ι / (2 * C * N) *
        ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2) := by
  have hr1 : 1 - h * pmin < 1 := by linarith [mul_pos hh hpmin]
  have hr0 : 0 ≤ 1 - h * pmin := by linarith [mul_le_mul_of_nonneg_left hpp hh.le]
  have hr2 : 0 < 1 - (1 - h * pmin) ^ 2 := by nlinarith
  have hq : 0 < 1 - h * pmax / 2 := by linarith
  have hterm : ∀ i, (1 + (1 - h * p i) ^ 2) / ((1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2) ^ 2) ≤
      (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2 := by
    intro i
    have hρ0 : 0 ≤ 1 - h * p i := by linarith [mul_le_mul_of_nonneg_left (hmax i) hh.le]
    have hρr : 1 - h * p i ≤ 1 - h * pmin := by linarith [mul_le_mul_of_nonneg_left (hmin i) hh.le]
    have hρ1 : 1 - h * p i < 1 := lt_of_le_of_lt hρr hr1
    have hd : 0 < 1 - (1 - h * p i) ^ 2 := by nlinarith
    have hqi : 1 - h * pmax / 2 ≤ 1 - h * p i / 2 := by
      linarith [mul_le_mul_of_nonneg_left (hmax i) hh.le]
    have hτ := tau_mono hρ0 hρr hr1
    have hstep : 1 / (1 - h * p i / 2) ^ 2 ≤ 1 / (1 - h * pmax / 2) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hq 2) (pow_le_pow_left₀ hq.le hqi 2)
    calc (1 + (1 - h * p i) ^ 2) / ((1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2) ^ 2)
        = (1 + (1 - h * p i) ^ 2) / (1 - (1 - h * p i) ^ 2) * (1 / (1 - h * p i / 2) ^ 2) := by
          rw [div_mul_div_comm, mul_one]
      _ ≤ (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) * (1 / (1 - h * pmax / 2) ^ 2) :=
          mul_le_mul hτ hstep (by positivity) (div_nonneg (by positivity) hr2.le)
      _ = (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2 := by
          rw [mul_one_div]
  calc 1 / (2 * C * N) * ∑ i, (1 + (1 - h * p i) ^ 2) /
        ((1 - (1 - h * p i) ^ 2) * (1 - h * p i / 2) ^ 2)
      ≤ 1 / (2 * C * N) * ∑ _i : ι,
        (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
    _ = Fintype.card ι / (2 * C * N) *
        ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Sums

/-! ### The spectrum-free three-term bound -/

section ULA

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The spectrum-free E4 error budget**: with `pmin ≤ pᵢ ≤ pmax`, `0 < h pmin`, `h pmax ≤ 1`,
`r = 1 − h pmin`,
`√E(LLĈ − d/2)²/(d/2) ≤ 2√(d/(2CN) · τ(r²)/(1 − h pmax/2)²)/d + (h pmax/2)/(1 − h pmax/2)
  + r^{2(b+1)}/(N(1 − r²)(1 − h pmin/2))`. -/
theorem llc_rel_rms_le_free [Nonempty ι] {H : Matrix ι ι ℝ} {t h pmin pmax : ℝ} (ht : 0 < t)
    (hh : 0 < h) (hP : (t • H).PosDef) (hpmin : 0 < pmin) (hmin : ∀ i, pmin ≤ hP.1.eigenvalues i)
    (hmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Real.sqrt (∫ ω, ((pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 : ℝ) ∂P) /
        (Fintype.card ι / 2) ≤
      2 * Real.sqrt (Fintype.card ι / (2 * C * N) *
          ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) / (1 - h * pmax / 2) ^ 2)) /
          Fintype.card ι +
        (h * pmax / 2) / (1 - h * pmax / 2) +
        (1 - h * pmin) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)) := by
  have hstab' : ∀ i, h * hP.1.eigenvalues i ≤ 1 := fun i =>
    le_trans (mul_le_mul_of_nonneg_left (hmax i) hh.le) hstab
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpp : pmin ≤ pmax := le_trans (hmin (Classical.arbitrary ι)) (hmax _)
  refine le_trans (llc_rel_rms_le ht hh hP hstab' hC hN b ξ hmeas hlaw hind) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- Monte Carlo term
    have := envelope_sum_le_free (p := hP.1.eigenvalues) hh hpmin hpp hmin hmax hstab hC' hN'
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt this) (by norm_num)) hd.le
  · -- ULA inflation
    have := inflation_sum_le_free (p := hP.1.eigenvalues) hh.le hmax hstab
    have e : (1 / (Fintype.card ι : ℝ)) * ∑ i, (h * hP.1.eigenvalues i / 2) /
        (1 - h * hP.1.eigenvalues i / 2) =
        (2 / Fintype.card ι) * (1 / 2 * ∑ i, (h * hP.1.eigenvalues i / 2) /
          (1 - h * hP.1.eigenvalues i / 2)) := by ring
    rw [e]
    calc (2 / (Fintype.card ι : ℝ)) * (1 / 2 * ∑ i, (h * hP.1.eigenvalues i / 2) /
          (1 - h * hP.1.eigenvalues i / 2))
        ≤ (2 / Fintype.card ι) * (Fintype.card ι / 2 * ((h * pmax / 2) / (1 - h * pmax / 2))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (h * pmax / 2) / (1 - h * pmax / 2) := by field_simp
  · -- burn-in
    have := shortfall_bd_sum_le_free (p := hP.1.eigenvalues) hh hpmin hmin hmax hstab hN b
    have e : (1 / ((Fintype.card ι : ℝ) * N)) * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
        ((1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)) =
        (2 / Fintype.card ι) * (1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [e]
    calc (2 / (Fintype.card ι : ℝ)) * (1 / 2 * ∑ i, (1 - h * hP.1.eigenvalues i) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * hP.1.eigenvalues i) ^ 2) * (1 - h * hP.1.eigenvalues i / 2)))
        ≤ (2 / Fintype.card ι) * (Fintype.card ι / 2 * ((1 - h * pmin) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (1 - h * pmin) ^ (2 * (b + 1)) / (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)) := by
          field_simp

/-- The Monte Carlo term in effective-sample-size form:
`2√(d/(2CN) · τ/q²)/d = √(2τ/(d·CN))/q` — the envelope-based effective sample size is `CN/τ(r²)`. -/
theorem monte_carlo_term_eq {d C N τ q : ℝ} (hd : 0 < d) (hC : 0 < C) (hN : 0 < N) (hτ : 0 ≤ τ)
    (hq : 0 < q) :
    2 * Real.sqrt (d / (2 * C * N) * (τ / q ^ 2)) / d = Real.sqrt (2 * τ / (d * C * N)) / q := by
  have hX : 0 ≤ d / (2 * C * N) * (τ / q ^ 2) := by positivity
  have hY : 0 ≤ 2 * τ / (d * C * N) := by positivity
  have hkey : (2 / d) ^ 2 * (d / (2 * C * N) * (τ / q ^ 2)) =
      (1 / q) ^ 2 * (2 * τ / (d * C * N)) := by
    field_simp
  calc 2 * Real.sqrt (d / (2 * C * N) * (τ / q ^ 2)) / d
      = Real.sqrt ((2 / d) ^ 2) * Real.sqrt (d / (2 * C * N) * (τ / q ^ 2)) := by
        rw [Real.sqrt_sq (by positivity)]
        ring
    _ = Real.sqrt ((2 / d) ^ 2 * (d / (2 * C * N) * (τ / q ^ 2))) :=
        (Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 / d) ^ 2) _).symm
    _ = Real.sqrt ((1 / q) ^ 2 * (2 * τ / (d * C * N))) := by rw [hkey]
    _ = Real.sqrt ((1 / q) ^ 2) * Real.sqrt (2 * τ / (d * C * N)) :=
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (1 / q) ^ 2) _
    _ = Real.sqrt (2 * τ / (d * C * N)) / q := by
        rw [Real.sqrt_sq (by positivity)]
        ring

/-- **The spectrum-free E4 error budget in the note's form**: with `τ(r²) = (1 + r²)/(1 − r²)`,
`√E(LLĈ − d/2)²/(d/2) ≤ √(2τ(r²)/(d·CN))/(1 − h pmax/2) + (h pmax/2)/(1 − h pmax/2)
  + r^{2(b+1)}/(N(1 − r²)(1 − h pmin/2))`. -/
theorem llc_rel_rms_le_free' [Nonempty ι] {H : Matrix ι ι ℝ} {t h pmin pmax : ℝ} (ht : 0 < t)
    (hh : 0 < h) (hP : (t • H).PosDef) (hpmin : 0 < pmin) (hmin : ∀ i, pmin ≤ hP.1.eigenvalues i)
    (hmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ}
    (hN : 0 < N) (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    Real.sqrt (∫ ω, ((pooledLLC H t h ξ N b ω - Fintype.card ι / 2) ^ 2 : ℝ) ∂P) /
        (Fintype.card ι / 2) ≤
      Real.sqrt (2 * ((1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2)) /
          (Fintype.card ι * C * N)) / (1 - h * pmax / 2) +
        (h * pmax / 2) / (1 - h * pmax / 2) +
        (1 - h * pmin) ^ (2 * (b + 1)) /
          (N * (1 - (1 - h * pmin) ^ 2) * (1 - h * pmin / 2)) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpp : pmin ≤ pmax := le_trans (hmin (Classical.arbitrary ι)) (hmax _)
  have hr0 : 0 ≤ 1 - h * pmin := by linarith [mul_le_mul_of_nonneg_left hpp hh.le]
  have hr1 : 1 - h * pmin < 1 := by linarith [mul_pos hh hpmin]
  have hτ : 0 ≤ (1 + (1 - h * pmin) ^ 2) / (1 - (1 - h * pmin) ^ 2) :=
    div_nonneg (by positivity) (by nlinarith)
  have hq : 0 < 1 - h * pmax / 2 := by linarith
  have h := llc_rel_rms_le_free ht hh hP hpmin hmin hmax hstab hC hN b ξ hmeas hlaw hind
  rwa [monte_carlo_term_eq hd hC' hN' hτ hq] at h

end ULA

end Laplace.Sampler
