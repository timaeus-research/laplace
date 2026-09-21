/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.Minibatch
import Laplace.Sampler.LLCClosures

/-!
# The minibatch rule of thumb and the batch-size rule (E8)

E8 of the Sanity on Sampling note: "For `lr pᵢ ≪ 1` the relative excess of the LLC is
`lr t² tr(C_g)/(2d) ≈ lr pmax t tr(S²)/(2 d λmax m)` … Keeping the excess below `ε` needs
`m ≳ lr pmax t tr(S²)/(2 d λmax ε)`, or equivalently a step size shrinking like `1/t²` rather than
`1/t`." The seabed has the first form as a two-sided bound (`minibatch_inflation_normalised`) and
the gradient-noise covariance `C_g = (1/m)(1 − m/n) S²` (`minibatch_gradient_cov`). Here:

* `minibatchGradCov`, `minibatchGradCov_posSemidef`, `trace_minibatchGradCov`:
  `C_g` is positive semidefinite with `tr C_g = (1/m)(1 − m/n) tr S²`;
* `minibatch_excess_bounds_note`: with `pmax = t λmax` the normalised excess
  `(LLC_mb − LLC_ULA)/(d/2)` lies between `(h pmax) t (1 − m/n) tr S²/(2 d λmax m)` and that over
  `1 − h pmax/2` — the note's rule of thumb, with its finite-population factor `1 − m/n` restored;
* `batch_size_rule`: `m ≥ (h pmax) t tr S²/(2 d λmax ε (1 − h pmax/2))` keeps the excess below
  `ε`;
* `step_size_rule`: at fixed `C_g`, `h t² tr C_g ≤ 2 d ε (1 − h pmax/2)` keeps it below `ε`, so `h`
  must shrink like `1/t²`.
-/

open Finset Matrix

namespace Laplace.Sampler

/-! ### The gradient-noise covariance -/

section PSD

variable {ι : Type*} [Finite ι]

/-- A real outer product `v vᵀ` is positive semidefinite. -/
theorem posSemidef_vecMulVec_self (v : ι → ℝ) : (vecMulVec v v).PosSemidef := by
  have h := posSemidef_vecMulVec_self_star v
  simpa using h

/-- The sample covariance of the per-sample gradients is positive semidefinite. -/
theorem sampleCov_posSemidef {n : ℕ} (hn : 2 ≤ n) (g : Fin n → ι → ℝ) :
    (sampleCov g).PosSemidef := by
  unfold sampleCov
  refine (posSemidef_sum univ fun i _ => posSemidef_vecMulVec_self _).smul ?_
  have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  positivity

/-- The gradient-noise covariance `C_g = (1/m)(1 − m/n) S²` of the minibatch mean gradient. -/
noncomputable def minibatchGradCov {n : ℕ} (m : ℕ) (g : Fin n → ι → ℝ) : Matrix ι ι ℝ :=
  ((m : ℝ)⁻¹ * (1 - (m : ℝ) / n)) • sampleCov g

theorem minibatchGradCov_posSemidef {n m : ℕ} (hmn : m ≤ n) (hn : 2 ≤ n) (g : Fin n → ι → ℝ) :
    (minibatchGradCov m g).PosSemidef := by
  unfold minibatchGradCov
  refine (sampleCov_posSemidef hn g).smul ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h1 : (0 : ℝ) ≤ 1 - (m : ℝ) / n := by
    rw [sub_nonneg, div_le_one hn']
    exact hmn'
  positivity

end PSD

section Trace

variable {ι : Type*} [Fintype ι]

/-- `tr C_g = (1/m)(1 − m/n) tr S²`. -/
theorem trace_minibatchGradCov {n : ℕ} (m : ℕ) (g : Fin n → ι → ℝ) :
    (minibatchGradCov m g).trace = (m : ℝ)⁻¹ * (1 - (m : ℝ) / n) * (sampleCov g).trace := by
  unfold minibatchGradCov
  rw [trace_smul, smul_eq_mul]

end Trace

/-! ### The rule of thumb in the note's variables -/

section Rules

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **E8's rule of thumb**: with `pmax = t λmax`, `1 ≤ m ≤ n`, the LLC excess normalised by `d/2`
lies between `(h pmax) t (1 − m/n) tr S²/(2 d λmax m)` and that divided by `1 − h pmax/2`. -/
theorem minibatch_excess_bounds_note {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef)
    (hh : 0 < h) (ht : 0 < t) {lmax : ℝ} (hlmax : 0 < lmax)
    (hpmax : ∀ i, hP.1.eigenvalues i ≤ t * lmax) (hstab : h * (t * lmax) < 2)
    (hd : 0 < Fintype.card ι) {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (g : Fin n → ι → ℝ) :
    h * (t * lmax) * t * (1 - (m : ℝ) / n) * (sampleCov g).trace /
        (2 * Fintype.card ι * lmax * m) ≤
      (t / 2 * (H * minibatchCov hP.1 h t (minibatchGradCov m g)).trace -
        t / 2 * (H * ulaCov (t • H) h).trace) / (Fintype.card ι / 2) ∧
    (t / 2 * (H * minibatchCov hP.1 h t (minibatchGradCov m g)).trace -
        t / 2 * (H * ulaCov (t • H) h).trace) / (Fintype.card ι / 2) ≤
      h * (t * lmax) * t * (1 - (m : ℝ) / n) * (sampleCov g).trace /
        (2 * Fintype.card ι * lmax * m * (1 - h * (t * lmax) / 2)) := by
  obtain ⟨hlo, hhi⟩ := minibatch_inflation_normalised t h hP hh hpmax hstab
    (minibatchGradCov_posSemidef hmn hn g) hd
  rw [trace_minibatchGradCov] at hlo hhi
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hd' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq : 1 - h * (t * lmax) / 2 ≠ 0 := by linarith
  have e1 : h * t ^ 2 * ((m : ℝ)⁻¹ * (1 - (m : ℝ) / n) * (sampleCov g).trace) /
      (2 * Fintype.card ι) =
      h * (t * lmax) * t * (1 - (m : ℝ) / n) * (sampleCov g).trace /
        (2 * Fintype.card ι * lmax * m) := by
    field_simp
  have e2 : h * t ^ 2 * ((m : ℝ)⁻¹ * (1 - (m : ℝ) / n) * (sampleCov g).trace) /
      (2 * Fintype.card ι * (1 - h * (t * lmax) / 2)) =
      h * (t * lmax) * t * (1 - (m : ℝ) / n) * (sampleCov g).trace /
        (2 * Fintype.card ι * lmax * m * (1 - h * (t * lmax) / 2)) := by
    field_simp
  exact ⟨e1 ▸ hlo, e2 ▸ hhi⟩

/-- **The batch-size rule**: `m ≥ (h pmax) t tr S²/(2 d λmax ε (1 − h pmax/2))` keeps the normalised
LLC excess below `ε`. -/
theorem batch_size_rule {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h) (ht : 0 < t)
    {lmax : ℝ} (hlmax : 0 < lmax) (hpmax : ∀ i, hP.1.eigenvalues i ≤ t * lmax)
    (hstab : h * (t * lmax) < 2) (hd : 0 < Fintype.card ι) {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : 2 ≤ n) (g : Fin n → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hmge : h * (t * lmax) * t * (sampleCov g).trace /
      (2 * Fintype.card ι * lmax * ε * (1 - h * (t * lmax) / 2)) ≤ m) :
    (t / 2 * (H * minibatchCov hP.1 h t (minibatchGradCov m g)).trace -
        t / 2 * (H * ulaCov (t • H) h).trace) / (Fintype.card ι / 2) ≤ ε := by
  have hhi := (minibatch_excess_bounds_note t h hP hh ht hlmax hpmax hstab hd hm hmn hn g).2
  refine le_trans hhi ?_
  have hq : 0 < 1 - h * (t * lmax) / 2 := by linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htr : 0 ≤ (sampleCov g).trace := (sampleCov_posSemidef hn g).trace_nonneg
  have hfpc : (1 - (m : ℝ) / n) ≤ 1 := by
    have : 0 ≤ (m : ℝ) / n := by positivity
    linarith
  have hfpc0 : 0 ≤ 1 - (m : ℝ) / n := by
    rw [sub_nonneg, div_le_one hn']
    exact_mod_cast hmn
  set K := h * (t * lmax) * t * (sampleCov g).trace with hK
  have hK0 : 0 ≤ K := by positivity
  -- K (1 − m/n)/(2 d λ m q) ≤ K/(2 d λ m q) ≤ ε  from  K/(2 d λ ε q) ≤ m
  have h1 : h * (t * lmax) * t * (1 - (m : ℝ) / n) * (sampleCov g).trace /
      (2 * Fintype.card ι * lmax * m * (1 - h * (t * lmax) / 2)) ≤
      K / (2 * Fintype.card ι * lmax * m * (1 - h * (t * lmax) / 2)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hfpc
      (by positivity : 0 ≤ h * (t * lmax) * t * (sampleCov g).trace)]
  refine le_trans h1 ?_
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hmge
  nlinarith [hmge]

/-- **The step-size rule**: at fixed gradient-noise covariance, `h t² tr C_g ≤ 2 d ε (1 − h pmax/2)`
keeps the normalised LLC excess below `ε` — a step shrinking like `1/t²`. -/
theorem step_size_rule {H : Matrix ι ι ℝ} (t h : ℝ) (hP : (t • H).PosDef) (hh : 0 < h)
    {pmax : ℝ} (hpmax : ∀ i, hP.1.eigenvalues i ≤ pmax) (hstab : h * pmax < 2)
    (hd : 0 < Fintype.card ι) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {ε : ℝ}
    (hstep : h * t ^ 2 * C.trace ≤ 2 * Fintype.card ι * ε * (1 - h * pmax / 2)) :
    (t / 2 * (H * minibatchCov hP.1 h t C).trace - t / 2 * (H * ulaCov (t • H) h).trace) /
      (Fintype.card ι / 2) ≤ ε := by
  have hhi := (minibatch_inflation_normalised t h hP hh hpmax hstab hC hd).2
  refine le_trans hhi ?_
  have hq : 0 < 1 - h * pmax / 2 := by linarith
  have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  rw [div_le_iff₀ (by positivity)]
  linarith

end Rules

end Laplace.Sampler
