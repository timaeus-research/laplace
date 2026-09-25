/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TiltLowerBound
import Laplace.Multi.ResponseStability

/-!
# Fluctuation–response: the sampling noise of the empirical response is the response form

For `n` independent samples from the member `P_{t,a}`, the empirical response `R̄_n` fluctuates in
the direction `v` with variance `Var(v·R̄_n) = (1/n) v ⬝ Cov_a(R,R) v` (`variance_empMean_dir`),
the covariance form of `ResponseStability` divided by `n`; and since the response derivative is
`Dm_t(a) v = −t Cov_a(R, R_v)`, this is `−(1/(nt)) v ⬝ Dm_t(a) v`
(`variance_empMean_dir_eq_meanMapDeriv`): the observable sampling noise of a response measures the
same covariance that governs its response to a change of the data — a finite-sample
fluctuation–response relation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit ht in
/-- The variance of a bounded observable under the member `P_{t,a}` is its posterior variance. -/
theorem variance_familyMeasure {f : X → ℝ} (hf : Bdd f) (a : ι → ℝ) :
    variance f (familyMeasure μ π L₀ R t a) = priorCov μ π (affLoss L₀ R a) f f t := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  rw [variance_eq_sub (memLp_two_of_bdd _ hf)]
  simp only [Pi.pow_apply]
  rw [integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a,
    integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a]
  unfold priorCov
  have e : (fun x ↦ f x ^ 2) = fun x ↦ f x * f x := funext fun x ↦ sq (f x)
  rw [e, sq]

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
/-- The empirical response in the direction `v` is the empirical mean of `R_v`. -/
theorem sum_mul_empMean_eq (v : ι → ℝ) (n : ℕ) (x : Fin n → X) :
    ∑ i, v i * empMean R n x i = (1 / n) * ∑ k, dirLoss R v (x k) := by
  simp only [empMean, dirLoss, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

omit ht in
/-- **Fluctuation–response**: `Var(v·R̄_n) = (1/n) v ⬝ Cov_a(R,R) v` under `n` independent samples
from `P_{t,a}`. -/
theorem variance_empMean_dir (a v : ι → ℝ) (n : ℕ) :
    variance (fun x : Fin n → X ↦ ∑ i, v i * empMean R n x i)
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a) =
      dotProduct v ((featCov μ π L₀ R t a).mulVec v) / n := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have e : (fun x : Fin n → X ↦ ∑ i, v i * empMean R n x i) =
      fun x ↦ (1 / n) * ∑ k, dirLoss R v (x k) := funext (sum_mul_empMean_eq v n)
  rw [e, variance_const_mul, variance_empSum _ (bdd_dirLoss hR v) n,
    variance_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (bdd_dirLoss hR v) a,
    dotProduct_featCov_mulVec hπm hπi hπ hπpos hL₀m hL₀ hR]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- **Fluctuation–response through the response derivative**:
`Var(v·R̄_n) = −(1/(n t)) v ⬝ Dm_t(a) v`. -/
theorem variance_empMean_dir_eq_meanMapDeriv (a v : ι → ℝ) (n : ℕ) :
    variance (fun x : Fin n → X ↦ ∑ i, v i * empMean R n x i)
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a) =
      -(dotProduct v (meanMapDeriv μ π L₀ R t a v)) / (n * t) := by
  rw [variance_empMean_dir hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a v n]
  have hZ := (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have e : dotProduct v (meanMapDeriv μ π L₀ R t a v) =
      -t * dotProduct v ((featCov μ π L₀ R t a).mulVec v) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) hL₀m hL₀ hR ht hZ v i,
      featCov_mulVec_apply hπm hπi hπ hπpos hL₀m hL₀ hR a v i]
    ring
  rw [e]
  have ht' : t ≠ 0 := ht.ne'
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

end

end Laplace.Multi
