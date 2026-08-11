/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.MonomialPotential

/-!
# Variance of monomial observables against the even-monomial Gibbs weight

Stage 1 of the weighted-jet recovery programme (germbij note §7.4):
the variance `Var(xⁿ) = ⟨x²ⁿ⟩ - ⟨xⁿ⟩²` against the reference weight
`exp(-t·x^(2k)/(2k)!)` in Gamma closed form
(`monomial_variance_odd`, `monomial_variance_even`) and — the
injectivity input for every coefficient-recovery rung — strictly
positive for `n ≥ 1` (`monomial_variance_pos`). The positivity proof
is the note's own argument: `Var[Q] = 0` would force `Q` constant
against a measure of full support, realized here as positivity of the
centered integral `∫ (xⁿ - M)²·exp(-t·L_k)` via the open nonempty
support of its continuous nonnegative integrand.
-/

open Real MeasureTheory

namespace Laplace.OneD

open Laplace

/-- Variance of an odd monomial against the pure even-monomial Gibbs
weight: the mean vanishes by symmetry, so the variance is the even
moment `⟨x^(2(2m+1))⟩` in Gamma form. -/
theorem monomial_variance_odd
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsCov (kthPotential k) t
        (fun x ↦ x ^ (2 * m + 1)) (fun x ↦ x ^ (2 * m + 1)) =
      ((Nat.factorial (2 * k) : ℝ) / t) ^
          (((2 * m + 1 : ℕ) : ℝ) / (k : ℝ)) *
        Real.Gamma ((2 * (2 * m + 1) + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  unfold gibbsCov
  have hsq : (fun x : ℝ ↦ x ^ (2 * m + 1) * x ^ (2 * m + 1)) =
      fun x : ℝ ↦ x ^ (2 * (2 * m + 1)) := by
    ext x
    rw [← pow_add]
    congr 1
    ring
  rw [hsq, gibbsExpectation_kthPotential_even hk (2 * m + 1) ht,
    gibbsExpectation_kthPotential_odd k m t]
  push_cast
  ring

/-- Variance of an even monomial against the pure even-monomial Gibbs
weight, as a difference of Gamma ratios scaled by the common power of
`(2k)!/t`. -/
theorem monomial_variance_even
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsCov (kthPotential k) t
        (fun x ↦ x ^ (2 * m)) (fun x ↦ x ^ (2 * m)) =
      ((Nat.factorial (2 * k) : ℝ) / t) ^ ((2 * (m : ℝ)) / (k : ℝ)) *
        (Real.Gamma ((2 * (2 * m) + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) -
          (Real.Gamma ((2 * m + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) ^ 2) := by
  unfold gibbsCov
  have hsq : (fun x : ℝ ↦ x ^ (2 * m) * x ^ (2 * m)) =
      fun x : ℝ ↦ x ^ (2 * (2 * m)) := by
    ext x
    rw [← pow_add]
    congr 1
    ring
  rw [hsq, gibbsExpectation_kthPotential_even hk (2 * m) ht,
    gibbsExpectation_kthPotential_even hk m ht]
  have hfac_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t :=
    div_pos (by exact_mod_cast Nat.factorial_pos _) ht
  have hpow : ((Nat.factorial (2 * k) : ℝ) / t) ^
        ((2 * (m : ℝ)) / (k : ℝ)) =
      (((Nat.factorial (2 * k) : ℝ) / t) ^ ((m : ℝ) / (k : ℝ))) ^ 2 := by
    rw [sq, ← Real.rpow_add hfac_t_pos]
    congr 1
    ring
  have hcast : (((2 * m : ℕ) : ℝ) / (k : ℝ)) = (2 * (m : ℝ)) / (k : ℝ) := by
    push_cast
    ring
  rw [hcast, hpow]
  push_cast
  ring

/-- **Strict positivity of the monomial variance** — the injectivity
input for the weighted-jet recovery rungs. For `k ≥ 1`, `n ≥ 1`,
`t > 0`, the variance of `xⁿ` against `exp(-t·x^(2k)/(2k)!)` is
strictly positive: the centered integrand `(xⁿ - M)²·weight` is
continuous, nonnegative, and not identically zero, so its integral is
positive and dividing by `Z > 0` keeps it so. -/
theorem monomial_variance_pos
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 < gibbsCov (kthPotential k) t
        (fun x ↦ x ^ n) (fun x ↦ x ^ n) := by
  set M : ℝ := gibbsExpectation (kthPotential k) t (fun x ↦ x ^ n)
    with hM_def
  have hZ : 0 < partitionFunction (kthPotential k) t :=
    partitionFunction_kthPotential_pos hk ht
  -- Integrability of the three moment integrands.
  have h0 : Integrable
      (fun x : ℝ ↦ Real.exp (-(t * kthPotential k x))) := by
    have h := kth_integrable_pow_pot hk 0 ht
    exact h.congr (Filter.Eventually.of_forall fun x ↦ by
      simp)
  have h1 : Integrable
      (fun x : ℝ ↦ x ^ n * Real.exp (-(t * kthPotential k x))) :=
    kth_integrable_pow_pot hk n ht
  have h2 : Integrable
      (fun x : ℝ ↦ x ^ (2 * n) * Real.exp (-(t * kthPotential k x))) :=
    kth_integrable_pow_pot hk (2 * n) ht
  -- The centered integrand and its integrability.
  have hcent : Integrable (fun x : ℝ ↦
      (x ^ n - M) ^ 2 * Real.exp (-(t * kthPotential k x))) := by
    have hsum : Integrable (fun x : ℝ ↦
        x ^ (2 * n) * Real.exp (-(t * kthPotential k x)) -
          (2 * M) * (x ^ n * Real.exp (-(t * kthPotential k x))) +
          M ^ 2 * Real.exp (-(t * kthPotential k x))) :=
      (h2.sub (h1.const_mul (2 * M))).add (h0.const_mul (M ^ 2))
    exact hsum.congr (Filter.Eventually.of_forall fun x ↦ by
      ring)
  -- Positivity of the centered integral.
  have hpos : 0 < ∫ x : ℝ,
      (x ^ n - M) ^ 2 * Real.exp (-(t * kthPotential k x)) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x ↦ by positivity) hcent]
    have hcont : Continuous (fun x : ℝ ↦
        (x ^ n - M) ^ 2 * Real.exp (-(t * kthPotential k x))) := by
      have hLk : Continuous (kthPotential k) := by
        unfold kthPotential
        fun_prop
      fun_prop
    have hopen : IsOpen (Function.support (fun x : ℝ ↦
        (x ^ n - M) ^ 2 * Real.exp (-(t * kthPotential k x)))) := by
      rw [Function.support_eq_preimage]
      exact isOpen_compl_singleton.preimage hcont
    refine hopen.measure_pos volume ?_
    rcases eq_or_ne M 0 with hM0 | hM0
    · refine ⟨1, ?_⟩
      simp only [Function.mem_support, hM0, sub_zero, one_pow]
      exact mul_ne_zero one_ne_zero (Real.exp_ne_zero _)
    · refine ⟨0, ?_⟩
      simp only [Function.mem_support]
      rw [zero_pow (by omega : n ≠ 0), zero_sub]
      exact mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr hM0))
        (Real.exp_ne_zero _)
  -- The variance identity: gibbsCov = (centered integral) / Z.
  have hMZ : (∫ x : ℝ, x ^ n * Real.exp (-(t * kthPotential k x))) =
      M * partitionFunction (kthPotential k) t := by
    rw [hM_def]
    unfold gibbsExpectation
    field_simp
  have hid : gibbsCov (kthPotential k) t
        (fun x ↦ x ^ n) (fun x ↦ x ^ n) =
      (∫ x : ℝ, (x ^ n - M) ^ 2 *
        Real.exp (-(t * kthPotential k x))) /
        partitionFunction (kthPotential k) t := by
    have hexpand : (∫ x : ℝ, (x ^ n - M) ^ 2 *
        Real.exp (-(t * kthPotential k x))) =
        (∫ x : ℝ, x ^ (2 * n) * Real.exp (-(t * kthPotential k x))) -
          (2 * M) * (∫ x : ℝ, x ^ n *
            Real.exp (-(t * kthPotential k x))) +
          M ^ 2 * partitionFunction (kthPotential k) t := by
      have hsub : Integrable (fun x : ℝ ↦
          x ^ (2 * n) * Real.exp (-(t * kthPotential k x)) -
            (2 * M) * (x ^ n * Real.exp (-(t * kthPotential k x)))) :=
        h2.sub (h1.const_mul (2 * M))
      calc ∫ x : ℝ, (x ^ n - M) ^ 2 *
            Real.exp (-(t * kthPotential k x))
          = ∫ x : ℝ, (x ^ (2 * n) *
              Real.exp (-(t * kthPotential k x)) -
              (2 * M) * (x ^ n * Real.exp (-(t * kthPotential k x)))) +
              M ^ 2 * Real.exp (-(t * kthPotential k x)) := by
            congr 1
            ext x
            ring
        _ = (∫ x : ℝ, x ^ (2 * n) *
              Real.exp (-(t * kthPotential k x)) -
              (2 * M) * (x ^ n *
                Real.exp (-(t * kthPotential k x)))) +
            ∫ x : ℝ, M ^ 2 * Real.exp (-(t * kthPotential k x)) := by
            rw [integral_add hsub (h0.const_mul (M ^ 2))]
        _ = (∫ x : ℝ, x ^ (2 * n) *
              Real.exp (-(t * kthPotential k x))) -
            (2 * M) * (∫ x : ℝ, x ^ n *
              Real.exp (-(t * kthPotential k x))) +
            M ^ 2 * partitionFunction (kthPotential k) t := by
            rw [integral_sub h2 (h1.const_mul (2 * M)),
              integral_const_mul, integral_const_mul]
            rfl
    unfold gibbsCov gibbsExpectation
    rw [hexpand, hMZ]
    have hsq : (fun x : ℝ ↦ x ^ n * x ^ n) =
        fun x : ℝ ↦ x ^ (2 * n) := by
      ext x
      rw [← pow_add]
      congr 1
      ring
    rw [hsq]
    field_simp
    ring
  rw [hid]
  exact div_pos hpos hZ

end Laplace.OneD
