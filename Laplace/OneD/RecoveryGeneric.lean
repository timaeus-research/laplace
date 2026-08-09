/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.RecoveryAllOrder

/-!
# The potential-generic expansion ladder

The all-order expansion for a general even-monomial base with a general
even-monomial perturbation: for `L = x^(2k)/(2k)! + b·x^(2m)`, the
partition function expands with Gamma-form coefficients at the graded
exponents `t^(j - (2mj+1)/(2k))`
(`generic_partition_expansion_allOrder`), which are exactly the germbij
note's correction orders `t^(-(j(m-k)/k + 1/(2k)))` for a degree-`2m`
perturbation of a degree-`2k` minimum. The proof is the quartic ladder's
(exponential split, `expRemainder` bound, term-by-term moments) with the
scale-`t` Gaussian moments replaced by the seabed's Gamma-form monomial
moments `kth_moment_even`. The inequality holds for every `m`; it is an
asymptotic expansion (strictly decreasing orders) exactly when `m > k`.
The quartic ladder is the `k = 1, m = 2` instance (with the double
factorials as the Gamma values, by duplication).
-/

open Real MeasureTheory

namespace Laplace.OneD

/-- rpow bookkeeping: `(A/t)^α = A^α · t^(-α)` for `A ≥ 0 < t`. -/
lemma div_rpow_split {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (α : ℝ) :
    (A / t) ^ α = A ^ α * t ^ (-α) := by
  rw [Real.div_rpow hA ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]

/-- rpow bookkeeping: `t^j · t^(-α) = t^(j - α)`. -/
lemma rpow_nat_sub {t : ℝ} (ht : 0 < t) (j : ℕ) (α : ℝ) :
    t ^ j * t ^ (-α) = t ^ ((j : ℝ) - α) := by
  rw [← Real.rpow_natCast t j, ← Real.rpow_add ht, ← sub_eq_add_neg]

/-- **The potential-generic all-order expansion** (germbij Section 7.4,
graded orders). For `L = x^(2k)/(2k)! + b·x^(2m)` with `b ≥ 0`, the
partition function matches its order-`n` expansion with Gamma-form
coefficients up to the `(n+1)`-st term's size. -/
theorem generic_partition_expansion_allOrder
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t)
    (n : ℕ) :
    |partitionFunction (fun x ↦
        x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) + b * x ^ (2 * m)) t
      - ∑ j ∈ Finset.range (n + 1),
          (-b) ^ j / ((Nat.factorial j : ℝ) * k) *
            (Nat.factorial (2 * k) : ℝ) ^
              ((2 * (m : ℝ) * j + 1) / ((2 * k : ℕ) : ℝ)) *
            Real.Gamma ((2 * (m : ℝ) * j + 1) / ((2 * k : ℕ) : ℝ)) *
            t ^ ((j : ℝ) - (2 * (m : ℝ) * j + 1) / ((2 * k : ℕ) : ℝ))|
    ≤ b ^ (n + 1) / ((Nat.factorial (n + 1) : ℝ) * k) *
        (Nat.factorial (2 * k) : ℝ) ^
          ((2 * (m : ℝ) * ((n + 1 : ℕ) : ℝ) + 1) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((2 * (m : ℝ) * ((n + 1 : ℕ) : ℝ) + 1) /
          ((2 * k : ℕ) : ℝ)) *
        t ^ ((((n + 1) : ℕ) : ℝ) -
          (2 * (m : ℝ) * ((n + 1 : ℕ) : ℝ) + 1) / ((2 * k : ℕ) : ℝ)) := by
  set A : ℕ → ℝ := fun j ↦
    (2 * (m : ℝ) * j + 1) / ((2 * k : ℕ) : ℝ) with hA_def
  set q : ℝ → ℝ := fun x ↦
    Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) with hq_def
  have hq_pos : ∀ x : ℝ, 0 < q x := fun x ↦ Real.exp_pos _
  have hint_pow : ∀ m' : ℕ, Integrable (fun x : ℝ ↦ x ^ m' * q x) :=
    fun m' ↦ kth_integrable_pow hk m' ht
  -- Gamma-form moments with the t-power already split off.
  have hmom : ∀ j : ℕ, (∫ x, x ^ (2 * (m * j)) * q x) =
      (1 / (k : ℝ)) * (Nat.factorial (2 * k) : ℝ) ^ (A j) *
        Real.Gamma (A j) * t ^ (-(A j)) := by
    intro j
    have h := kth_moment_even hk (m * j) ht
    have hBA : ((2 * ((m * j : ℕ) : ℝ) + 1) / ((2 * k : ℕ) : ℝ)) = A j := by
      rw [hA_def]
      push_cast
      ring
    simp only [hq_def]
    rw [h, hBA, div_rpow_split (Nat.cast_nonneg _) ht]
    ring
  -- Pointwise expansion of the perturbation exponential.
  have hsplit : ∀ x : ℝ,
      Real.exp (-(t * (x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) +
        b * x ^ (2 * m)))) =
      (∑ j ∈ Finset.range (n + 1),
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
          (x ^ (2 * (m * j)) * q x)) +
      q x * expRemainder (n + 1) (t * b * x ^ (2 * m)) := by
    intro x
    rw [show -(t * (x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) +
        b * x ^ (2 * m))) =
        -(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) +
        -(t * b * x ^ (2 * m)) by ring, Real.exp_add]
    unfold expRemainder
    simp only [hq_def]
    rw [mul_sub, Finset.mul_sum]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) *
          ((-(t * b * x ^ (2 * m))) ^ j / (Nat.factorial j : ℝ)) =
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
          (x ^ (2 * (m * j)) *
            Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
      intro j _
      rw [show -(t * b * x ^ (2 * m)) = -(t * b) * x ^ (2 * m) by ring,
        mul_pow, ← pow_mul, show 2 * m * j = 2 * (m * j) by ring]
      ring
    rw [Finset.sum_congr rfl hterm]
    ring
  -- Integrability.
  have hint_term : ∀ j : ℕ, Integrable (fun x : ℝ ↦
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
        (x ^ (2 * (m * j)) * q x)) :=
    fun j ↦ (hint_pow (2 * (m * j))).const_mul _
  have hint_sum : Integrable (fun x : ℝ ↦ ∑ j ∈ Finset.range (n + 1),
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
        (x ^ (2 * (m * j)) * q x)) :=
    integrable_finset_sum _ fun j _ ↦ hint_term j
  have hrem_bound : ∀ x : ℝ,
      |q x * expRemainder (n + 1) (t * b * x ^ (2 * m))| ≤
      (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (2 * (m * (n + 1))) * q x) := by
    intro x
    have hs : 0 ≤ t * b * x ^ (2 * m) := by
      have hx : (0 : ℝ) ≤ x ^ (2 * m) := by
        rw [pow_mul]
        positivity
      exact mul_nonneg (mul_nonneg ht.le hb) hx
    have h1 := abs_expRemainder_le (n + 1) hs
    rw [abs_mul, abs_of_pos (hq_pos x)]
    calc q x * |expRemainder (n + 1) (t * b * x ^ (2 * m))|
        ≤ q x * ((t * b * x ^ (2 * m)) ^ (n + 1) /
            (Nat.factorial (n + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (hq_pos x).le
      _ = (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            (x ^ (2 * (m * (n + 1))) * q x) := by
          rw [mul_pow (t * b) (x ^ (2 * m)), mul_pow t b,
            show (x ^ (2 * m)) ^ (n + 1) = x ^ (2 * (m * (n + 1))) by
              rw [← pow_mul, show 2 * m * (n + 1) = 2 * (m * (n + 1))
                by ring]]
          ring
  have hcont_rem : Continuous
      (fun x : ℝ ↦ q x * expRemainder (n + 1) (t * b * x ^ (2 * m))) := by
    have h1 : Continuous fun x : ℝ ↦ t * b * x ^ (2 * m) := by fun_prop
    have h2 := (expRemainder_continuous (n + 1)).comp h1
    have h3 : Continuous q := by
      simp only [hq_def]
      fun_prop
    exact h3.mul h2
  have hint_rem : Integrable
      (fun x ↦ q x * expRemainder (n + 1) (t * b * x ^ (2 * m))) := by
    have hg : Integrable (fun x : ℝ ↦
        (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
          (x ^ (2 * (m * (n + 1))) * q x)) :=
      (hint_pow (2 * (m * (n + 1)))).const_mul _
    apply hg.mono' hcont_rem.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hrem_bound x
  -- Assemble.
  have hZ : partitionFunction (fun x ↦
      x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) + b * x ^ (2 * m)) t =
      (∑ j ∈ Finset.range (n + 1),
        (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
          ∫ x, x ^ (2 * (m * j)) * q x) +
      ∫ x, q x * expRemainder (n + 1) (t * b * x ^ (2 * m)) := by
    unfold partitionFunction
    have hfun : (∫ x : ℝ, Real.exp (-(t * (x ^ (2 * k) /
        (Nat.factorial (2 * k) : ℝ) + b * x ^ (2 * m))))) =
        ∫ x, ((∑ j ∈ Finset.range (n + 1),
          (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
            (x ^ (2 * (m * j)) * q x)) +
          q x * expRemainder (n + 1) (t * b * x ^ (2 * m))) := by
      congr 1
      funext x
      exact hsplit x
    rw [hfun, MeasureTheory.integral_add hint_sum hint_rem,
      MeasureTheory.integral_finset_sum _ fun j _ ↦ hint_term j]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦
      MeasureTheory.integral_const_mul _ _
  -- Term-by-term evaluation.
  have hcoeff : ∀ j ∈ Finset.range (n + 1),
      (-(t * b)) ^ j / (Nat.factorial j : ℝ) *
        ∫ x, x ^ (2 * (m * j)) * q x =
      (-b) ^ j / ((Nat.factorial j : ℝ) * k) *
        (Nat.factorial (2 * k) : ℝ) ^ (A j) * Real.Gamma (A j) *
        t ^ ((j : ℝ) - A j) := by
    intro j _
    rw [hmom j, show (-(t * b)) = t * (-b) by ring, mul_pow,
      ← rpow_nat_sub ht j (A j)]
    have hk0 : ((k : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      exact this.ne'
    field_simp
  -- The expansion error is the remainder integral.
  have hE : partitionFunction (fun x ↦
      x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) + b * x ^ (2 * m)) t
      - (∑ j ∈ Finset.range (n + 1),
          (-b) ^ j / ((Nat.factorial j : ℝ) * k) *
            (Nat.factorial (2 * k) : ℝ) ^ (A j) * Real.Gamma (A j) *
            t ^ ((j : ℝ) - A j)) =
      ∫ x, q x * expRemainder (n + 1) (t * b * x ^ (2 * m)) := by
    rw [hZ, Finset.sum_congr rfl hcoeff]
    ring
  rw [hE]
  -- Bound the remainder integral by the (n+1)-st moment.
  have hg : Integrable (fun x : ℝ ↦
      (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (2 * (m * (n + 1))) * q x)) :=
    (hint_pow (2 * (m * (n + 1)))).const_mul _
  have h1 : |∫ x, q x * expRemainder (n + 1) (t * b * x ^ (2 * m))| ≤
      ∫ x, (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
        (x ^ (2 * (m * (n + 1))) * q x) := by
    calc |∫ x, q x * expRemainder (n + 1) (t * b * x ^ (2 * m))|
        ≤ ∫ x, |q x * expRemainder (n + 1) (t * b * x ^ (2 * m))| := by
          have := MeasureTheory.norm_integral_le_integral_norm
            (f := fun x ↦ q x *
              expRemainder (n + 1) (t * b * x ^ (2 * m)))
            (μ := volume)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ x, (t * b) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) *
            (x ^ (2 * (m * (n + 1))) * q x) :=
          MeasureTheory.integral_mono hint_rem.abs hg fun x ↦
            hrem_bound x
  refine h1.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, hmom (n + 1), mul_pow t b,
    ← rpow_nat_sub ht (n + 1) (A (n + 1))]
  have hk0 : ((k : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact this.ne'
  field_simp
  ring

end Laplace.OneD
