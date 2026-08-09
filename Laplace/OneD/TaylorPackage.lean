/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.StableRecovery

/-!
# The stabilizer envelope

Stage C2 of the smooth-germ programme, first installment. The
degree-`D` Taylor polynomial of a smooth loss need not be confining
(its top coefficient can be negative), so the comparison argument
stabilizes it with an even monomial `d·x^M`, `M > D`: in scaled
coordinates the stabilizer first appears at rung `M - 2 > R`, so it
is invisible to every recovered coefficient. The consult's
coefficient-wise construction (`exists_stabilizer_envelope`) produces
`d` by an elementary case split at `|x| = ρ`,
`ρ = min(1, a/(2(B+1)))`, `B = ∑|c_i|`, yielding the global envelope
`(a/2)·x² ≤ a·x² + ∑ c_i·x^(3+i) + d·x^M` with no suprema or
compactness arguments.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- **The stabilizer envelope** (stage C2.2 core). For `a > 0`,
higher coefficients `c` at degrees `3, …, R'+2`, and an even `M`
above every degree present, there is `d ≥ 0` such that the stabilized
polynomial dominates `(a/2)·x²` globally. -/
theorem exists_stabilizer_envelope
    {R' : ℕ} {a : ℝ} (ha : 0 < a) (c : Fin R' → ℝ) {M : ℕ}
    (hM_even : Even M) (hM : R' + 2 < M) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ x : ℝ,
      a / 2 * x ^ 2 ≤
        a * x ^ 2 + (∑ i : Fin R', c i * x ^ (2 + (i.1 + 1))) +
          d * x ^ M := by
  set B : ℝ := ∑ i : Fin R', |c i| with hB_def
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  set ρ : ℝ := min 1 (a / (2 * (B + 1))) with hρ_def
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hBρ : B * ρ ≤ a / 2 := by
    have h1 : ρ ≤ a / (2 * (B + 1)) := min_le_right _ _
    have h2 : B * ρ ≤ B * (a / (2 * (B + 1))) :=
      mul_le_mul_of_nonneg_left h1 hB0
    have h3 : B * (a / (2 * (B + 1))) ≤ a / 2 := by
      rw [← mul_div_assoc,
        div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  refine ⟨(∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M,
    by positivity, fun x ↦ ?_⟩
  have hxM : (0 : ℝ) ≤ x ^ M := hM_even.pow_nonneg x
  have habsM : |x| ^ M = x ^ M := hM_even.pow_abs x
  -- The sum is bounded below by minus its absolute row.
  have hsum_lb : -(∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
      ∑ i : Fin R', c i * x ^ (2 + (i.1 + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h1 : |c i * x ^ (2 + (i.1 + 1))| =
        |c i| * |x| ^ (2 + (i.1 + 1)) := by
      rw [abs_mul, abs_pow]
    calc -(|c i| * |x| ^ (2 + (i.1 + 1))) = -|c i * x ^ (2 + (i.1 + 1))| := by
          rw [h1]
      _ ≤ c i * x ^ (2 + (i.1 + 1)) := neg_abs_le _
  rcases le_total |x| ρ with hx | hx
  · -- Inner region: each degree ≥ 3 term is ≤ B·ρ·x² ≤ (a/2)·x².
    have hx1 : |x| ≤ 1 := le_trans hx hρ1
    have hterm : ∀ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)) ≤
        |c i| * (|x| * x ^ 2) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h3 : |x| ^ (2 + (i.1 + 1)) ≤ |x| ^ 3 :=
        pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
      calc |x| ^ (2 + (i.1 + 1)) ≤ |x| ^ 3 := h3
        _ = |x| * x ^ 2 := by
            rw [pow_succ, sq_abs]
            ring
    have hsum_ub : (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
        B * ρ * x ^ 2 := by
      calc (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)))
          ≤ ∑ i : Fin R', |c i| * (|x| * x ^ 2) :=
            Finset.sum_le_sum fun i _ ↦ hterm i
        _ = B * (|x| * x ^ 2) := by
            rw [hB_def, Finset.sum_mul]
        _ ≤ B * (ρ * x ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            apply mul_le_mul_of_nonneg_right hx (sq_nonneg x)
        _ = B * ρ * x ^ 2 := by ring
    have hd : (0 : ℝ) ≤ (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) /
        ρ ^ M * x ^ M := by
      apply mul_nonneg _ hxM
      positivity
    have hBρx : B * ρ * x ^ 2 ≤ a / 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right hBρ (sq_nonneg x)
    nlinarith [hsum_lb, hsum_ub]
  · -- Outer region: each term is absorbed by the stabilizer.
    have hterm : ∀ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)) ≤
        |c i| * ρ ^ (2 + (i.1 + 1)) / ρ ^ M * x ^ M := by
      intro i
      have hj : 2 + (i.1 + 1) ≤ M := by omega
      have hkey : |x| ^ (2 + (i.1 + 1)) * ρ ^ M ≤
          ρ ^ (2 + (i.1 + 1)) * |x| ^ M := by
        have h1 : ρ ^ M = ρ ^ (2 + (i.1 + 1)) *
            ρ ^ (M - (2 + (i.1 + 1))) := by
          rw [← pow_add]
          congr 1
          omega
        have h2 : |x| ^ M = |x| ^ (2 + (i.1 + 1)) *
            |x| ^ (M - (2 + (i.1 + 1))) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h1, h2]
        have h3 : ρ ^ (M - (2 + (i.1 + 1))) ≤
            |x| ^ (M - (2 + (i.1 + 1))) :=
          pow_le_pow_left₀ hρ0.le hx _
        calc |x| ^ (2 + (i.1 + 1)) *
              (ρ ^ (2 + (i.1 + 1)) * ρ ^ (M - (2 + (i.1 + 1))))
            ≤ |x| ^ (2 + (i.1 + 1)) *
              (ρ ^ (2 + (i.1 + 1)) * |x| ^ (M - (2 + (i.1 + 1)))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ρ ^ (2 + (i.1 + 1)) *
              (|x| ^ (2 + (i.1 + 1)) * |x| ^ (M - (2 + (i.1 + 1)))) := by
              ring
      have hρM : (0 : ℝ) < ρ ^ M := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hρM]
      calc |c i| * |x| ^ (2 + (i.1 + 1)) * ρ ^ M
          = |c i| * (|x| ^ (2 + (i.1 + 1)) * ρ ^ M) := by ring
        _ ≤ |c i| * (ρ ^ (2 + (i.1 + 1)) * |x| ^ M) :=
            mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
        _ = |c i| * ρ ^ (2 + (i.1 + 1)) * |x| ^ M := by ring
        _ = |c i| * ρ ^ (2 + (i.1 + 1)) * x ^ M := by
            rw [habsM]
    have habsorb : (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1))) ≤
        (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M * x ^ M := by
      calc (∑ i : Fin R', |c i| * |x| ^ (2 + (i.1 + 1)))
          ≤ ∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1)) / ρ ^ M * x ^ M :=
            Finset.sum_le_sum fun i _ ↦ hterm i
        _ = (∑ i : Fin R', |c i| * ρ ^ (2 + (i.1 + 1))) / ρ ^ M *
            x ^ M := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
    nlinarith [hsum_lb, habsorb, sq_nonneg x, ha]

end Laplace.OneD
