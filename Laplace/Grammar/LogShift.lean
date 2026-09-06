/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogInsertions

/-!
# The log-shift operator (grammar §4 `lem:log_shift`)

Combining the binomial theorem with the order-derivative identity `∂_ν^m S_ν = ∫ (log t)^m …` gives the
paper's log-shift operator identity

  `∫₀^∞ t^{ν-1} (c - log t)^p e^{-βt+βa√t} dt = ∑_{m=0}^p binom(p,m) c^{p-m} (-1)^m ∂_ν^m S_ν(a)`,

i.e. `(c - ∂_ν)^p S_ν` written out. This packages log insertions of a shifted logarithm as a
differential operator in the order.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- **Log-shift operator** (grammar §4 `lem:log_shift`):
`∫ t^{ν-1}(c-log t)^p e^{-βt+βa√t} = ∑_{m≤p} binom(p,m) c^{p-m} (-1)^m ∂_ν^m S_ν(a)`,
the expansion of `(c-∂_ν)^p S_ν`. -/
theorem fluctuation_log_shift (β a c ν : ℝ) (p : ℕ) (hβ : 0 < β) (hν : 0 < ν) :
    (∫ t in Set.Ioi 0, t ^ (ν - 1) * (c - Real.log t) ^ p
        * Real.exp (-β * t + β * a * Real.sqrt t))
      = ∑ m ∈ Finset.range (p + 1), (p.choose m : ℝ) * c ^ (p - m) * (-1) ^ m
          * iteratedDeriv m (fun l => fluctuation β l a) ν := by
  have hint : ∀ m : ℕ, Integrable (fun t => (p.choose m : ℝ) * c ^ (p - m) * (-1) ^ m
      * ((Real.log t) ^ m * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t)))
      (volume.restrict (Set.Ioi 0)) := by
    intro m
    apply Integrable.const_mul
    refine (log_pow_fluctuation_integrableOn β ν a m hβ hν).mono' ?_ ?_
    · exact (by fun_prop : Measurable (fun t => (Real.log t) ^ m * t ^ (ν - 1)
        * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_pos (Real.rpow_pos_of_pos ht _), abs_of_pos (Real.exp_pos _)]
  have hstep : (∫ t in Set.Ioi 0, t ^ (ν - 1) * (c - Real.log t) ^ p
        * Real.exp (-β * t + β * a * Real.sqrt t))
      = ∫ t in Set.Ioi 0, ∑ m ∈ Finset.range (p + 1), (p.choose m : ℝ) * c ^ (p - m) * (-1) ^ m
          * ((Real.log t) ^ m * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    beta_reduce
    rw [show c - Real.log t = -Real.log t + c by ring, add_pow, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [neg_pow]; ring
  rw [hstep, integral_finsetSum _ (fun m _ => hint m)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul, ← iteratedDeriv_fluctuation_order β a hβ m ν hν]

end Laplace.Grammar
