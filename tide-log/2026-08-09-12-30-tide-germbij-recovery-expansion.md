# Tide: germbij-recovery-expansion

**Direction (user):** continue the germbij recovery thread (auto mode):
the first expansion-based subleading recovery, implementing the note's
Section 7.4 pairing mechanism in its smallest instance: the first
correction of the quartic-perturbed Gaussian partition function with an
explicit error bound, and recovery of b from the expansion.

**Seabed:** laplace, main at af0809c (recovery thread: exact, asymptotic,
and monotonicity recovery all merged; scale-t Gaussian moments
integral_pow_mul_exp_neg_t_sq_half available).
**Worktree/branch:** laplace-tide-germbij-recovery-expansion /
tide/germbij-recovery-expansion
**Started:** 2026-08-09T12:30Z

## Candidates v1 (Claude)

**A (elementary Taylor bound):** for s ≥ 0,
0 ≤ e^{-s} - 1 + s ≤ s² (and the |·| corollary). Via
Real.add_one_le_exp twice (no inverses, no calculus).

**B (first correction with explicit error):** for b ≥ 0, t > 0, with
E(b,t) := Z_b(t) - √(2π) t^{-1/2} + 3b√(2π) t^{-3/2},
0 ≤ E(b,t) ≤ 105 b² √(2π) t^{-5/2},
where Z_b(t) = partitionFunction (x²/2 + b x⁴) t. Key structure: after
splitting e^{-t(x²/2+bx⁴)} = q·e^{-tbx⁴} (q the Gaussian factor) and
expanding e^{-tbx⁴} = 1 - tbx⁴ + r with 0 ≤ r ≤ (tbx⁴)², the k = 0 and
k = 2 moments cancel the main and correction terms EXACTLY, so
E(b,t) = ∫ q·r, bounded two-sidedly by the k = 4 moment
(7‼ = 105).

**C (expansion-based recovery):** b₁, b₂ ≥ 0 and Z_{b₁} =ᶠ[atTop] Z_{b₂}
force b₁ = b₂: the difference of the two E's is exactly
3(b₁-b₂)√(2π)t^{-3/2}, bounded by 105(b₁²+b₂²)√(2π)t^{-5/2}, and an
archimedean choice of t gives the contradiction. This is the note's
"corrections at distinct orders recover each a_j" pairing at the first
order, complementing the monotonicity mechanism of the previous tide.

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_expansion_v1.md`.
Summary: no Mathlib lemma subsumes A for unbounded s ≥ 0 (the local
abs_exp_sub_one_sub_id_le is range-restricted); supplied a
multiplication-only proof of A (avoid inverse-order lemmas); recommended
two-sided bounds as the internal statement with the |·| corollary
exposed; normalize the exponent once in a pointwise helper rather than
fighting simp under exp; isolate the rpow product identities as helpers;
for the |∫f| ≤ ∫g chain use norm_integral_le_integral_norm +
integral_mono_ae with Integrable.mono'; EventuallyEq preferred for C's
hypothesis (with an optional explicit-T wrapper); archimedean finish
without limits confirmed; noted the monotonicity shortcut is already
merged and that A+B+C is the right development for the expansion
mechanism specifically.

## Vote

- Claude: A + B + C in Laplace/OneD/RecoveryExpansion.lean.
- GPT-5.6 Sol: A + B + C in that file, ordered bounds-first. Agreed.

## Numerical check

Run before the consult (scipy quad, b = 0.3):
(Z_b(t) - √(2π/t))·t^{3/2} at t = 10, 100, 1000, 10000:
-1.599, -2.148, -2.244, -2.255 → target -3b√(2π) = -2.256. Error bound:
err·t^{5/2} at t = 10, 100, 1000: 6.57, 10.82, 11.73 vs
C = 105 b² √(2π)/2... wait: with the s² (not s²/2) constant,
C = 105 b² √(2π) = 23.69; the observed sharp constant is ≈ 11.84
(= 105 b² √(2π)/2, the s²/2 constant), consistent: our proved constant
is double the sharp one, as expected from the elementary bound.

## Result

- Branch tide/germbij-recovery-expansion,
  Laplace/OneD/RecoveryExpansion.lean: exp_neg_sub_one_add_bounds,
  quartic_partition_expansion_bounds,
  quartic_coefficient_recovery_of_eventuallyEq.
- Four build iterations. Fixes: kth_integrable_pow needed its import
  (MonomialPotential); the integral_add/sub Pi.add gotcha hit again and
  was fixed by the documented type-ascribed single-lambda witnesses; the
  moment closed-form steps were made robust by normalizing both
  hypothesis and goal with norm_num [Nat.doubleFactorial] and finishing
  with linarith (the integral as an atom); a calc proving an equality
  needed le_of_eq against the ≤ goal.
- Surprise: the k = 0 and k = 2 moments cancel the main and correction
  terms EXACTLY, so the expansion error is literally the integrated
  remainder ∫ q·r — no approximate bookkeeping anywhere. The archimedean
  recovery finish worked as deliberated.
