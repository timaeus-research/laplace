# Tide: germbij-recovery-coefflimit

**Direction (user):** continue the germbij recovery thread (auto mode):
the coefficient-limit packaging deferred from the all-order tide. Each
coefficient of the quartic expansion is the limit of the rescaled
remainder, the note's "the expansion determines each coefficient" in
Tendsto form.

**Seabed:** laplace, chained on tide/germbij-recovery-allorder (bc09d3e,
PR #39 in flight); consumes quartic_partition_expansion_allOrder.
**Worktree/branch:** laplace-tide-germbij-recovery-coefflimit /
tide/germbij-recovery-coefflimit
**Started:** 2026-08-09T14:40Z

## Deliberation (inherited)

This is candidate C of the all-order tide's deliberation
(tide-log/gpt56_germbij_recovery_allorder_v1.md, section "C:
mathematically worthwhile, but defer it"): both parties agreed on the
statement (the rescaled remainder tends to the next coefficient) and the
route (apply the expansion at order n+1, split off the last term of the
sum, show the rest is O(t^{-1}) after rescaling, squeeze), deferring
only until the expansion API stabilized. It has (PR #39). No fresh
consult round.

## Candidate (agreed)

```
theorem quartic_expansion_coefficient_limit {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    Tendsto (fun t : ℝ ↦
      (Z_b(t) - √(2π) ∑_{j ≤ n} c_j t^{-(j+1/2)}) * t^((n+1)+1/2))
      atTop (nhds (√(2π) c_{n+1}))
```
with c_j = (-b)^j (4j-1)‼/j!.

## Numerical check

The n = 1 instance was checked in the first-correction tide
((Z - √(2π/t))t^{3/2} -> -3b√(2π), scipy, archived); the general shape
follows the same verified expansion. Not re-scripted.

## Result

- Branch tide/germbij-recovery-coefflimit,
  Laplace/OneD/RecoveryCoeffLimit.lean:
  quartic_expansion_coefficient_limit.
- Two build iterations (a simp couldn't close the rpow exponent
  cancellation; replaced by an explicit show-ring-rpow_zero chain).
- Surprise: none; the inherited deliberation's route (split the last
  term, squeeze the rescaled next-order remainder below C/t) compiled
  essentially as sketched.
