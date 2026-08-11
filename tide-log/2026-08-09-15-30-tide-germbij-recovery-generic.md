# Tide: germbij-recovery-generic

**Direction (user):** continue the germbij recovery thread (auto mode):
the potential-generic expansion ladder, the thread's last recorded
follow-up. All-order expansion of Z for kthPotential k + b x^(2m) with
Gamma-form coefficients and the note's graded exponents j - (2mj+1)/(2k).

**Seabed:** laplace, main at b715fc5 (quartic ladder complete:
RecoveryExpansion, RecoveryAllOrder, RecoveryCoeffLimit; generic moments
kth_moment_even; expRemainder bound abs_expRemainder_le).
**Worktree/branch:** laplace-tide-germbij-recovery-generic /
tide/germbij-recovery-generic
**Started:** 2026-08-09T15:30Z

## Candidate v1 (Claude)

Single theorem generic_partition_expansion_allOrder: for 1 ≤ k, m : ℕ,
b ≥ 0, t > 0, n, with α_j = (2mj+1)/(2k):
|Z_{k,m,b}(t) - Σ_{j≤n} (-b)^j/(j!·k) ((2k)!)^{α_j} Γ(α_j) t^{j-α_j}|
≤ b^{n+1}/((n+1)!·k) ((2k)!)^{α_{n+1}} Γ(α_{n+1}) t^{(n+1)-α_{n+1}}.
Mirror of the quartic all-order proof with q := exp(-t·kthPotential k),
moment index 2mj (kth_moment_even), and the div_rpow split
((2k)!/t)^α = ((2k)!)^α t^{-α}. The exponents j - α_j are exactly the
note's graded orders -(j(m-k)/k + 1/(2k)) (asymptotic expansion when
m > k; the inequality itself needs no relation between m and k).
Specializes at k = 1, m = 2 to the quartic ladder (Gamma duplication
gives the double factorials; not proven in Lean, coexists).

## Numerical check

Run before the consult (scipy quad, k = 2, m = 3, b = 0.05, n = 1):
t = 50: |Z-main| = 1.47e-01 vs bound 3.67e-01; t = 200: 3.62e-02 vs
6.48e-02; t = 1000: 6.32e-03 vs 8.67e-03. Bound holds, slack shrinking,
consistent with the alternating remainder.

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_generic_v1.md`.
Summary: statement and derivation sound including m = 0; main hazard is
accidental Nat division in the exponents (avoided: all alphas written
with real casts); confirmed the rpow helper spelling, Real.div_rpow, and
the single-theorem file shape; suggested an optional named abbreviation
genericRecoveryAlpha for readability (not adopted: the raw form keeps
the statement self-contained and matches the note; recorded as a
possible later refactor).

## Vote

- Claude: single theorem + two rpow helpers, Laplace/OneD/RecoveryGeneric.lean.
- GPT-5.6 Sol: same shape (with the optional abbreviation). Agreed.

## Result

- Branch tide/germbij-recovery-generic,
  Laplace/OneD/RecoveryGeneric.lean: div_rpow_split, rpow_nat_sub,
  generic_partition_expansion_allOrder.
- Three build iterations. Fixes: positivity cannot see x^(2m) ≥ 0 for
  symbolic m (bridge via pow_mul to (x²)^m); mul_pow needs explicit
  arguments when the product is not the outermost head; and the
  statement's (n+1) casts inside the alpha expressions had to be written
  ↑(n+1) rather than ↑n + 1 for `set` to abstract them (the cast-shape
  sibling of the Pi-form gotchas). One garbage edit line caught before
  build.
- Surprise: the mirror held; the Gamma-form bookkeeping needed no
  mathematical adjustment from the deliberated form, matching the
  numerical check.
