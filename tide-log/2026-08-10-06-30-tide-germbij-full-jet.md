# Tide: germbij-full-jet (stage C6)

**Direction (user):** the full-jet packaging (auto mode, standing
delegation): extract iterated-derivative equality from
smooth_jet_recovery's coefficient conclusion, and quantify over all
finite orders for smooth (ContDiff ⊤) losses — the note's Theorem 3.1
statement shape ("every partial derivative of positive order") in 1D.

**Seabed:** laplace, main at c3ebfa1 (smooth-germ complete).
**Worktree/branch:** laplace-tide-germbij-full-jet /
tide/germbij-full-jet
**Started:** 2026-08-10T06:30Z

## Deliberation

C6 was scoped in the smooth-germ consult ("full Taylor-jet
packaging: quantify over arbitrary finite R and package the
compatible family of finite-order conclusions") and deliberately
excluded from the C5 tide. Seabed survey shows it is pure
composition: taylorBase = iD2/2 and taylorCoeff i = iD(3+i)/(3+i)!
convert coefficient equality to iteratedDeriv equality (factorials
nonzero); the all-orders corollary instantiates the finite theorem at
R := k−2 per k, with ContDiff ⊤ restricting to each finite order.
Documented prior-deliberation path; no new closed form (definitional
conversions only), so no numerical check is feasible or needed —
noted per protocol.

## Vote

- Claude: one small tide (two corollaries).
- GPT-5.6 Sol (scoping consult): C6 as its own stage.

Agreed (carried over).

## Result

- Theorems (Laplace/OneD/FullJetRecovery.lean, ~90 lines, zero
  sorries, zero warnings; gate verified via import + .olean):
  smooth_jet_recovery_iteratedDeriv (coefficient equality converted
  to iterated-derivative equality for 2 ≤ k ≤ R+2, via
  taylorBase = iD₂/2 and taylorCoeff i = iD_{3+i}/(3+i)! with
  factorials cleared) and smooth_full_jet_recovery (C6: for smooth
  losses with data at every rate, every derivative of order ≥ 2
  agrees — instantiating the finite theorem at R := k−2 per k).
- Surprises: the C^∞ grade bookkeeping — ContDiff's exponent is now
  WithTop ℕ∞ where the coercion of (⊤ : ℕ∞) is the C^∞ grade (NOT ⊤,
  which is the analytic grade ω); exact_mod_cast cannot bridge
  ↑n ≤ ↑⊤, and the ∞ notation is scoped. The working idiom is
  contDiff_infty.mp (giving ∀ n, ContDiff ℝ n f) with the hypothesis
  stated as ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞).
