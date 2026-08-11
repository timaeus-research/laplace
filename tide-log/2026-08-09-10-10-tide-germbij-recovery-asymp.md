# Tide: germbij-recovery-asymp

**Direction (user):** continue the germbij recovery thread (auto mode):
the asymptotic strengthening of dimension-one recovery. The note's
hypothesis is agreement of asymptotic expansions, not exact equality, so
upgrade eventual_power_eq and kth_partitionFunction_recovery to
IsEquivalent hypotheses.

**Seabed:** laplace, main after tide/germbij-recovery-1d (PR #35):
eventual_power_eq, partitionFunction_smul, kth_partitionFunction_recovery,
plus the closed form partitionFunction_kthPotential.
**Started:** 2026-08-09T10:10Z
**Worktree/branch:** laplace-tide-germbij-recovery-asymp /
tide/germbij-recovery-asymp

## Candidates v1 (Claude)

**Candidate A (uniqueness of power-law asymptotes).**
```
theorem power_asymptote_unique {α₁ α₂ β₁ β₂ : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (h : (fun t : ℝ ↦ α₁ * t ^ β₁) ~[atTop] fun t : ℝ ↦ α₂ * t ^ β₂) :
    β₁ = β₂ ∧ α₁ = α₂
```
Proof: isEquivalent_iff_tendsto_one (denominator eventually nonzero for
t > 0); the ratio is eventually (α₁/α₂) t^(β₁-β₂); trichotomy on
β₁ - β₂: positive gives Tendsto atTop (const_mul_atTop +
tendsto_rpow_atTop), contradicting the nhds-1 limit
(not_tendsto_nhds_of_tendsto_atTop); negative gives limit 0
(tendsto_rpow_neg_atTop), contradicting 1 = 0 by tendsto_nhds_unique;
zero collapses the ratio to the constant α₁/α₂, and tendsto_nhds_unique
gives α₁/α₂ = 1.

**Candidate B (asymptotic recovery corollary).**
```
theorem kth_partitionFunction_recovery_of_isEquivalent ... :
    (fun t ↦ partitionFunction (fun x ↦ a₁ * kthPotential k₁ x) t)
      ~[atTop] (fun t ↦ partitionFunction (fun x ↦ a₂ * kthPotential k₂ x) t)
    → k₁ = k₂ ∧ a₁ = a₂
```
Transport both sides along EventuallyEq (t > 0 eventually, closed form
holds) via IsEquivalent.congr_left/congr_right, apply A, then the same
exponent/coefficient extraction as the exact-equality theorem (the ~30
line extraction block is duplicated; acceptable at second use, factor at
third).

This is the faithful form of the note's Section 7.4 claim: recovery from
asymptotic (expansion-level) data.

Claude's initial lean: A + B in one file (extend Laplace/OneD/Recovery.lean
rather than a new file, since they strengthen its two public theorems).

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_asymp_v1.md`. Summary:
route (b) (isEquivalent_iff_tendsto_one) confirmed as cleanest; names
confirmed (tendsto_rpow_atTop, tendsto_rpow_neg_atTop,
not_tendsto_nhds_of_tendsto_atTop, tendsto_nhds_unique,
IsEquivalent.congr_left/congr_right); IsEquivalent preferred over a raw
ratio hypothesis for downstream consumers; advice: factor the shared
algebraic tail of the two recovery theorems into a helper.

## Vote

- Claude: A + B extending Laplace/OneD/Recovery.lean.
- GPT-5.6 Sol: A + B same PR, A beside eventual_power_eq, B beside the
  exact recovery theorem, shared tail factored into a helper. Adopted.

## Numerical check

Not feasible beyond the tide-14 tautology (uniqueness statements);
underlying closed form already verified in the seabed.

## Result

- Branch tide/germbij-recovery-asymp, Laplace/OneD/Recovery.lean
  restructured: power_asymptote_unique (new),
  partitionFunction_kth_smul_rpow / kth_coeff_pos / kth_recovery_of_data
  (factored from the exact recovery theorem per the consult's advice),
  kth_partitionFunction_recovery (same statement, now 20 lines),
  kth_partitionFunction_recovery_of_isEquivalent (new).
- Three build iterations. Fixes: Pi.div_apply must be unfolded before
  field_simp under an IsEquivalent-derived ratio (the division is Pi.div,
  not a lambda — same class as the known Pi.add gotcha);
  tendsto_rpow_atTop / tendsto_rpow_neg_atTop are top-level, not in the
  Real namespace; tendsto_nhds_unique needs the constant-limit witness
  type-annotated; a trailing ring became dead after field_simp closed the
  goal.
- Surprise: none mathematical; the trichotomy proof came out exactly as
  deliberated.
