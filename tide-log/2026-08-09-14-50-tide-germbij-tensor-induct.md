# Tide: germbij tensor J7 (the jet induction)

**Direction (user):** standing auto-mode commission; the final
tensor-programme stage.
**Seabed:** laplace, branch tide/germbij-tensor-recover at baa87e9
(stacked on unmerged J6, PR #81).
**Started:** 2026-08-09T14:50 local

## Candidates

Consult J7, with the composition-honest hypothesis shape:

1. **`finite_jet_recovery`**: families of HigherLaplaceDomain
   packages at each 2 < k ≤ N (per the consult: "a structure
   parameterized by a natural N may be much easier than ContDiff ∞
   uniformly inside all rate proofs; prove finite-order recovery
   first"), the base matching at j < 3 as hypothesis (degree 0 is
   observationally undetermined — constants; degrees 1-2 follow for
   a COMMON H from the shared quadratic_peano/hessian_recovery, so
   hypothesizing them keeps the theorem honest without re-deriving),
   abstract symmetry at each degree, and the o(q^{k−2}) moment data
   at each degree: conclude ∀ j ≤ N, iteratedFDeriv j L₁ 0 =
   iteratedFDeriv j L₂ 0, by strong induction with J6 as the step.
2. **`smooth_jet_recovery_multi`**: the all-degrees wrapper
   (families at every k, data at every degree ⇒ every derivative
   tensor agrees), instantiating the finite theorem at N := j.

## Numerical check

Pure induction over verified components; structural.

## Vote

- Claude: as staged. - GPT-5.6 Sol: same (archived consult J7,
  including the finite-first ruling). Agreed.

## Result

Committed on tide/germbij-tensor-induct: `Laplace/Multi/JetInduction.lean`
(~90 lines), theorems `finite_jet_recovery` and
`smooth_jet_recovery_multi`. Compiled on the first build with only
unused-binder warnings (fixed); zero sorries. The tensor programme
J0-J7 is closed: from H-recovery (degree 2) through single-degree
tensor recovery (J6) to the full jet, moment data at rate o(q^(k-2))
per degree identifies every derivative tensor of the loss at the
origin (degrees >= 3 unconditionally given the packages; degrees < 3
enter as the base hypothesis, with degree 0 observationally
undetermined and degrees 1-2 recoverable for a common H from
quadratic_peano / hessian_recovery).

Surprise: none — the induction was pure plumbing over J6, the rare
tide where the first draft compiled. The only design decision was
packaging the per-degree domain packages as a Pi-type family
`∀ k, 2 < k → k ≤ N → HigherLaplaceDomain k L H` rather than a single
order-N package with weakening (deriving the order-k Taylor remainder
bound from the order-N one is real work; the family shape is honest
and free).
